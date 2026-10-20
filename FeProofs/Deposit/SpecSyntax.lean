import Stele.Notation

/-!
# FeDeposit surface spec

The Fe reimplementation of the Ethereum 2.0 deposit contract
(`crates/fe/tests/fixtures/fe_test/deposit_contract.fe` in the Fe repository).

Storage follows the Fe `DepositStore` struct at slot 0: `branch` in slots 0..31,
`deposit_count` in slot 32, `zero_hashes` in slots 33..64.

Every SHA-256 is a `STATICCALL` to precompile 2 over a 64-byte buffer; the bytecode reverts if the
call fails or returns fewer than 32 bytes and otherwise uses the first returned word
(`sha256_64`).  The calls appear in the bytecode's order, since each one is an opaque `Θ` call.

`u64_chunk` is SSZ's `uint64` chunk: the little-endian bytes of the value in the top eight bytes
of a word, computed with the same three byte-swap passes as Fe's `ssz::u64_chunk`; `le64` is its
eight-byte `bytes` form (`ssz::serialize_u64`).

The incremented deposit count is kept as `size` rather than read back after the write, as the
bytecode does: it stores the incremented count and continues from the value on its stack.

Fe rejects call value on every entry point except `deposit`, including the constructor.
Transitions are listed in the dispatcher's compare order.
-/

open Stele Stele.Notation

namespace FeProofs.Deposit.Syntax

def contractSyntax : ContractDecl := solidity% contract FeDeposit {
  uint256[32] branch;
  uint256 deposit_count;
  uint256[32] zero_hashes;

  event DepositEvent(bytes pubkey, bytes withdrawal_credentials, bytes amount, bytes signature,
    bytes index);

  constructor() {
    for (uint256 height = 0; height < 31; height++) {
      uint256 cur = zero_hashes[height];
      uint256 next = sha256_pair(cur, cur);
      zero_hashes[height + 1] = next;
    }
  }

  function supportsInterface(bytes4 interface_id) external returns (bool) {
    return interface_id == bytes4(0x01ffc9a7) || interface_id == bytes4(0x85640907);
  }

  function deposit(bytes calldata pubkey, bytes calldata withdrawal_credentials,
      bytes calldata signature, bytes32 deposit_data_root) external payable {
    require(pubkey.length == 48);
    require(withdrawal_credentials.length == 32);
    require(signature.length == 96);
    require(msg.value >= 1000000000000000000);
    require(msg.value % 1000000000 == 0);
    uint256 deposit_amount = msg.value / 1000000000;
    require(deposit_amount <= 18446744073709551615);
    uint64 amount = uint64(deposit_amount);
    uint256 pubkey_root = sha256_64(abi.encodePacked(bytes(pubkey), bytes16(bytes16(0))));
    uint256 signature_left = sha256_64(signature[0:64]);
    uint256 signature_right = sha256_64(abi.encodePacked(bytes(signature[64:96]),
      bytes32(bytes32(0))));
    uint256 signature_root = sha256_pair(signature_left, signature_right);
    uint256 credentials = abi.decode(withdrawal_credentials, (uint256));
    uint256 amount_chunk = u64_chunk(amount);
    uint256 left = sha256_pair(pubkey_root, credentials);
    uint256 right = sha256_pair(amount_chunk, signature_root);
    uint256 node = sha256_pair(left, right);
    require(node == uint256(deposit_data_root));
    bytes memory amount_bytes = le64(amount);
    bytes memory index_bytes = le64(uint64(deposit_count));
    emit DepositEvent(pubkey, withdrawal_credentials, amount_bytes, signature, index_bytes);
    require(deposit_count < 4294967295);
    uint256 size = deposit_count + 1;
    deposit_count = size;
    for (uint256 height = 0; height < 32; height++) {
      if ((size &[uint256] 1) == 1) {
        branch[height] = node;
        return;
      }
      uint256 sibling = branch[height];
      uint256 parent = sha256_pair(sibling, node);
      node = parent;
      size = size / 2;
    }
    require(false);
  }

  function get_deposit_count() external returns (bytes) {
    bytes memory count = le64(uint64(deposit_count));
    return count;
  }

  function get_deposit_root() external returns (uint256) {
    uint256 count = deposit_count;
    uint256 node = 0;
    uint256 size = count;
    for (uint256 height = 0; height < 32; height++) {
      if ((size &[uint256] 1) == 1) {
        uint256 sibling = branch[height];
        uint256 parent = sha256_pair(sibling, node);
        node = parent;
      } else {
        uint256 zero = zero_hashes[height];
        uint256 parent = sha256_pair(node, zero);
        node = parent;
      }
      size = size / 2;
    }
    uint256 length_chunk = u64_chunk(uint64(count));
    uint256 root = sha256_pair(node, length_chunk);
    return root;
  }

  function sha256_64(bytes payload) internal returns (uint256) {
    address precompile = address(2);
    (bool ok, bytes result) = precompile.staticcall(payload);
    require(ok);
    require(result.length >= 32);
    return abi.decode(result[0:32], (uint256));
  }

  function sha256_pair(uint256 left, uint256 right) internal returns (uint256) {
    uint256 digest = sha256_64(abi.encodePacked(uint256(left), uint256(right)));
    return digest;
  }

  function u64_chunk(uint64 value) internal returns (uint256) {
    uint256 v = uint256(value);
    v = ((v &[uint256] 71777214294589695) <<[uint256] 8)
      |[uint256] ((v >>[uint256] 8) &[uint256] 71777214294589695);
    v = ((v &[uint256] 281470681808895) <<[uint256] 16)
      |[uint256] ((v >>[uint256] 16) &[uint256] 281470681808895);
    return ((v <<[uint256] 32) |[uint256] (v >>[uint256] 32)) <<[uint256] 192;
  }

  function le64(uint64 value) internal returns (bytes) {
    uint256 chunk = u64_chunk(value);
    return abi.encodePacked(uint64(uint64(chunk >>[uint256] 192)));
  }
}

end FeProofs.Deposit.Syntax
