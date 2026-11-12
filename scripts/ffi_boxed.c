// The symbols Lean's interpreter calls for EVMLean's two `@[extern]` functions,
// `ffi.sha256` and `ffi.BLAKE2Compress` (`Ethereum/FFI/ffi.lean`).  Each takes its arguments
// boxed and hands them to the C function, as the wrapper Lean compiles for the declaration
// does (`lake build Ethereum.FFI.ffi:c` prints them).  `scripts/build_ffi.sh` builds these with
// EVMLean's `ffi.c` into a library that `lean --load-dynlib` loads, so that `#eval` can run
// the SHA-256 and BLAKE2 precompiles.
#include <lean/lean.h>

lean_object* sha256(lean_object*, size_t);
lean_object* blake2compressb64(lean_object*);

LEAN_EXPORT lean_object* lp_evmlean_ffi_sha256___boxed(lean_object* input, lean_object* len) {
  size_t n = lean_unbox_usize(len);
  lean_dec(len);
  lean_object* hash = sha256(input, n);
  lean_dec_ref(input);
  return hash;
}

LEAN_EXPORT lean_object* lp_evmlean_ffi_BLAKE2Compress___boxed(lean_object* input) {
  lean_object* out = blake2compressb64(input);
  lean_dec_ref(input);
  return out;
}
