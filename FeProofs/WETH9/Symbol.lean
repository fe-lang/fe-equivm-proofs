import FeProofs.WETH9.StringGetter

/-!
# FeWETH9 `symbol()`

Dispatcher arm entry: pc 571; reach lemma `feWETH9ReachSymbolBody`.  The arm checks the call
value, then calls `SolString::load` (pc 800) on slot 1 with return address 586, which jumps to the
return encoder; `stringGetter` (`StringGetter.lean`) does the rest.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace FeProofs.WETH9

set_option maxRecDepth 2000000

/-- `symbol()`: the theorem `Correct.lean` routes selector 7 to, under `feWETH9StorageWF`. -/
theorem feWETH9SymbolBody {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = feWETH9Bytecode) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (feWETH9SelBytes 7)) (hwf : feWETH9StorageWF σ I) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (feWETH9SelBytes 7) rfl hsel
  have hd := feWETH9Dispatch_symbol hsel
  obtain ⟨k, C, rd⟩ := feWETH9ReachSymbolBody (g := Sat256.ofUInt256 g) (σ := σ)
    (σ₀ := σ₀) (A := A) hcode hsz hsize hsel
  by_cases hwv : I.weiValue = ⟨0⟩
  swap
  · rd_run rd using [hwv]
    exact RDrev.reEquivDispatchedRevertSel hcode rd hd
      fun _ => bodyReverts_nonPayable (by simp only [initState]; exact hwv)
  rd_run rd to 800 using [hwv]
  exact stringGetter (field := "symbol") hcode hsize hd
    (show decodeCalldata [] [] I.calldata = some ∅ from decodeCalldata_empty_ok hsz)
    rfl rfl rfl rfl hwv (hwf.2 hsel hwv) (by jump_dest) (by simp) rd
    fun _ _ _ _ _ rd => by rd_step rd; exact ⟨_, _, _, rd⟩

end FeProofs.WETH9
