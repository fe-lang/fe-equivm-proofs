#!/usr/bin/env python3
"""Rewrite proof_skeleton.py dispatcher reach lemmas to use `rd_run`.

usage: convert_dispatch.py <Dispatch.lean>...
"""
import re, sys

reach = re.compile(
    r"(  have hword : solcSelectorWord I = ⟨(\d+)⟩ :=\n(?:    .*\n)+?)"
    r"  have rd0 := RD\.initState \(g := g\) \(σ := σ\) \(σ₀ := σ₀\) \(A := A\) hcode\n"
    r"(?:  have rd\d+ := .*\n)+"
    r"  exact ⟨_, _, by simpa \[[^\]]*\] using rd\d+⟩\n")
short = re.compile(
    r"  have rd0 := RD\.initState \(g := g\) \(σ := σ\) \(σ₀ := σ₀\) \(A := A\) hcode\n"
    r"  have rd1 := \w+\.\w+_block_0_taken \(by simp\) \(lt_four_ne_zero_of_lt hshort\) \(by jump_dest\) rd0\n"
    r"  have rd2 := \w+\.\w+ \(by simp\) rd1\n"
    r"  exact rd2\n")
for path in sys.argv[1:]:
    s = open(path).read()
    def arm(m):
        # the arm entry pc is in the statement just above
        pc = re.findall(r"\(UInt256\.ofNat (\d+)\)\n      \[\(UInt256\.shiftRight", s[:m.start()])[-1]
        return (m.group(1) +
            "  have rd0 := RD.initState (g := g) (σ := σ) (σ₀ := σ₀) (A := A) hcode\n"
            f"  rd_run rd0 to {pc} using [lt_four_eq_zero_of_ge hsz hsize,\n"
            "    (show UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes (⟨0⟩ : UInt256).toNat 32))\n"
            f"      (UInt256.ofNat 224) = ⟨{m.group(2)}⟩ from hword)]\n"
            "  exact ⟨_, _, rd0⟩\n")
    t, n1 = reach.subn(arm, s)
    t, n2 = short.subn(
        "  have rd0 := RD.initState (g := g) (σ := σ) (σ₀ := σ₀) (A := A) hcode\n"
        "  rd_run rd0 using [lt_four_ne_zero_of_lt hshort]\n  exact rd0\n", t)
    open(path, 'w').write(t)
    print(f'{path}: {n1} reach, {n2} short')
