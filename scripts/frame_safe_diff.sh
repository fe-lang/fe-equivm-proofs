#!/bin/sh
# Tests `FrameSafe` (`Fe/Sonatina/FrameSafe.lean`) where it is not proved: runs the machine IR
# with its spills beside the machine IR (`Fe/Sonatina/SpillDiff.lean`) on the inputs of the
# precompile generators `scripts/<P>Diff.lean`, and on the Fe tests and generated calls of
# corpus drivers, and prints a line per run that panics with `spillClobbered` (CLOBBER) or
# otherwise ends differently (DIFFER), and a total per section (FRAMESAFE).  A precompile's
# generator is reused as it is: its last line, the `#eval` of its `main`, is replaced by a
# driver.  In a corpus driver the targets are the paired model (`Sidecar.pairedModel`), so a
# disagreement of the two models is a DISAGREE line whose model reverts with the bytes of
# `SPILL CLOBBER` (5350494c4c20434c4f42424552) or `SPILL DIFFER ...` (5350494c4c20444946464552).
#
# Usage: scripts/frame_safe_diff.sh <precompile sidecar dir> [corpus driver.lean ...]
#   FRAMESAFE_GENERATED=<n> caps the generated inputs per precompile (default: the generator's).
#   FRAMESAFE_ONLY="<name> ..." runs only those precompiles (all by default).
# The sections run one after another; the IR runs in Lean's interpreter, slowly (Blake2F's
# rounds take seconds each).  Output goes to .lake/frame-safe/<time>/, one file per section;
# <name>.log has a line per run as it ends.
set -eu
cd "$(dirname "$0")/.."
sidecars=$1
shift
out=.lake/frame-safe/$(date +%Y%m%d-%H%M%S)
mkdir -p $out

# precompile <name> <namespace> <generated> <vectors> [<call data prefix> [<generator>]]
precompile() {
  case " ${FRAMESAFE_ONLY:-$1} " in *" $1 "*) ;; *) return 0 ;; esac
  name=$1 ns=$2 count=${FRAMESAFE_GENERATED:-$3} vectors=$4 prefix=${5:-.empty} gen=${6:-$1}
  file=$out/${name}FrameSafe.lean
  { echo "import Fe.Sonatina.SpillDiff"
    grep -v "^#eval " scripts/${gen}Diff.lean
    cat <<EOF

def frameSafeInputs : List (String × ByteArray) := Id.run do
  let mut ins := $vectors
  let mut gen := mkStdGen 1
  for _ in [:$count] do
    let ((kind, d), next) := $ns.input.run gen
    gen := next
    ins := ins ++ [(kind, d)]
  return ins

#eval Fe.Sonatina.frameSafeCalldata "$name" "$sidecars/$name.sidecar.json" frameSafeInputs
  ($prefix)
EOF
  } > $file
  FRAMESAFE_LOG=$out/$name.log lake lean $file > $out/$name.txt 2>&1 || true
  grep "^FRAMESAFE\|^CLOBBER\|^DIFFER\|error" $out/$name.txt | head -20
}

geth='(GEN.geth.map fun (n, i, _) => (s!"geth {n}", Fe.EVM.Diff.hex i))'
ecvec='(EcrecoverPrecompileDiff.geth.map (fun (n, i, _) => (s!"geth {n}", Fe.EVM.Diff.hex i)) ++
    EcrecoverPrecompileDiff.evmlean.map fun (n, i, _) => (s!"EVMLean {n}", i))'
precompile Blake2F Blake2FDiff 120 "$(echo "$geth" | sed s/GEN/Blake2FDiff/)"
precompile Bn254Add Bn254AddDiff 400 "$(echo "$geth" | sed s/GEN/Bn254AddDiff/)"
precompile Bn254Mul Bn254MulDiff 200 "$(echo "$geth" | sed s/GEN/Bn254MulDiff/)"
precompile EcrecoverPrecompile EcrecoverPrecompileDiff 150 "$ecvec"
# The contract `Ecrecover` takes the same words after the selector of `recover`.
precompile Ecrecover EcrecoverPrecompileDiff 150 "$ecvec" "⟨#[0x2a, 0xa6, 0xd3, 0x51]⟩" \
  EcrecoverPrecompile
precompile Ripemd160 Ripemd160Diff 200 \
  '(Ripemd160Diff.paper.map fun (m, _) => (s!"paper {repr m}", m.toUTF8))'

for driver in "$@"; do
  base=$(basename $driver .lean)
  file=$out/${base}FrameSafe.lean
  sed -e 's/^import Fe.Sonatina.Diff$/import Fe.Sonatina.SpillDiff/' \
    -e 's/Fe\.Sonatina\.targetsOf/Fe.Sonatina.spillTargetsOf/' $driver > $file
  lake lean $file > $out/$base.txt 2>&1 || true
  spill=$(grep -c "^DISAGREE.*5350494c4c20" $out/$base.txt || true)
  echo "FRAMESAFE $base spill-disagreements=$spill"
  grep "^DIFF \|^GENERATED\|^DISAGREE.*5350494c4c20" $out/$base.txt | head -20
done
echo "output in $out"
