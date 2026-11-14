#!/bin/sh
# Builds .lake/ffi/libfeffi, a shared library with the C code behind EVMLean's `@[extern]`
# functions (SHA-256 and BLAKE2 compression), and prints its path.  `lean --load-dynlib` on it
# lets `#eval` run those precompiles; without it the interpreter stops with "Could not find
# native implementation of external declaration 'ffi.sha256'".
#
# The hash sources are the two repositories EVMLean's lakefile clones, at pinned commits.  Run
# from the project root.  Exits 1, printing no path, if there is no C compiler or a clone fails.
set -eu
out=.lake/ffi
case "$(uname)" in
  Darwin) lib=$out/libfeffi.dylib; flags="-undefined dynamic_lookup" ;;
  *) lib=$out/libfeffi.so; flags="" ;;
esac
command -v cc > /dev/null || exit 1
mkdir -p $out
clone() {
  [ -d "$out/$1" ] && return
  rm -rf "$out/$1.tmp"
  git clone -q "$2" "$out/$1.tmp"
  git -C "$out/$1.tmp" checkout -q --detach "$3"
  mv "$out/$1.tmp" "$out/$1"
}
clone sha2 https://github.com/amosnier/sha-2.git 565f65009bdd98267361b17d50cddd7c9beb3e6c
clone keccak256 https://github.com/brainhub/SHA3IUF.git fc8504750a5c2174a1874094dd05e6a0d8797753
evmlean=.lake/packages/evmlean/Ethereum/FFI/ffi.c
if [ ! -f $lib ] || [ $evmlean -nt $lib ] || [ scripts/ffi_boxed.c -nt $lib ]; then
  cc -shared -fPIC -O2 $flags -I "$(lake env lean --print-prefix)/include" -I $out/sha2 \
    -I $out/keccak256 -o $lib scripts/ffi_boxed.c $evmlean $out/sha2/sha-256.c \
    $out/keccak256/sha3.c
fi
echo $lib
