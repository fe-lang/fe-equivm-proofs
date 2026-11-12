#!/bin/sh
# Builds .lake/ffi/libfeffi, a shared library with the C code behind EVMLean's `@[extern]`
# functions (SHA-256 and BLAKE2 compression), and prints its path.  `lean --load-dynlib` on it
# lets `#eval` run those precompiles; without it the interpreter stops with "Could not find
# native implementation of external declaration 'ffi.sha256'".
#
# The hash sources are the two repositories EVMLean's lakefile clones.  Run from the project
# root.  Exits 1, printing no path, if there is no C compiler or a clone fails.
set -eu
out=.lake/ffi
case "$(uname)" in
  Darwin) lib=$out/libfeffi.dylib; flags="-undefined dynamic_lookup" ;;
  *) lib=$out/libfeffi.so; flags="" ;;
esac
command -v cc > /dev/null || exit 1
mkdir -p $out
[ -d $out/sha2 ] || git clone -q --depth 1 https://github.com/amosnier/sha-2.git $out/sha2
[ -d $out/keccak256 ] || git clone -q --depth 1 https://github.com/brainhub/SHA3IUF.git $out/keccak256
evmlean=.lake/packages/evmlean/Ethereum/FFI/ffi.c
if [ ! -f $lib ] || [ $evmlean -nt $lib ] || [ scripts/ffi_boxed.c -nt $lib ]; then
  cc -shared -fPIC -O2 $flags -I "$(lake env lean --print-prefix)/include" -I $out/sha2 \
    -I $out/keccak256 -o $lib scripts/ffi_boxed.c $evmlean $out/sha2/sha-256.c \
    $out/keccak256/sha3.c
fi
echo $lib
