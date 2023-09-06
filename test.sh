#! /bin/bash

set -e

if [ $# -ne 2 ]; then
  exit 1
fi

from=$1
to=$2

rm -rf $to
cp -r $from $to

cargo run --release -- $to/c2rust-lib.rs

# nightly=`cat $to/rust-toolchain`
# RUSTFLAGS=-Awarnings cargo +$nightly build --manifest-path $to/Cargo.toml

# rm -rf $from/target
# rm -rf $to/target
# diff -r $from $to | less
