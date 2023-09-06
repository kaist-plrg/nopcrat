#! /bin/bash

set -e

from=$1
to=$2

if [ "$from" = "" ]; then
  exit 1
fi

if [ "$to" = "" ]; then
  exit 1
fi

if [ ! -d "$from" ]; then
  exit 1
fi

rm -rf $to
cp -r $from $to

cargo run --release -- $to/c2rust-lib.rs

nightly=`cat $to/rust-toolchain`
RUSTFLAGS=-Awarnings cargo +$nightly build --manifest-path $to/Cargo.toml

rm -rf $from/target
rm -rf $to/target
diff -r $from $to | less
