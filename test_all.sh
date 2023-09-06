#! /bin/bash

set -e

if [ $# -ne 1 ]; then
  exit 1
fi

cargo fmt --check
cargo clippy -- -D warnings
cargo build --release

for dir in $1/*; do
  if [ -d $dir ]; then
    echo $dir
    ./test.sh $dir ~/tmp
  fi
done
