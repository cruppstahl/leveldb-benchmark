benchmarks for hamsterdb and leveldb

based on leveldb 1.15.0

To build:
- download/unpack leveldb 1.15.0
- replace the Makefile
- replace db/db_bench.cc
- copy db_hamster.cc to doc/bench/
- run `make db_bench` and `make db_hamster`
