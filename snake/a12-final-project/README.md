## Useful Commands

Zip up the submission:
```shell
zip -r input.zip input
zip -r submission.zip . -x "input/*"
```

Eval for OCaml enviromnment:
```shell
eval $(opam env --switch=4.13.1)
```

Full clean, rebuild, and test
```shell
make clean && dune build && make test && ./test
```

## Building the C Tests


### Set up CMake
```shell
cd unittests
cmake -B build -S . -DCMAKE_BUILD_TYPE=Debug
```

### Build tests
```shell
cd unittests/
cmake --build build
```

### Run tests
```shell
cd unittests/build/
# run gtest directly
./unittests
# run gtest on single test
./unittests --gtest_filter=<test_suite>.<test_name>
# run cmake tester thing
ctest
```
