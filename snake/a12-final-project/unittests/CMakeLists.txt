cmake_minimum_required(VERSION 3.20)
project(snake_test)

include(FetchContent)

set(CMAKE_CXX_STANDARD 20)
set(CMAKE_CXX_STANDARD_REQUIRED ON)
set(CMAKE_C_STANDARD 99)
set(CMAKE_C_STANDARD_REQUIRED ON)

if (CMAKE_CXX_COMPILER_ID MATCHES "(GNU|Clang)")
    add_compile_options(
            -Wall
            -Wextra
            -Wpedantic
            -Wconversion
            -march=native
            $<$<CONFIG:DEBUG>:-fsanitize=address>
            $<$<CONFIG:DEBUG>:-g3>
            $<$<CONFIG:RELEASE>:-g0>
    )
    add_link_options(
            -rdynamic
            $<$<CONFIG:DEBUG>:-fsanitize=address>
    )
elseif (CMAKE_CXX_COMPILER_ID MATCHES "MSVC")
    add_compile_options(
            /W4
    )
else ()
    message(FATAL_ERROR "Unknown compiler '${CMAKE_CXX_COMPILER_ID}'")
endif ()

add_library(
    snake
    ../runtime/ss_bin_tree.c
    ../runtime/string_span.c
    ../runtime/ss_bin_tree.h
    ../runtime/string_span.h
)
target_include_directories(snake PUBLIC ../runtime/)

enable_testing()

FetchContent_Declare(googletest
        GIT_REPOSITORY https://github.com/google/googletest.git
        GIT_TAG release-1.12.1)
set(gtest_force_shared_crt ON CACHE BOOL "" FORCE)
FetchContent_MakeAvailable(googletest)

add_executable(
        unittests
        ss_bin_tree_test.cpp
        string_span_test.cpp
        test_util.hpp
)
target_link_libraries(
        unittests
        gtest_main
        snake
)

include(GoogleTest)
gtest_discover_tests(unittests)


