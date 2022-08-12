# Copyright (c) Christopher Di Bella.
# SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
#
include(add-targets-impl)

# Builds an executable.
# Parameters include:
#     TARGET target_name                  Name of the object being built.
#     FILENAME /path/to/file              Path to the file that is being built.
#     INCLUDE cmake_package+              List of imported CMake packages the target requires.
#     COMPILER_OPTIONS options+           List of options to be passed to the compiler.
#     COMPILER_DEFINITIONS definitions+   List of macro definitions to be passed to the compiler.
function(cxx_executable)
   PROJECT_TEMPLATE_EXTRACT_ADD_TARGET_ARGS(${ARGN})

   add_executable("${add_target_args_TARGET}" "${add_target_args_FILENAME}")
   PROJECT_TEMPLATE_CALL_ADD_IMPL()
endfunction()

# Builds a library.
# Accepts the same parameters as `cxx_executable`, as well as:
#     LIBRARY_TYPE (STATIC|SHARED|MODULE|OBJECT)         Specifies how the library is to be built.
function(cxx_library)
   PROJECT_TEMPLATE_EXTRACT_ADD_TARGET_ARGS(${ARGN})

   set(legal_library_types "" STATIC SHARED MODULE OBJECT)
   list(FIND legal_library_types "${add_target_args_LIBRARY_TYPE}" library_type_result)
   if(library_type_result EQUAL -1)
      message(FATAL_ERROR "Cannot add a library of type \"${add_target_args_LIBRARY_TYPE}\"")
   endif()

   add_library("${add_target_args_TARGET}" ${add_target_args_LIBRARY_TYPE} "${add_target_args_FILENAME}")
   PROJECT_TEMPLATE_CALL_ADD_IMPL()
endfunction()

# Builds a test executable and creates a test target (for CTest).
# Accepts the same parameters as `cxx_executable`
# Depends on Catch2 being imported, and the existence of a target called test_main.
function(cxx_test)
   cxx_executable(${ARGN})

   PROJECT_TEMPLATE_EXTRACT_ADD_TARGET_ARGS(${ARGN})
   target_link_libraries("${add_target_args_TARGET}" PRIVATE test_main)
   add_test("test.${add_target_args_TARGET}" "${add_target_args_TARGET}")
endfunction()

# Builds an executable that can be run as a more reliable benchmark.
# Accepts the same parameters as `cxx_executable`.
# Depends on Google Benchmark being imported.
function(cxx_benchmark)
   cxx_executable(${ARGN})

   PROJECT_TEMPLATE_EXTRACT_ADD_TARGET_ARGS(${ARGN})
   target_compile_options("${add_target_args_TARGET}" PRIVATE -fno-inline)
   target_link_libraries("${add_target_args_TARGET}" PRIVATE benchmark::benchmark benchmark::benchmark_main)
endfunction()
