# Copyright (c) Christopher Di Bella.
# SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
#
cmake_minimum_required(VERSION 3.13)

project("COMP6771_EUCLIDEAN_VECTOR" CXX)
add_library(${PROJECT_NAME} INTERFACE)

set(CMAKE_CXX_STANDARD 20)
set(CMAKE_CXX_EXTENSIONS Off)
set(CMAKE_CXX_STANDARD_REQUIRED On)
set(CMAKE_EXPORT_COMPILE_COMMANDS On)

list(APPEND CMAKE_MODULE_PATH "${CMAKE_CURRENT_SOURCE_DIR}/config/cmake")

# Project configuration
enable_testing()
include(CTest)

# clang-tidy options
#option(${PROJECT_NAME}_ENABLE_CLANG_TIDY "Builds with clang-tidy, if available. Defaults to On." On)

#if(${PROJECT_NAME}_ENABLE_CLANG_TIDY)
#	find_package(ClangTidy REQUIRED)
#endif()

include(add-targets)

include_directories(include)

add_subdirectory(source)
add_subdirectory(test)
