# Copyright (c) Christopher Di Bella.
# SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
#

# Provides build settings common for all targets.
function(add_impl)
	set(optional_values "")
	set(single_value_args TARGET)
	set(multi_value_args INCLUDE LINK COMPILER_OPTIONS COMPILER_DEFINITIONS)

	cmake_parse_arguments(add_target_args
	                      "${optional_values}"
	                      "${single_value_args}"
	                      "${multi_value_args}"
	                      ${ARGN})

	target_include_directories("${add_target_args_TARGET}"
	                           PUBLIC
	                           "${PROJECT_SOURCE_DIR}/include")
	target_include_directories("${add_target_args_TARGET}"
	                           PRIVATE
	                           "${add_target_args_INCLUDE}")
	target_compile_options("${add_target_args_TARGET}"
	                       PRIVATE
	                       "${add_target_args_COMPILER_OPTIONS}")
	target_compile_definitions("${add_target_args_TARGET}"
	                           PRIVATE
	                           "${add_target_args_COMPILER_DEFINITIONS}")
	target_link_libraries("${add_target_args_TARGET}"
	                      PRIVATE
	                      "${add_target_args_LINK}")
endfunction()

macro(PROJECT_TEMPLATE_EXTRACT_ADD_TARGET_ARGS)
	set(optional_values "")
	set(single_value_args TARGET FILENAME LIBRARY_TYPE)
	set(multi_value_args INCLUDE LINK COMPILER_OPTIONS COMPILER_DEFINITIONS)

	cmake_parse_arguments(add_target_args
	                      "${optional_values}"
	                      "${single_value_args}"
	                      "${multi_value_args}"
	                      ${ARGN})

	if("${add_target_args_TARGET}" STREQUAL "")
		message(FATAL_ERROR "TARGET is not set. Cannot build a target without naming it!")
	endif()

	if("${add_target_args_FILENAME}" STREQUAL "")
		message(FATAL_ERROR "FILENAME is not set. Cannot build target ${add_target_args_TARGET} without a filename.")
	endif()
endmacro()

macro(PROJECT_TEMPLATE_CALL_ADD_IMPL)
	add_impl(TARGET "${add_target_args_TARGET}"
	         INCLUDE "${add_target_args_INCLUDE}"
	         LINK "${add_target_args_LINK}"
	         COMPILER_OPTIONS "${add_target_args_COMPILER_OPTIONS}"
	         COMPILER_DEFINITIONS "${add_target_args_COMPILER_DEFINITIONS}")
endmacro()
