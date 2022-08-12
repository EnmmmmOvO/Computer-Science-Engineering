cxx_library(
	TARGET test_main
	FILENAME test_main.cpp
)
target_include_directories(test_main PUBLIC .)

add_subdirectory(q1)
add_subdirectory(q2)
