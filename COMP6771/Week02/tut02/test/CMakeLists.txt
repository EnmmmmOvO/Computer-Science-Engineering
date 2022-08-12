cxx_library(
   TARGET test_main
   FILENAME test_main.cpp
)
target_include_directories(test_main PUBLIC .)

cxx_test(
   TARGET sort_descending_test
   FILENAME "sort_descending_test.cpp"
   LINK sort_descending
)

cxx_test(
   TARGET is_permutation_test
   FILENAME "is_permutation_test.cpp"
   LINK is_permutation
)
