cxx_library(
   TARGET test_main
   FILENAME test_main.cpp
)

cxx_test(
   TARGET hello
   FILENAME "hello.cpp"
)

cxx_test(
   TARGET sort3_test
   FILENAME "sort3_test.cpp"
   LINK sort3
)
