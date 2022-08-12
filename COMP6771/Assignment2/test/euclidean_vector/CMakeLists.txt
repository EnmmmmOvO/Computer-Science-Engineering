cxx_test(
    TARGET euclidean_vector_test1
    FILENAME "euclidean_vector_test1.cpp"
    LINK euclidean_vector
)

cxx_test(
   TARGET euclidean_vector_constructor_test
   FILENAME "euclidean_vector_constructor_test.cpp"
   LINK euclidean_vector
)

cxx_test(
        TARGET euclidean_vector_operations_test
        FILENAME "euclidean_vector_operations_test.cpp"
        LINK euclidean_vector
)

cxx_test(
        TARGET euclidean_vector_member_functions_test
        FILENAME "euclidean_vector_member_functions_test.cpp"
        LINK euclidean_vector
)

cxx_test(
        TARGET euclidean_vector_friends_test
        FILENAME "euclidean_vector_friends_test.cpp"
        LINK euclidean_vector
)

cxx_test(
        TARGET euclidean_vector_utility_functions_test
        FILENAME "euclidean_vector_utility_functions_test.cpp"
        LINK euclidean_vector
)