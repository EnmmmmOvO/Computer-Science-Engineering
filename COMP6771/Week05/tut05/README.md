# Tutorial 5

## Question 1

Why is prefix increment/decrement usually preferred to postfix increment/decrement? When would we use postfix?

## Question 2

What is *stack unwinding*?

What happens during stuck unwinding?

What issue can this potentially cause? How can we fix this?

## Question 3

What are the 4 exception safety levels and what does each mean?

## Question 4

Look at `source/rethrow.cpp`

This program currently catches the exception fine within the make_connection function. However, we want the client (the main function) to also log it's own error message "Could not establish connection". How can we use rethrow to achieve this?

## Question 5

In what cases would we want to have two catch statements for a thrown exception?

## Question 6

In what case would we want to define our own exception? Give an example, and explain why we would.

Are there ways to define our own exception without reinvesting the wheel?

## Question 7

Look at `source/catch.cpp`

What is wrong with this code?
