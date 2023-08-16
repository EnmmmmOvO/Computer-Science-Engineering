#!/usr/bin/python3

def a():
	x = 1
	print('a', x, y, z)

def b():
	x = 2
	y = 2
	a()
	print('b', x, y, z)

def c():
	x = 3
	y = 3
	global z
	z = 3
	b()
	print('c', x, y, z)
