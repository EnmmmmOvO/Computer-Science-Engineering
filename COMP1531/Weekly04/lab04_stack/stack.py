"""
stack.py
"""

class Stack:
	"""
	Implementation
	"""
	def __init__(self):
		"""
		list
		"""
		self.items = []
	
	
	def push(self, data):
		"""
		insert into stack
		"""
		self.items.append(data)
	
	
	def pop(self):
		"""
		remove data from stack
		"""
		return self.items.pop()
	
	
	def display(self):
		"""
		display items from stack
		"""
		for item in self.items:
			print(item,end = " ")