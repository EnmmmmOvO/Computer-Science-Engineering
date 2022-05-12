"""
calculate c and a 
"""
import math

class Circle:
	"""
	initialization
	"""
	def __init__(self, r):
		if r > 0 :
			self.r = r
		else :
			self.r = 0
			"""
			ensure r is greater than 0
			"""

	def circumference(self):
		"""
		circumference = 2 * pi * r
		"""
		return 2 * math.pi * self.r
		
  

	def area(self) :
		"""
		air =  pi * r * r
		"""
		return math.pi * self.r * self.r

