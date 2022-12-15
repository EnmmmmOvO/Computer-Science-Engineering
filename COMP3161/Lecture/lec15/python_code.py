class Private:
    def __private(self):
        print("gtfo you're not supposed to call this!")
# Here's how we can access this "private" method, whose name is actually obfuscated:

# >>> priv = Private()
# >>> priv.__private()
# Traceback (most recent call last):
#   File "<stdin>", line 1, in <module>
# AttributeError: 'Private' object has no attribute '__private'
# >>> dir(priv)
# ['_Private__private', '__class__', '__delattr__', '__dict__', '__dir__', '__doc__', '__eq__', '__format__', '__ge__', '__getattribute__', '__gt__', '__hash__', '__init__', '__init_subclass__', '__le__', '__lt__', '__module__', '__ne__', '__new__', '__reduce__', '__reduce_ex__', '__repr__', '__setattr__', '__sizeof__', '__str__', '__subclasshook__', '__weakref__']
# >>> priv._Private__private()
# gtfo you're not supposed to call this!

# (This language feature was never written with abstraction in mind so this is not unexpected).