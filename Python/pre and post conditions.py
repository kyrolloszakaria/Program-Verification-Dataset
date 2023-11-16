def checkConditions(func):
	def wrapped(*args, **kwargs):
		if not (precondition_bool_expression):
			raise Exception(reason)
		else:
			result = func(*args, **kwargs)
			
			if not (postcondition_bool_expression):
				raise Exception(reason)
			else:
				return result
				
	return wrapped

# If you know what args and kwargs are going to be passed to func and have them
# explicitly laid out in the declaration of wrapped, yet you still want to use
# the decorator on a method inside of a class:

def checkConditions(func):
	def wrapped(self, arg1, arg2, arg3, etc):
		if not (precondition_bool_expression):
			raise Exception(reason)
		else:
			result = func(self, arg1, arg2, arg3, etc)
			
			if not (postcondition_bool_expression):
				raise Exception(reason)
			else:
				return result
				
	return wrapped
