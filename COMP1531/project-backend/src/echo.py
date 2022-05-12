from src.error import InputError

def echo(value):
    if value == 'echo':
        raise InputError('Input cannot be echo')
    return value
