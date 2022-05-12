
def neighbours(iterable):
    '''
    A generator, that, given an iterable, yields the "neighbourhood" of each
    element. The neighbourhood is a tuple containing the element itself as well
    as the one that comes before and the one that comes after. For example,
    >>> list(neighbours([1,2,3,4]))
    [(1,2), (1,2,3), (2,3,4), (3,4)]

    Note that the first and last elements are pairs, while the rest are triples.

    Params:
      iterable (iterable): The iterable being processed. In the event it's empty,
      this generator should not yield anything. In the event it only contains
      one element, only that element should be yielded in a one-tuple.

    Yields:
      (tuple) : The neighbourhood of the current element.
    '''
    # Hint: Don't forget that iterables can produce values infinitely. You can't
    # rely on being able to retrieve all the elements at once.
    neighbour = list(iterable)
    length = len(neighbour)
    result = []

    if length == 0:
        return neighbour
    elif length == 1:
        result.append((neighbour[0],))
        return result
    else:
        tuplefirst = (neighbour[0], neighbour[1])
        result.append(tuplefirst)

        number = 0
        while (number < length - 2):
            tap = (neighbour[number], neighbour[number + 1], neighbour[number + 2])
            result.append(tap)
            number += 1

        tupleend = (neighbour[-2],neighbour[-1])
        result.append(tupleend)
        return result


if __name__ == '__main__':
    print(neighbours("hey"))

      