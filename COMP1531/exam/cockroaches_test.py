'''
cockroaches test
'''
from cockroaches import decontaminate


def generate_files(cockroaches):
    '''
    Input Parameters:

    - cockroaches        a dictionary of the form

    {
        'monday.txt': ['kitchen', 'attic', 'bathroom']
        'tuesday.txt': ['kitchen', 'bedroom', 'backyaard'], etc
    }
    '''
    for filename in cockroaches:
        with open(filename, 'w') as file_:
            for room in cockroaches[filename]:
                file_.write(room + '\n')


def test_sample():
    '''
    test sample
    '''
    files = ['monday.txt', 'friday.txt']  # E.G. Files are "monday.txt" and "friday.txt"
    # Create the test files and populate with data
    mapping = {"monday.txt": ["kitchen", "backyard"], "friday.txt": ["kitchen"]}
    generate_files(mapping)
    assert (decontaminate(files) == {'backyard': 1, 'kitchen': 2})
