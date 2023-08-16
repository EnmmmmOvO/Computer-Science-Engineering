#!/usr/bin/env python3

import os
import queue
import re
import sys


class compiler_list(str):
    def __init__(self, file_location):
        # Get the base filename without extension
        self.file_name = os.path.basename(file_location).split('.')[0]

        # List to store the lines from the source file
        self.compiler_list = list()

        # Read lines from the provided file
        with open(file_location, 'r') as f:
            while True:
                line = f.readline()
                if not line:
                    break
                self.compiler_list.append(line.lstrip().rstrip())

        # List to store the final output lines
        self.output_list = list()

        # Set to store the import modules
        self.import_list = set()

        # Initial indentation level
        self.indent = 0

        # Queue to manage some 'case' entities, for nest cases
        self.case_queue = queue.LifoQueue()

        # Dictionary to manage variables and their path
        self.variable_list = dict()

        # Counter for lines
        self.i = -1

    def __len__(self):
        return len(self.compiler_list)

    def __getitem__(self, key):
        return self.compiler_list[key]

    def __str__(self):
        return ('#!/usr/bin/env python3 -n\n' +
                ('' if len(self.import_list) == 0 else '\n' + ''.join(
                    f'import {i}\n' for i in self.import_list)) + '\n' +
                '\n'.join(self.output_list))

    # Check if reached the end of the list
    def is_end(self):
        return self.i == len(self.compiler_list) - 1

    # Get the next line from the list
    def get_next_line(self):
        self.i += 1
        return self.compiler_list[self.i] if self.i < len(self.compiler_list) else None

    # Insert line into the output list with proper indentation
    def insert_line(self, line):
        if line:
            self.output_list.append('\t' * self.indent + line.replace('\n', '\n' + '\t' * self.indent))

    # Insert case into the case queue
    def insert_case(self, case):
        self.case_queue.put([case, 0])

    # Get the current case from the queue
    def get_case(self):
        case_variable, time = self.case_queue.get()
        self.case_queue.put([case_variable, time + 1])
        return case_variable, time

    # Remove the current case from the queue
    def remove_case(self):
        self.case_queue.get()

    # Insert variable and its path
    def insert_variable(self, variable, path=False):
        self.variable_list[variable] = path

    # Check if a variable exists in the variable list
    def check_variable(self, variable):
        return self.variable_list[variable] if variable in self.variable_list else False

    # Insert module into the import list
    def insert_import(self, module):
        self.import_list.add(module)

    # Write the output list to a Python file
    def output_file(self):
        with open(self.file_name + '.py', 'w') as f:
            f.write(self)

    # Increase the indentation level
    def increase_indent(self):
        self.indent += 1

    # Decrease the indentation level
    def decrease_indent(self):
        self.indent -= 1


if len(sys.argv) != 2:
    print(f'Usage: {sys.argv[0]} <file.sh>')
    sys.exit(1)

compiler = compiler_list(sys.argv[1])


def condition_check(condition):
    condition = condition.lstrip().rstrip()
    check = ''
    # Check if the condition starts with '!' add 'not' to the condition
    if re.search(r'^! ', condition):
        condition = re.sub(r'^!\s+(.*)', r'\1', condition)
        check = 'not '

    # Check if the condition starts with test get the condition
    if re.search(r'^test ', condition):
        condition = re.sub(r'^test\s+(.*)', r'\1', condition)
    # Check if the condition is [ ... ] get the condition
    elif re.search(r'^\[', condition):
        condition = re.sub(r'^\[\s+(.*)\s+]', r'\1', condition)

    # If the condition is an empty string, simply return without any action
    if condition == '':
        return
    # Check if the condition starts with '!' add 'not' to the condition
    elif re.search(r'^! ', condition):
        condition = re.sub(r'^!\s+(.*)', r'\1', condition)
        check += 'not '
        condition = condition_check(condition)
        return f'{check}{condition}'
    # Check if the condition starts with '-e ' check if the file exists
    if re.search(r'^-e ', condition):
        match = re.match(r"^-e (.*)", condition)
        sentence, comment = sentence_process(match.group(1))
        compiler.insert_import('os')
        return f'{check}os.path.exists({sentence})'
    # Check if the condition starts with '-d ' check if it is a directory
    elif re.search(r'^-d ', condition):
        match = re.match(r"^-d (.*)", condition)
        sentence, comment = sentence_process(match.group(1))
        compiler.insert_import('os')
        return f'{check}os.path.isdir({sentence})'
    # Check if the condition starts with '-f ' check if it is a file
    elif re.search(r'^-f ', condition):
        match = re.match(r"^-f (.*)", condition)
        sentence, comment = sentence_process(match.group(1))
        compiler.insert_import('os')
        return f'{check}os.path.isfile({sentence})'
    # Check if the condition starts with '-L ' check if it is a link
    elif re.search(r'^-L ', condition):
        match = re.match(r"^-L (.*)", condition)
        sentence, comment = sentence_process(match.group(1))
        compiler.insert_import('os')
        return f'{check}os.path.islink({sentence})'
    # Check if the condition starts with '-r ' check it is readable
    elif re.search(r'^-r ', condition):
        match = re.match(r"^-r (.*)", condition)
        sentence, comment = sentence_process(match.group(1))
        compiler.insert_import('os')
        return f'{check}os.access({sentence}, os.R_OK)'
    # Check if the condition starts with '-w ' check it is writable
    elif re.search(r'^-w ', condition):
        match = re.match(r"^-w (.*)", condition)
        sentence, comment = sentence_process(match.group(1))
        compiler.insert_import('os')
        return f'{check}os.access({sentence}, os.W_OK)'
    # Check if the condition starts with '-x ' check it is executable
    elif re.search(r'^-x ', condition):
        match = re.match(r"^-x (.*)", condition)
        sentence, comment = sentence_process(match.group(1))
        compiler.insert_import('os')
        return f'{check}os.access({sentence}, os.X_OK)'
    # Check if the condition starts with '-s ' check it is not empty
    elif re.search(r'^-s ', condition):
        match = re.match(r"^-s (.*)", condition)
        sentence, comment = sentence_process(match.group(1))
        compiler.insert_import('os')
        return f'{check}os.path.getsize({sentence}) > 0'
    # Check if the condition starts with '-z ' check it is empty
    elif re.search(r'^-z ', condition):
        match = re.match(r"^-z (.*)", condition)
        sentence, comment = sentence_process(match.group(1))
        return f'{check}not {sentence}'
    # Check if the condition starts with '-n ' check it is not empty
    elif re.search(r'^-n ', condition):
        match = re.match(r"^-n (.*)", condition)
        sentence, comment = sentence_process(match.group(1))
        return f'{check}{sentence}'
    # Check if the condition starts with '=' check it is equal
    elif re.search(r'\s+=\s+', condition):
        match = re.match(r"^(.*)\s+=\s+(.*)", condition)
        sentence1, comment1 = sentence_process(match.group(1))
        sentence2, comment2 = sentence_process(match.group(2))
        return f'{check}{sentence1} == {sentence2}'
    # Check if the condition starts with '!=' check it is not equal
    elif re.search(r'\s+!=\s+', condition):
        match = re.match(r"^(.*)\s+!=\s+(.*)", condition)
        sentence1, comment1 = sentence_process(match.group(1))
        sentence2, comment2 = sentence_process(match.group(2))
        return f'{check}{sentence1} != {sentence2}'
    # Check if the condition starts with '-eq ' check it is equal
    elif re.search(r'\s+-eq\s+', condition):
        match = re.match(r"^(.*)\s+-eq\s+(.*)", condition)
        sentence1, comment1 = sentence_process(match.group(1))
        sentence2, comment2 = sentence_process(match.group(2))
        return f'{check}{sentence1} == {sentence2}'
    # Check if the condition starts with '-ne ' check it is not equal
    elif re.search(r'\s+-ne\s+', condition):
        match = re.match(r"^(.*)\s+-ne\s+(.*)", condition)
        sentence1, comment1 = sentence_process(match.group(1))
        sentence2, comment2 = sentence_process(match.group(2))
        return f'{check}{sentence1} != {sentence2}'
    # Check if the condition starts with '-gt ' check it is >
    elif re.search(r'\s+-gt\s+', condition):
        match = re.match(r"^(.*)\s+-gt\s+(.*)", condition)
        sentence1, comment1 = sentence_process(match.group(1))
        sentence2, comment2 = sentence_process(match.group(2))
        return f'{check}{sentence1} > {sentence2}'
    # Check if the condition starts with '-ge ' check it is >=
    elif re.search(r'\s+-ge\s+', condition):
        match = re.match(r"^(.*)\s+-ge\s+(.*)", condition)
        sentence1, comment1 = sentence_process(match.group(1))
        sentence2, comment2 = sentence_process(match.group(2))
        return f'{check}{sentence1} >= {sentence2}'
    # Check if the condition starts with '-lt ' check it is <
    elif re.search(r'\s+-lt\s+', condition):
        match = re.match(r"^(.*)\s+-lt\s+(.*)", condition)
        sentence1, comment1 = sentence_process(match.group(1))
        sentence2, comment2 = sentence_process(match.group(2))
        return f'{check}{sentence1} < {sentence2}'
    # Check if the condition starts with '-le ' check it is <=
    elif re.search(r'\s+-le\s+', condition):
        match = re.match(r"^(.*)\s+-le\s+(.*)", condition)
        sentence1, comment1 = sentence_process(match.group(1))
        sentence2, comment2 = sentence_process(match.group(2))
        return f'{check}{sentence1} <= {sentence2}'
    else:
        return {check}


def condition_process(condition):
    # Split the condition by '&&' and '||' and process them
    if '&&' in condition:
        out = list()
        comments = ''
        for i in condition.split('&&'):
            next_condition, comments = condition_process(i)
            if next_condition:
                out.append(next_condition)
        return ' and '.join(out), comments
    elif '||' in condition:
        out = list()
        comments = ''
        for i in condition.split('||'):
            next_condition, comments = condition_process(i)
            if next_condition:
                out.append(next_condition)
        return ' or '.join(out), comments
    # Find the comment and process the condition
    elif re.search(r'\s+#', condition):
        match = re.match(r'^(.*)\s+(#.*)', condition)
        return condition_check(match.group(1)), match.group(2)
    else:
        return condition_check(condition), ''


# Process the word, return list of words and their types, 0 means do not need '', 1 means need ''
def word_process(word, input_type=0):
    # Check if the word is empty
    if word == '':
        return [['', -2]]
    # Check if the word is backticks, if so take the command inside the backticks and process it
    elif re.search(r'`', word):
        match = re.match(r'^([^`]*)`(.*)`(.*)', word)
        sentence, comment = sentence_process(match.group(2), 2)
        next_word = word_process(match.group(3), input_type)
        next_word.insert(0, [sentence, 0])
        if match.group(1):
            next_word.insert(0, [match.group(1), 1])
        return next_word
    # Check if the word is double quotes, if so take the formula inside the double quotes and process it
    elif re.search(r'[^\\]?\$\(\(', word):
        match = re.match(r'^([^$]*)\$\(\(([^()]*)\)\)(.*)', word)
        formula = re.sub(r'\$(\w+)', r'\1', match.group(2))
        next_word = word_process(match.group(3), input_type)
        next_word.insert(0, [formula, 0])
        if match.group(1):
            next_word.insert(0, [match.group(1), 1])
        return next_word
    # Check if the word is single quotes, same as backticks
    elif re.search(r'[^\\]?\$\(', word):
        match = re.match(r'^([^$]*)\$\(([^()]*)\)(.*)', word)
        sentence, comment = sentence_process(match.group(2), 2)
        next_word = word_process(match.group(3), input_type)
        next_word.insert(0, [sentence, 0])
        if match.group(1):
            next_word.insert(0, [match.group(1), 1])
        return next_word
    # Check if the word is variable
    elif re.search(r'[^\\]?\$\{', word):
        match = re.match(r'^([^$]*)\$\{([^${}]*)}(.*)', word)
        next_word = word_process(match.group(3), input_type)
        # if the variable is ${1} ... ${10} set as sys.argv[]
        if match.group(2).isdigit():
            compiler.insert_import('sys')
            next_word.insert(0, [f'sys.argv[{match.group(2)}]', 0])
        # if the variable is glob set as glob.glob()
        elif compiler.check_variable(match.group(2)):
            compiler.insert_import('glob')
            next_word.insert(0, [f'" ".join(sorted(glob.glob({match.group(2)})))', 2])
        else:
            next_word.insert(0, [match.group(2), 0])

        if match.group(1):
            next_word.insert(0, [match.group(1), 1])
        return next_word
    # Check if the word is variable without {}
    elif re.search(r'[^\\]?\$', word):
        # if the variable is $# set as len(sys.argv) - 1
        if re.search(r'\$#', word):
            match = re.match(r'([^$#]*)\$#(.*)', word)
            compiler.insert_import('sys')
            next_word = word_process(match.group(2), input_type)
            next_word.insert(0, ['len(sys.argv) - 1', 0])
            if match.group(1):
                next_word.insert(0, [match.group(1), 1])
            return next_word
        # if the variable is $@ set as " ".join(sys.argv[1:])
        elif re.search(r'\$@', word):
            match = re.match(r'([^$@]*)\$@(.*)', word)
            next_word = word_process(match.group(2), input_type)
            compiler.insert_import('sys')
            next_word.insert(0, ['" ".join(sys.argv[1:])', 0])
            if match.group(1):
                next_word.insert(0, [match.group(1), 1])
            return next_word
        # if the variable is $1 ... $9 set as sys.argv[]
        elif re.search(r'\$\d', word):
            match = re.match(r'([^$]*)\$(\d)(.*)', word)
            compiler.insert_import('sys')
            next_word = word_process(match.group(3), input_type)
            next_word.insert(0, [f'sys.argv[{match.group(2)}]', 0])
            if match.group(1):
                next_word.insert(0, [match.group(1), 1])
            return next_word
        # set it until the next not letter or number position
        else:
            match = re.match(r'([^$]*)\$(\w+)(.*)', word)
            next_word = word_process(match.group(3), input_type)
            if compiler.check_variable(match.group(2)):
                compiler.insert_import('glob')
                next_word.insert(0, [f'" ".join(sorted(glob.glob({match.group(2)})))', 0])
            else:
                next_word.insert(0, [match.group(2), 0])

            if match.group(1):
                next_word.insert(0, [match.group(1), 1])
            return next_word
    # Check if the word is glob
    elif input_type == 2 and re.search(r'[*?\[\]]', word):
        compiler.insert_import('glob')
        return [[f'" ".join(sorted(glob.glob("{word}")))', 0], ['', -2]]
    else:
        return [[word, 1], ['', -2]]


# combine the word list to a sentence, if only one 0 type return word without '', only 1 type return word with ''
# else return an f'' sentence
def word_list_process(word_list):
    word_list = word_list[:-1]
    if len(word_list) == 0:
        return ''
    if len(word_list) == 1 and word_list[0][1] == 0:
        return word_list[0][0]

    out = ''
    status = 0
    for i, j in word_list:
        if j == -2:
            out += i
            break
        elif j == 0:
            status = 1
            out += '{' + i + '}'
        elif j == 1:
            out += i

    return "'" + out + "'" if status == 0 else f"f'{out}'"


# process the sentence, return the sentence and comment
def sentence_process(sentence, front=0):
    if sentence == '':
        return '', ''

    sentence = sentence.lstrip()

    # Check if the sentence is comment
    if re.search(r'^#', sentence):
        return '', ' ' + sentence
    # Check if the sentence is double quote
    if re.search(r'^"', sentence):
        match = re.match(r'^"([^"]*)"(.*)', sentence)
        word = word_list_process(word_process(match.group(1)))
        next_sentence, comment = sentence_process(match.group(2))
        if word.isdigit():
            return "'" + word + "'" + next_sentence, comment
        return word + next_sentence, comment
    # Check if the sentence is single quote
    elif re.search(r"^'", sentence):
        match = re.match(r"^'([^']*)'(.*)", sentence)
        next_sentence, comment = sentence_process(match.group(2))
        return "'" + match.group(1) + "'" + ('' if next_sentence == '' else ", " + next_sentence), comment
    # Check if the sentence is backticks
    elif re.search(r'^`', sentence):
        match = re.match(r"^(`[^`]*`)(.*)", sentence)
        word = word_process(match.group(1))
        next_sentence, comment = sentence_process(match.group(2))
        return word_list_process(word) + ('' if next_sentence == '' else ", " + next_sentence), comment
    # Check if the sentence start test which is not condition
    elif re.search(r'^test ', sentence):
        if re.search(r'\s+#', sentence):
            match = re.match(r'^(test.*)(\s+#.*)', sentence)
            next_sentence = condition_check(match.group(1))
            return next_sentence, match.group(2)
        else:
            next_sentence = condition_check(sentence)
            return next_sentence, ''
    # Check if the sentence have [ ] which is not condition
    elif re.search(r'^\[', sentence):
        if re.search(r'\s+#', sentence):
            match = re.match(r'^(\[\s+.*\s+])(\s+#.*)', sentence)
            next_sentence = condition_check(match.group(1))
            return next_sentence, match.group(2)
        else:
            next_sentence = condition_check(sentence)
            return next_sentence, ''
    # Check have any front word
    elif front == 0:
        if re.search(r'^\$\(\(', sentence):
            match = re.match(r'(^\$\(\([^()]*\)\))( ?.*)', sentence)
        elif re.search(r'^\$\(', sentence):
            match = re.match(r'(^\$\([^()]*\))( ?.*)', sentence)
        elif re.search(r'^\$\{', sentence):
            match = re.match(r'(^\$\{[^{}]*})( ?.*)', sentence)
        elif re.search(r'^`', sentence):
            match = re.match(r'(^`[^`]*`)( ?.*)', sentence)
        else:
            match = re.match(r'^([^ ]*)( ?.*)', sentence)
        word = word_process(match.group(1), 2)
        next_sentence, comment = sentence_process(match.group(2))
        return word_list_process(word) + ('' if next_sentence == '' else ", " + next_sentence), comment
    # Set as subprocess to process
    else:
        compiler.insert_import('subprocess')
        match = re.match(r'^([^ ]*) ?(.*)', sentence)
        next_sentence, comment = sentence_process(match.group(2))
        # front 2 means the sentence need assign to a variable
        if front == 2:
            if next_sentence == '':
                return (f"subprocess.run(['{match.group(1)}'], text=True, "
                        f"stdout=subprocess.PIPE).stdout.rstrip('\\n')"), comment
            else:
                return (f"subprocess.run(['{match.group(1)}', {next_sentence}], text=True, "
                        f"stdout=subprocess.PIPE).stdout.rstrip('\\n')"), comment
        # else means can run directly
        else:
            if next_sentence == '':
                return f"subprocess.run(['{match.group(1)}'])", comment
            else:
                return f"subprocess.run(['{match.group(1)}', {next_sentence}])", comment


def line_process(line, out=0):
    line = line.lstrip()
    # Check if the line is shell script start
    if re.search(r'^#!', line):
        return None
    # Check if the line is comment
    elif re.search(r'^#', line):
        return line
    # Check if has > or >> or <
    elif re.search(r'\s+>\s+', line) or re.search(r'\s+>>\s+', line) or re.search(r'\s+<\s+', line):
        return handle_redirection(line)
    # Check if the line is an assignment
    elif re.search(r'^\w+=', line):
        match = re.match(r'(\w+)=([^=]*)', line)
        variable = match.group(1)
        word = match.group(2)
        if re.search(r'^[^\'"`$]', word) and re.search(r'[*?\[\]]', word):
            match = re.match(r'(\w+)=([^= #]*)\s?(.*)', line)
            compiler.insert_import('glob')
            compiler.insert_variable(variable, True)
            return f"{variable} = '{match.group(2)}' " + match.group(3)
        else:
            sentence, comment = sentence_process(word)
            compiler.insert_variable(variable)
            return f'{variable} = {sentence}' + comment
    # Check if the line is echo
    elif re.search(r'^echo ', line):
        line = re.sub(r'^echo\s+', '', line)
        end_flag = True
        if re.search(r'-n', line):
            line = re.sub(r'^-n\s+', '', line)
            end_flag = False
        sentence, comment = sentence_process(line)
        # if the request from handle_redirection, change stream to f
        if end_flag:
            return 'print(' + sentence + ('' if out == 0 else ', file=f') + ') ' + comment
        else:
            return 'print(' + sentence + ('' if out == 0 else ', file=f') + ', end="") ' + comment
    # Check if the line is a for loop
    elif re.search(r'^for ', line):
        # Match the for ... in ...; do
        if re.search(r';\s+do', line):
            match = re.match(r'^for\s+([^#]*)\s+in\s+(.*);\s+do(.*)', line)
            if re.search(r'^\$@', match.group(2)):
                compiler.insert_line(f'for {match.group(1)} in sys.argv[1:]:' + match.group(3))
            else:
                sentence, comment = sentence_process(match.group(2))
                if re.search(r'[*?\[\]]', match.group(2)):
                    sentence = re.sub(r'" "\.join\((sorted\(glob.glob\(.*\)\))\)', r'\1', sentence)
                compiler.insert_line(f'for {match.group(1)} in [{sentence}]:' + match.group(3))
            compiler.increase_indent()
            return
        # Match the for ... in ...
        #           do
        else:
            match = re.match(r'^for\s+([^#]*)\s+in\s+(.*)', line)
            if re.search(r'^\$@', match.group(2)):
                match_1 = re.match(r'^\$@(.*)', match.group(2))
                compiler.insert_line(f'for {match.group(1)} in sys.argv[1:]:' + match_1.group(1))
            else:
                sentence, comment = sentence_process(match.group(2))
                if re.search(r'[*?\[\]]', match.group(2)):
                    sentence = re.sub(r'" "\.join\((sorted\(glob.glob\(.*\)\))\)', r'\1', sentence)
                compiler.insert_line(f'for {match.group(1)} in [{sentence}]:' + comment)
            line = compiler.get_next_line()
            compiler.increase_indent()
            match = re.match(r'^do\s?(.*)', line)
            return match.group(1)
    # Check if the line is a for loop or while loop end
    elif re.search(r'^done', line):
        match = re.match(r'^done ?(.*)', line)
        compiler.decrease_indent()
        return match.group(1)
    # Check if the line is an exit flag
    elif re.search(r'^exit', line):
        compiler.import_list.add('sys')
        return re.sub(r'exit\s*(\d*)(.*)', r'sys.exit(\1)\2', line)
    # Check if the line is a cd command
    elif re.search(r'cd', line):
        compiler.import_list.add('os')
        line = re.sub(r'cd\s*', '', line)
        if line == '':
            return 'os.chdir(os.environ["HOME"])'
        sentence, comment = sentence_process(line)
        return 'os.chdir(' + sentence + ') ' + comment
    # Check if the line is an input command
    elif re.search(r'^read', line):
        match = re.match(r'read\s*([^#]*)\s?(.*)', line)
        return f'{match.group(1)} = input() ' + match.group(2)
    # Check if the line is an if statement
    elif re.search(r'^if', line):
        # Match the if ...; then
        if re.search(r';\s+then', line):
            match = re.match(r'^if\s+(.*);\s+then(.*)', line)
            sentence, comment = condition_process(match.group(1))
            compiler.insert_line(f'if {sentence}:' + match.group(2))
            compiler.increase_indent()
            return
        # Match the if ...
        #           then
        else:
            match = re.match(r'^if\s+(.*)', line)
            sentence, comment = condition_process(match.group(1))
            compiler.insert_line(f'if {sentence}:' + comment)
            compiler.increase_indent()
            line = compiler.get_next_line()
            match = re.match(r'^then\s?(.*)', line)
            return match.group(1)
    # Check if the line is an elif statement
    elif re.search(r'^elif', line):
        # Match the elif ...; then
        if re.search(r';\s+then', line):
            match = re.match(r'^elif\s+(.*);\s+then(.*)', line)
            sentence, comment = condition_process(match.group(1))
            compiler.decrease_indent()
            compiler.insert_line(f'elif {sentence}:' + match.group(2))
            compiler.increase_indent()
            return
        # Match the elif ...
        #           then
        else:
            match = re.match(r'^elif\s+(.*)', line)
            sentence, comment = condition_process(match.group(1))
            compiler.decrease_indent()
            compiler.insert_line(f'elif {sentence}:' + comment)
            compiler.increase_indent()
            line = compiler.get_next_line()
            match = re.match(r'^then\s?(.*)', line)
            return match.group(1)
    # Check if the line is an else statement
    elif re.search(r'^else', line):
        match = re.match(r'^else\s?(.*)', line)
        compiler.decrease_indent()
        compiler.insert_line(f'else:' + match.group(1))
        compiler.increase_indent()
        return
    # Check if the line is an end of if statement
    elif re.search(r'^fi', line):
        match = re.match(r'^fi\s?(.*)', line)
        compiler.decrease_indent()
        return match.group(1)
    # Check if the line is a while loop
    elif re.search(r'while', line):
        # Match the while ...; do
        if re.search(r';\s+do', line):
            match = re.match(r'^while\s+(.*);\s+do(.*)', line)
            condition, comment = condition_process(match.group(1))
            compiler.insert_line(f'while {condition}:' + match.group(2))
            compiler.increase_indent()
            return
        # Match the while ...
        #           do
        else:
            match = re.match(r'^while\s+(.*)', line)
            condition, comment = condition_process(match.group(1))
            compiler.insert_line(f'while {condition}:' + comment)
            compiler.increase_indent()
            line = compiler.get_next_line()
            match = re.match(r'^do\s?(.*)', line)
            return match.group(1)
    # Check if the line is case
    elif re.search(r'case', line):
        match = re.match(r'^case\s+(.*)\s+in\s?(.*)', line)
        compiler.insert_case(sentence_process(match.group(1))[0])
        return match.group(2)
    # Check if the line is case condition
    elif re.search(r'^[^()]+\)', line):
        match = re.match(r'^([^()]+)\)\s?(.*)', line)
        variable, time = compiler.get_case()
        if match.group(1) == '*':
            compiler.insert_line(f'else:' + match.group(2))
        else:
            if '|' in match.group(1):
                out = 'in [' + ','.join([f'\'{x}\'' for x in match.group(1).split('|')]) + ']'
            else:
                out = f'== {match.group(1)}' if match.group(1).isdigit() else f'== \'{match.group(1)}\''
            if time == 0:
                compiler.insert_line(f'if {variable} {out}:' + match.group(2))
            else:
                compiler.insert_line(f'elif {variable} {out}:' + match.group(2))
        compiler.increase_indent()
        return
    # Check if the line is case condition end
    elif re.search(r'^;;', line):
        match = re.match(r'^;;\s?(.*)', line)
        compiler.decrease_indent()
        return match.group(1)
    # Check if the line is end of case
    elif re.search(r'^esac', line):
        match = re.match(r'^esac\s?(.*)', line)
        compiler.remove_case()
        return match.group(1)
    # Check if the line is && or ||
    elif re.search(r'\s+&&\s+', line) or re.search(r'\s+\|\|\s+', line):
        condition = line.split('&&')[0]
        # check if there is || in front of the first &&
        if re.search(r'\s+\|\|\s+', condition):
            condition = condition_check(line.split('||')[0])
            next_sentence = line_process('||'.join(line.split('||')[1:])).replace('\n', '\n\t')
            return f'if not {condition}:\n\t{next_sentence}'
        else:
            condition = condition_check(condition)
            next_sentence = line_process('&&'.join(line.split('&&')[1:])).replace('\n', '\n\t')
            return f'if {condition}:\n\t{next_sentence}'
    else:
        if out == 1:
            sentence, comment = sentence_process(line, 2)
        else:
            sentence, comment = sentence_process(line, 1)
        return sentence + ' ' + comment


# Not finish, only can do echo ... > | >> ..., cat < ...
def handle_redirection(line):
    if "<" in line:
        line = line.replace("<", "")
        return line_process(line, 1)
    elif ">" in line and ">>" not in line:
        cmd, file_name = line.split(">")
        cmd = line_process(cmd, 1).strip()
        match = re.match(r'^\s*([^ ]*)\s?(.*)$', file_name)
        if 'print' in cmd:
            return f"with open('" + match.group(1) + "', 'w') as f: " + match.group(2) + "\n\t" + cmd
        else:
            return f"with open('" + match.group(1) + "', 'w') as f: " + match.group(2) + "\n\tf.write(" + cmd + ")"
    elif ">>" in line:
        cmd, file_name = line.split(">>")
        cmd = line_process(cmd, 1).strip()
        match = re.match(r'^\s*([^ ]*)\s?(.*)$', file_name)
        if 'print' in cmd:
            return f"with open('" + match.group(1) + "', 'a') as f: " + match.group(2) + "\n\t" + cmd
        else:
            return f"with open('" + match.group(1) + "', 'a') as f: " + match.group(2) + "\n\tf.write(" + cmd + ")"


def main():
    while True:
        if compiler.is_end():
            break
        compiler.insert_line(line_process(compiler.get_next_line()))
    print(compiler)


if __name__ == '__main__':
    main()
