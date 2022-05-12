#include <sys/types.h>

#include <sys/stat.h>

#include <assert.h>
#include <fcntl.h>
#include <stdbool.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <unistd.h>


static char **tokenize (char *string, char *separator);
static void free_tokens (char **tokens);
static bool is_executable (char *pathname);

static void temp(char **path, char *name);

int main (int argc, char *argv[])
{
	char *environ = getenv("PATH");
	char **path = tokenize(environ, ":");

	for (int loop = 1; loop < argc; loop++) temp(path, argv[loop]);
	free_tokens(path);
	return 0;
}

static void temp(char **path, char *name) {
	int loop = 0;
	for (char **dir = path; *dir != NULL; dir++) {
		size_t length = strlen(*dir) + strlen(name) + 2;
		char *pathname = malloc(length);
		snprintf(pathname, length, "%s/%s", *dir, name);
		if (faccessat (AT_FDCWD, pathname, X_OK, AT_EACCESS) == 0) {
			puts(pathname);
			loop = 1;
		}
		free(pathname);
	}
	if (loop == 0) {
		printf ("%s not found\n", name);
	}
}


////////////////////////////////////////////////////////////////////////
//    . . . you do not need to modify code beyond this point . . .    //

//
// Split a string 'str' into pieces by any one of a set of separators.
// Returns an array of strings, with the last element being `NULL'.
// The array itself, and the strings, are allocated with `malloc(3)';
// the provided `free_token' function can deallocate this.
//
static char **
tokenize (char *str, char *sep)
{
	size_t n_tokens = 0;
	char **tokens = NULL;

	while (*str != '\0') {
		// We are pointing at zero or more of any of the separators.
		// Skip all leading instances of the separators.
		str += strspn (str, sep);

		// Trailing separators after the last token mean that, at this
		// point, we are looking at the end of the string, so:
		if (*str == '\0')
			break;

		// Now, `s' points at one or more characters we want to keep.
		// The number of non-separator characters is the token length.
		// Allocate a copy of the token, and preserve it.
		size_t len = strcspn (str, sep);
		char *tok = strndup (str, len);
		assert (tok != NULL);
		str += len;

		// Add this token.  (Should really use reallocarray(3) here.)
		tokens = realloc (tokens, ++n_tokens * sizeof *tokens);
		tokens[n_tokens - 1] = tok;
	}

	// Add the final `NULL'.
	tokens = realloc (tokens, ++n_tokens * sizeof *tokens);
	tokens[n_tokens - 1] = NULL;

	return tokens;
}

//
// Free an array of strings.
//
static void
free_tokens (char **tokens)
{
	for (int i = 0; tokens != NULL && tokens[i] != NULL; i++)
		free (tokens[i]);

	free (tokens);
}


//
// Check whether this process can execute a file.
//
static bool
is_executable (char *pathname)
{
	struct stat s;
	return
		// does the file exist?
		stat (pathname, &s) == 0 &&
		// is the file a regular file?
		S_ISREG (s.st_mode) &&
		// can we execute it?
		faccessat (AT_FDCWD, pathname, X_OK, AT_EACCESS) == 0;
}
