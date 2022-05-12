// File system implementation

// !!! DO NOT MODIFY THIS FILE !!!

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "Fs.h"

static void doFree(File file);
static void doPrint(File dir, int level);
static FileList newFileNode(File file);

// !!! DO NOT MODIFY THIS FILE !!!

Fs FsNew(void) {
	Fs fs = malloc(sizeof(*fs));
	if (fs == NULL) {
		fprintf(stderr, "error: out of memory\n");
		exit(EXIT_FAILURE);
	}

	fs->root = newDir("");
	return fs;
}

// !!! DO NOT MODIFY THIS FILE !!!

void FsFree(Fs fs) {
	doFree(fs->root);
	free(fs);
}

static void doFree(File file) {
	if (file->type == DIRECTORY) {		
		FileList curr = file->files;
		while (curr != NULL) {
			doFree(curr->file);
			FileList temp = curr;
			curr = curr->next;
			free(temp);
		}
	}
	free(file->name);
	free(file->text);
	free(file);
}

// !!! DO NOT MODIFY THIS FILE !!!

void FsPrint(Fs fs) {
	printf("/\n");
	doPrint(fs->root, 1);
}

static void doPrint(File dir, int level) {
	for (FileList curr = dir->files; curr != NULL; curr = curr->next) {
		for (int i = 0; i < level; i++) {
			printf("    ");
		}
		printf("%s\n", curr->file->name);
		if (curr->file->type == DIRECTORY) {
		    doPrint(curr->file, level + 1);
		}
	}
}

// !!! DO NOT MODIFY THIS FILE !!!

File getRoot(Fs fs) {
	return fs->root;
}

// !!! DO NOT MODIFY THIS FILE !!!

File newDir(char *name) {
	File file = malloc(sizeof(*file));
	if (file == NULL) {
		fprintf(stderr, "error: out of memory\n");
		exit(EXIT_FAILURE);
	}

	file->name = strdup(name);
	file->type = DIRECTORY;
	file->text = NULL;
	file->files = NULL;
	return file;
}

// !!! DO NOT MODIFY THIS FILE !!!

File newTextFile(char *name, char *content) {
	File file = malloc(sizeof(*file));
	if (file == NULL) {
		fprintf(stderr, "error: out of memory\n");
		exit(EXIT_FAILURE);
	}

	file->name = strdup(name);
	file->type = TEXT_FILE;
	file->text = strdup(content);
	file->files = NULL;
	return file;
}

// !!! DO NOT MODIFY THIS FILE !!!

void addFileToDir(File dir, File file) {
	if (dir->type != DIRECTORY) {
		fprintf(stderr, "addFileToDir: error: "
		                "'dir' is not a directory\n");
		exit(EXIT_FAILURE);
	}
	
	FileList n = newFileNode(file);
	if (dir->files == NULL) {
		dir->files = n;
	} else {
		FileList curr = dir->files;
		while (curr->next != NULL) {
			curr = curr->next;
		}
		curr->next = n;
	}
}

// !!! DO NOT MODIFY THIS FILE !!!

static FileList newFileNode(File file) {
	FileList n = malloc(sizeof(*n));
	if (n == NULL) {
		fprintf(stderr, "error: out of memory\n");
		exit(EXIT_FAILURE);
	}

	n->file = file;
	n->next = NULL;
	return n;
}

// !!! DO NOT MODIFY THIS FILE !!!

