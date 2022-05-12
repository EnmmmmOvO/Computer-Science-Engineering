
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "Fs.h"


int Size(File f);

int totalTextSize(Fs fs) {
	// TODO
	return Size(fs->root);
}

int Size(File f) {
	int size = 0;
	FileList start = f->files;
	for (; start != NULL; start = start->next) {
		File fileNow = start->file;
		if (fileNow->type == TEXT_FILE) {
			for (int i = 0; fileNow->text[i] != '\0'; i++) size++;
		}
		if (fileNow->type == DIRECTORY && fileNow->files != NULL) size += Size(fileNow);
	}
	return size;
}

