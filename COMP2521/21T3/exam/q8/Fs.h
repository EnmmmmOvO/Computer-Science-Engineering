// File system interface

// !!! DO NOT MODIFY THIS FILE !!!

#ifndef FS_H
#define FS_H

typedef enum {
	DIRECTORY,
	TEXT_FILE,
} FileType;

typedef struct Fs *Fs;
typedef struct File *File;
typedef struct FileList *FileList;

struct Fs {
	File root;
};

struct File {
	char    *name;
	FileType type;  // DIRECTORY or TEXT_FILE
	char    *text;  // NULL if and only if the file is a directory
	FileList files; // NULL if and only if the file is a text file
	                // or if the file is a directory and the directory
	                // is empty
};

struct FileList {
	File     file;
	FileList next;
};

// !!! DO NOT MODIFY THIS FILE !!!

// Creates a new file system with an empty root directory
Fs FsNew(void);

// Frees all memory associated with the given file system
void FsFree(Fs fs);

// Prints out the file system in a tree-like format
void FsPrint(Fs fs);

// Returns the root directory of the given file system
File getRoot(Fs fs);

// Returns a new directory with the given name
// Note: This DOES NOT add the directory to the file system. A file is
//       only added to the file system once you use addFileToDir to add
//       it to a directory that is already attached to the file system.
File newDir(char *name);

// Returns a new text file with the given name and content 
// Note: This DOES NOT add the text file to the file system. A file is
//       only added to the file system once you use addFileToDir to add
//       it to a directory that is already attached to the file system.
File newTextFile(char *name, char *content);

// Adds a file to the given directory
void addFileToDir(File dir, File file);

#endif

// !!! DO NOT MODIFY THIS FILE !!!

