// Interface to the File System ADT
// COMP2521 Assignment 1

// !!! DO NOT MODIFY THIS FILE !!!

#ifndef FS_H
#define FS_H

#define PATH_MAX 4096

typedef struct FsRep *Fs;

Fs FsNew(void);

void FsGetCwd(Fs fs, char cwd[PATH_MAX + 1]);

void FsFree(Fs fs);

void FsMkdir(Fs fs, char *path);

void FsMkfile(Fs fs, char *path);

void FsCd(Fs fs, char *path);

void FsLs(Fs fs, char *path);

void FsPwd(Fs fs);

void FsTree(Fs fs, char *path);

void FsPut(Fs fs, char *path, char *content);

void FsCat(Fs fs, char *path);

void FsDldir(Fs fs, char *path);

void FsDl(Fs fs, bool recursive, char *path);

void FsCp(Fs fs, bool recursive, char *src[], char *dest);

void FsMv(Fs fs, char *src[], char *dest);

#endif

