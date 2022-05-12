/// Implementation of the File System ADT
// COMP2521 Assignment 1

// Written by: Jinghan Wang
// Date: 29/10/2021

#include <assert.h>
#include <ctype.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "FileType.h"
#include "Fs.h"
#include "utility.h"

struct FsRep { 
    char *name;
    FileType type;
    int size;
    Fs position;
    Fs *dir;
};

Fs FsNew(void) {
    // TODO
    Fs new = malloc(sizeof(Fs));
    if (new == NULL) {
        printf("Cannot allocate FsRep!\n");
        return NULL;
    }
    new->name = "root";
    new->type = DIRECTORY;
    new->size = 0;
    new->position = new;
    new->dir = malloc(sizeof(Fs));
    new->dir[0] = new;
    return new;
}

void FsGetCwd(Fs fs, char cwd[PATH_MAX + 1]) {
    // TODO
}

void FsFree(Fs fs) {
    // TODO
    if (fs->type ==  REGULAR_FILE) {
        if (fs->dir[1] != NULL) {
            free(fs->dir[1]);
            free(fs);
        }
    } else if (fs->type == DIRECTORY && fs->size != 0) {
        for (int loop = 1; loop <= fs->size; loop++) {
            FsFree(fs->dir[loop]);
        }
        free(fs);
    } else {
        free(fs);
    }
    
    return;
}

void blacnceTree(Fs fs) {
    int sizeNum = fs->size;
    if (sizeNum == 0) {
        return;
    } else {
        for (int i = 1; i < sizeNum; i++) {
            for (int j = i + 1; j <= sizeNum; j++) {
                if (strcmp(fs->dir[i]->name, fs->dir[j]->name) > 0) {
                    Fs temp = fs->dir[i];
                    fs->dir[i] = fs->dir[j];
                    fs->dir[j] = temp;
                }
            }
        }
        for (int loop = 1; loop <= sizeNum; loop++) {
            blacnceTree(fs->dir[loop]);
        }
    }
}

void FsMkdir(Fs fs, char *path) {
    // TODO
    Fs f = fs->position;
    char *pathOrigin = malloc(sizeof(char) * strlen(path));
    char *dirName;
    int temp = 0;

    
    for (int loop = 0; loop < strlen(path) && path[loop] != '\0'; loop++) {
        if (path[loop] == '/') temp = 1;
        pathOrigin[loop] = path[loop];
    }
    

    if (temp == 1) {
        dirName = strtok(pathOrigin, "/");

        if (strcmp(dirName, ".") == 0) {
            dirName = strtok(NULL, "/");
        }

        while (dirName != NULL) {
            char *tempChar;
            tempChar = strtok(NULL, "/");

            if (tempChar == NULL) {
                break;
            } else {
                if (strcmp(dirName, ".") == 0) {
                    dirName = tempChar;
                    continue;
                }

                if (strcmp(dirName, "..") == 0) {
                    f = f->dir[0];
                    dirName = tempChar;
                    continue;
                }

                int loop;
                for (loop = 1, temp = 0; temp == 0 && loop <= f->size; loop++) {
                    if (strcmp(f->dir[loop]->name, dirName) == 0) {
                        if (f->dir[loop]->type != DIRECTORY) {
                            printf("mkdir: cannot create directory '%s': Not a directory\n", path);
                            return;
                        }
                        temp = 1;
                        break;
                    }
                }

                if (temp == 1) {
                    dirName = tempChar;
                    f = f->dir[loop];
                } else {
                    printf("mkdir: cannot create directory '%s': No such file or directory\n", path);
                    return ;
                }
            }
        }   
    } else {
        dirName = path;
    }
    
    if (strcmp(dirName, ".") == 0 || strcmp(dirName, "..") == 0) {
        printf("mkdir: cannot create directory '%s': File exists\n", path);
        return;
    }

    for (int loop = 0; dirName[loop] != '\0'; loop++) {
        if (!(isalnum(dirName[loop]) || dirName[loop] == '.' ||  dirName[loop] == '_' || dirName[loop] == '-')) {
            printf("%c is an unsupported character!\n", dirName[loop]);
            return ;
        }
    }


    int loop;
    for (loop = 1; loop <= f->size; loop++) {
        if (strcmp(dirName, f->dir[loop]->name) == 0) {
            printf("mkdir: cannot create directory '%s': File exists\n", path);
            return;
        }
    }


    Fs new = malloc(sizeof(Fs));
    new->name = dirName;
    new->type = DIRECTORY;
    new->size = 0;
    new->dir = malloc(sizeof(Fs));
    new->dir[0] = f;

    f->size++;
    Fs *tempDir = malloc(sizeof(Fs) * (f->size + 1));
    tempDir[f->size] = new;

    for (loop = 0; loop < f->size; loop++) {
        tempDir[loop] = f->dir[loop];
    }

    f->dir = tempDir;
    blacnceTree(f);
}


void FsMkfile(Fs fs, char *path) {
    // TODO
    Fs f = fs->position;
    char *pathOrigin = malloc(sizeof(char) * strlen(path));
    char *dirName;
    int temp = 0;

    
    for (int loop = 0; loop < strlen(path) && path[loop] != '\0'; loop++) {
        if (path[loop] == '/') temp = 1;
        pathOrigin[loop] = path[loop];
    }
    

    if (temp == 1) {
        dirName = strtok(pathOrigin, "/");

        if (strcmp(dirName, ".") == 0) {
            dirName = strtok(NULL, "/");
        }

        while (dirName != NULL) {
            char *tempChar;
            tempChar = strtok(NULL, "/");

            if (tempChar == NULL) {
                break;
            } else {
                if (strcmp(dirName, ".") == 0) {
                    dirName = tempChar;
                    continue;
                }

                if (strcmp(dirName, "..") == 0) {
                    f = f->dir[0];
                    dirName = tempChar;
                    continue;
                }

                int loop;
                for (loop = 1, temp = 0; temp == 0 && loop <= f->size; loop++) {
                    if (strcmp(f->dir[loop]->name, dirName) == 0) {
                        if (f->dir[loop]->type != DIRECTORY) {
                            printf("mkfile: cannot create directory '%s': Not a directory\n", path);
                            return;
                        }
                        temp = 1;
                        break;
                    }
                }

                if (temp == 1) {
                    dirName = tempChar;
                    f = f->dir[loop];
                } else {
                    printf("mkfile: cannot create directory '%s': No such file or directory\n", path);
                    return ;
                }
            }
        }   
    } else {
        dirName = path;
    }
    
    if (strcmp(dirName, ".") == 0 || strcmp(dirName, "..") == 0) {
        printf("mkfile: cannot create directory '%s': File exists\n", path);
        return;
    }

    for (int loop = 0; dirName[loop] != '\0'; loop++) {
        if (!(isalnum(dirName[loop]) || dirName[loop] == '.' ||  dirName[loop] == '_' || dirName[loop] == '-')) {
            printf("%c is an unsupported character!\n", dirName[loop]);
            return ;
        }
    }


    int loop;
    for (loop = 1; loop <= f->size; loop++) {
        if (strcmp(dirName, f->dir[loop]->name) == 0) {
            printf("mkfile: cannot create directory '%s': File exists\n", path);
            return;
        }
    }


    Fs new = malloc(sizeof(Fs));
    new->name = dirName;
    new->type = REGULAR_FILE;
    new->size = -1;
    new->dir = malloc(sizeof(Fs));
    new->dir[0] = f;

    f->size++;
    Fs *tempDir = malloc(sizeof(Fs) * (f->size + 1));
    tempDir[f->size] = new;

    for (loop = 0; loop < f->size; loop++) {
        tempDir[loop] = f->dir[loop];
    }

    f->dir = tempDir;
    blacnceTree(f);
    
}


void FsCd(Fs fs, char *path) {
    // TODO
    if (path == NULL) {
        fs->position = fs;
        return;
    }
    
    if (strcmp(path, "/") == 0) {
        fs->position = fs;
        return;
    }

    Fs f = fs->position;
    Fs copy = f;
    char *pathOrigin = malloc(sizeof(char) * strlen(path));
    char *dirName;
    int temp = 0;

    
    for (int loop = 0; loop < strlen(path) && path[loop] != '\0'; loop++) {
        if (path[loop] == '/') temp = 1;
        pathOrigin[loop] = path[loop];
    }
    
    dirName = strtok(pathOrigin, "/");

    if (strcmp(dirName, ".") == 0) {
        dirName = strtok(NULL, "/");
    }

    while (dirName != NULL) {
        char *tempChar;
        tempChar = strtok(NULL, "/");

        if (strcmp(dirName, ".") == 0) {
            dirName = tempChar;
            continue;
        }

        if (strcmp(dirName, "..") == 0) {
            f = f->dir[0];
            dirName = tempChar;
            continue;
        }

        int loop;
        for (loop = 1, temp = 0; loop <= f->size; loop++) {
            if (strcmp(f->dir[loop]->name, dirName) == 0) {
                if (f->dir[loop]->type != DIRECTORY) {
                    printf("cd: '%s': Not a directory\n", path);
                    fs->position = copy;
                    return;
                }
                temp = 1;
                break;
            }
        }

        if (temp == 1) {
            dirName = tempChar;
            f = f->dir[loop];
        } else {
            printf("cd: '%s': No such file or directory\n", path);
            fs->position = copy;
            return ;
        }

    }  
    fs->position = f; 
}

void FsLs(Fs fs, char *path) {
    // TODO
    Fs f = fs->position;
    if (path != NULL) {
        if (strcmp(path, "/") == 0) {
            f = fs;
        } else {
            char *pathOrigin = malloc(sizeof(char) * strlen(path));
            char *dirName;
            int temp = 0;

            
            
            for (int loop = 0; loop < strlen(path) && path[loop] != '\0'; loop++) {
                if (path[loop] == '/') temp = 1;
                pathOrigin[loop] = path[loop];
            }
            
            dirName = strtok(pathOrigin, "/");

            if (strcmp(dirName, ".") == 0) {
                dirName = strtok(NULL, "/");
            }

            while (dirName != NULL) {
                char *tempChar;
                tempChar = strtok(NULL, "/");

                if (strcmp(dirName, ".") == 0) {
                    dirName = tempChar;
                    continue;
                }

                if (strcmp(dirName, "..") == 0) {
                    f = f->dir[0];
                    dirName = tempChar;
                    continue;
                }

                int loop;
                for (loop = 1, temp = 0; temp == 0 && loop <= f->size; loop++) {
                    if (strcmp(f->dir[loop]->name, dirName) == 0) {
                        if (f->dir[loop]->type != DIRECTORY) {
                            if (tempChar == NULL) {
                                printf("%s\n", path);
                            } else {
                                printf("ls: cannot access '%s': Not a directory\n", path);
                            }
                            return;
                        }
                        temp = 1;
                        break;
                    }
                }

                if (temp == 1) {
                    dirName = tempChar;
                    f = f->dir[loop];
                } else {
                    printf("ls: cannot access '%s': No such file or directory\n", path);
                    return ;
                }
            }
        }
    }

    for (int loop = 1; loop <= f->size; loop++) printf("%s\n", f->dir[loop]->name);
    
}


void FsPwd(Fs fs) {
    // TODO
    Fs f = fs->position;
    char **temp = malloc(sizeof(char) * PATH_MAX);
    int loop = 0;
    for (; f != fs; f = f->dir[0], loop++) temp[loop] = f->name;
    printf("/");
    for (loop--; loop >= 0; loop--) {
        printf("%s", temp[loop]);
        if (loop != 0) printf("/");
    }
    printf("\n");
}

void static printTree(Fs fs, int deep) {
    if (fs->size == 0) {
        return;
    } else {
        for (int loop = 1; loop <= fs->size; loop++) {
            for (int loopA = 0; loopA < deep * 4; loopA++) printf(" ");
            printf("%s\n", fs->dir[loop]->name);
            printTree(fs->dir[loop], deep + 1);
        }
    }
}

void FsTree(Fs fs, char *path) {
    // TODO
    if (path != NULL) {
        if (strcmp(path, "/") == 0) {
            fs->position = fs;
            return;
        }

        Fs f = fs->position;
        Fs copy = f;
        char *pathOrigin = malloc(sizeof(char) * strlen(path));
        char *dirName;
        int temp = 0;

        
        for (int loop = 0; loop < strlen(path) && path[loop] != '\0'; loop++) {
            if (path[loop] == '/') temp = 1;
            pathOrigin[loop] = path[loop];
        }
        
        dirName = strtok(pathOrigin, "/");

        if (strcmp(dirName, ".") == 0) {
            dirName = strtok(NULL, "/");
        }

        while (dirName != NULL) {
            char *tempChar;
            tempChar = strtok(NULL, "/");

            if (strcmp(dirName, ".") == 0) {
                dirName = tempChar;
                continue;
            }

            if (strcmp(dirName, "..") == 0) {
                f = f->dir[0];
                dirName = tempChar;
                continue;
            }

            int loop;
            for (loop = 1, temp = 0; loop <= f->size; loop++) {
                if (strcmp(f->dir[loop]->name, dirName) == 0) {
                    if (f->dir[loop]->type != DIRECTORY) {
                        printf("tree: '%s': Not a directory\n", path);
                        fs->position = copy;
                        return;
                    }
                    temp = 1;
                    break;
                }
            }

            if (temp == 1) {
                dirName = tempChar;
                f = f->dir[loop];
            } else {
                printf("tree: '%s': No such file or directory\n", path);
                fs->position = copy;
                return ;
            }
        }  
        fs->position = f; 
    } else {
        fs->position = fs;
    }
    FsPwd(fs);  

    Fs f = fs->position;
    printTree(f, 1);
}



void FsPut(Fs fs, char *path, char *content) {
    // TODO
    if (strcmp(path, ".") == 0 || strcmp(path, "..") == 0 || strcmp(path, "/") == 0) {
        printf("put: '%s': Is a directory\n", path);
        return;
    }

    Fs f = fs->position;
    char *pathOrigin = malloc(sizeof(char) * strlen(path));
    char *dirName;
    int temp = 0;

    
    for (int loop = 0; loop < strlen(path) && path[loop] != '\0'; loop++) {
        if (path[loop] == '/') temp = 1;
        pathOrigin[loop] = path[loop];
    }
    

    if (temp == 1) {
        dirName = strtok(pathOrigin, "/");

        if (strcmp(dirName, ".") == 0) {
            dirName = strtok(NULL, "/");
        }

        while (dirName != NULL) {
            char *tempChar;
            tempChar = strtok(NULL, "/");

            if (tempChar == NULL) {
                break;
            } else {
                if (strcmp(dirName, ".") == 0) {
                    dirName = tempChar;
                    continue;
                }

                if (strcmp(dirName, "..") == 0) {
                    f = f->dir[0];
                    dirName = tempChar;
                    continue;
                }

                int loop;
                for (loop = 1, temp = 0; temp == 0 && loop <= f->size; loop++) {
                    if (strcmp(f->dir[loop]->name, dirName) == 0) {
                        if (f->dir[loop]->type != DIRECTORY) {
                            printf("put: '%s': Not a directory\n", path);
                            return;
                        }
                        temp = 1;
                        break;
                    }
                }

                if (temp == 1) {
                    dirName = tempChar;
                    f = f->dir[loop];
                } else {
                    printf("put: '%s': No such file or directory\n", path);
                    return ;
                }
            }
        }   
    } else {
        dirName = path;
    }

    if (strcmp(dirName, ".") == 0 || strcmp(dirName, "..") == 0) {
        printf("put: '%s': Is a directory\n", path);
        return;
    }

    int loop;
    for (loop = 1, temp = 0; loop <= f->size; loop++) {
        if (strcmp(f->dir[loop]->name, dirName) == 0) {
            if (f->dir[loop]->type == DIRECTORY) {
                printf("put: '%s': Is a directory\n", path);
                return;
            }
            temp = 1;
            break;
        }
    }

    if (temp != 1) {
        printf("put: '%s': No such file or directory\n", path);
        return ;
    }

    Fs new = malloc(sizeof(Fs));
    new->name = malloc(sizeof(char) * strlen(content));
    for (int loop = 0; loop < strlen(content); loop++) 
        new->name[loop] = content[loop];

    Fs *tempFs = malloc(sizeof(Fs) * 2);
    tempFs[0] = f->dir[loop]->dir[0];
    tempFs[1] = new;

    f->dir[loop]->dir = tempFs;


    
}

void FsCat(Fs fs, char *path) {
    // TODO
    
    if (strcmp(path, ".") == 0 || strcmp(path, "..") == 0 || strcmp(path, "/") == 0) {
        printf("cat: '%s': Is a directory\n", path);
        return;
    }

    Fs f = fs->position;
    char *pathOrigin = malloc(sizeof(char) * strlen(path));
    char *dirName;
    int temp = 0;

    
    for (int loop = 0; loop < strlen(path) && path[loop] != '\0'; loop++) {
        if (path[loop] == '/') temp = 1;
        pathOrigin[loop] = path[loop];
    }
    

    if (temp == 1) {
        dirName = strtok(pathOrigin, "/");

        if (strcmp(dirName, ".") == 0) {
            dirName = strtok(NULL, "/");
        }

        while (dirName != NULL) {
            char *tempChar;
            tempChar = strtok(NULL, "/");

            if (tempChar == NULL) {
                break;
            } else {
                if (strcmp(dirName, ".") == 0) {
                    dirName = tempChar;
                    continue;
                }

                if (strcmp(dirName, "..") == 0) {
                    f = f->dir[0];
                    dirName = tempChar;
                    continue;
                }

                int loop;
                for (loop = 1, temp = 0; temp == 0 && loop <= f->size; loop++) {
                    if (strcmp(f->dir[loop]->name, dirName) == 0) {
                        if (f->dir[loop]->type != DIRECTORY) {
                            printf("cat: '%s': Not a directory\n", path);
                            return;
                        }
                        temp = 1;
                        break;
                    }
                }

                if (temp == 1) {
                    dirName = tempChar;
                    f = f->dir[loop];
                } else {
                    printf("cat: '%s': No such file or directory\n", path);
                    return ;
                }
            }
        }   
    } else {
        dirName = path;
    }
    
    int loop;
    for (loop = 1, temp = 0; loop <= f->size; loop++) {
        if (strcmp(f->dir[loop]->name, dirName) == 0) {
            if (f->dir[loop]->type == DIRECTORY) {
                printf("cat: '%s': Is a directory\n", path);
                return;
            }
            temp = 1;
            break;
        }
    }

    if (temp != 1) {
        printf("cat: '%s': No such file or directory\n", path);
        return ;
    }

    if (f->dir[loop]->dir[1] != NULL) printf("%s", f->dir[loop]->dir[1]->name);
    
}



void FsDldir(Fs fs, char *path) {
    // TODO
    Fs f = fs->position;
    char *pathOrigin = malloc(sizeof(char) * strlen(path));
    char *dirName;
    int temp = 0;

    
    for (int loop = 0; loop < strlen(path) && path[loop] != '\0'; loop++) {
        if (path[loop] == '/') temp = 1;
        pathOrigin[loop] = path[loop];
    }
    

    if (temp == 1) {
        dirName = strtok(pathOrigin, "/");

        if (strcmp(dirName, ".") == 0) {
            dirName = strtok(NULL, "/");
        }

        while (dirName != NULL) {
            char *tempChar;
            tempChar = strtok(NULL, "/");

            if (tempChar == NULL) {
                break;
            } else {
                if (strcmp(dirName, ".") == 0) {
                    dirName = tempChar;
                    continue;
                }

                if (strcmp(dirName, "..") == 0) {
                    f = f->dir[0];
                    dirName = tempChar;
                    continue;
                }

                int loop;
                for (loop = 1, temp = 0; temp == 0 && loop <= f->size; loop++) {
                    if (strcmp(f->dir[loop]->name, dirName) == 0) {
                        if (f->dir[loop]->type != DIRECTORY) {
                            printf("dldir: failed to remove '%s': Not a directory\n", path);
                            return;
                        }
                        temp = 1;
                        break;
                    }
                }

                if (temp == 1) {
                    dirName = tempChar;
                    f = f->dir[loop];
                } else {
                    printf("dldir: failed to remove '%s': No such file or directory\n", path);
                    return ;
                }
            }
        }   
    } else {
        dirName = path;
    }

    int loop;
    for (loop = 1, temp = 0; loop <= f->size; loop++) {
        if (strcmp(f->dir[loop]->name, dirName) == 0) {
            if (f->dir[loop]->type == REGULAR_FILE) {
                printf("dldir: failed to remove '%s': Not a directory\n", path);
                return;
            }
            temp = 1;
            break;
        }
    }

    if (temp != 1) {
        printf("dldir: failed to remove '%s: No such file or directory\n", path);
        return ;
    }

    if (f->dir[loop]->size != 0) {
        printf("dldir: failed to remove '%s: Directory not empty\n", path);
        return;
    } 

    
    f->size--;
    Fs *tempFs = malloc(sizeof(Fs) * f->size);
    for (int i = 0, j = 0; i < f->size; i++, j++) {
        if (j == loop) j++;
        tempFs[i] = f->dir[j];
    }

    free(f->dir[loop]);
    f->dir = tempFs;

}

void FsDl(Fs fs, bool recursive, char *path) {
    // TODO
    Fs f = fs->position;
    char *pathOrigin = malloc(sizeof(char) * strlen(path));
    char *dirName;
    int temp = 0;

    
    for (int loop = 0; loop < strlen(path) && path[loop] != '\0'; loop++) {
        if (path[loop] == '/') temp = 1;
        pathOrigin[loop] = path[loop];
    }
    

    if (temp == 1) {
        dirName = strtok(pathOrigin, "/");

        if (strcmp(dirName, ".") == 0) {
            dirName = strtok(NULL, "/");
        }

        while (dirName != NULL) {
            char *tempChar;
            tempChar = strtok(NULL, "/");

            if (tempChar == NULL) {
                break;
            } else {
                if (strcmp(dirName, ".") == 0) {
                    dirName = tempChar;
                    continue;
                }

                if (strcmp(dirName, "..") == 0) {
                    f = f->dir[0];
                    dirName = tempChar;
                    continue;
                }

                int loop;
                for (loop = 1, temp = 0; temp == 0 && loop <= f->size; loop++) {
                    if (strcmp(f->dir[loop]->name, dirName) == 0) {
                        if (f->dir[loop]->type != DIRECTORY) {
                            printf("dl: failed to remove '%s': Not a directory\n", path);
                            return;
                        }
                        temp = 1;
                        break;
                    }
                }

                if (temp == 1) {
                    dirName = tempChar;
                    f = f->dir[loop];
                } else {
                    printf("dl: failed to remove '%s': No such file or directory\n", path);
                    return ;
                }
            }
        }   
    } else {
        dirName = path;
    }

    int loop;
    for (loop = 1, temp = 0; loop <= f->size; loop++) {
        if (strcmp(f->dir[loop]->name, dirName) == 0) {
            temp = 1;
            break;
        }
    }

    if (temp != 1) {
        printf("dl: failed to remove '%s: No such file or directory\n", path);
        return ;
    }

    if (f->dir[loop]->type == DIRECTORY && recursive == 0) {
        printf("dl: cannot remove '%s': Is a directory\n", path);
    }

    f->size--;
    Fs *tempFs = malloc(sizeof(Fs) * f->size);
    for (int i = 0, j = 0; i <= f->size; i++, j++) {
        if (j == loop) j++;
        tempFs[i] = f->dir[j];
    }

    FsFree(f->dir[loop]);
    f->dir = tempFs;
}

void static copy(Fs new, Fs old) {
    for (int loop = 0; loop < strlen(old->name); loop++)
        new->name[loop] = old->name[loop];
    new->type = old->type;
    new->position = old->position;
    new->size = old->size;
    new->dir = malloc(sizeof(new->size));
    new->dir[0] = new;
    for (int loop = 1; loop <= old->size; loop++) {
        Fs new1 = malloc(sizeof(Fs));
        new->dir[loop] = new1;
        copy(new1, old->dir[loop]);
    }
}

void FsCp(Fs fs, bool recursive, char *src[], char *dest) {
    // TODO 
    int loopSrc = 0;
    int loopDest = 0;
    for (int loop = 1; loop <= fs->size; loop++) {
        if (strcmp(src[0], fs->dir[loop]->name) == 0) {
            loopSrc = loop;
        }
        if (strcmp(dest, fs->dir[loop]->name) == 0) {
            loopDest = loop;
        }
    }

    int loop = 0;
    if (fs->dir[loopSrc]->type == REGULAR_FILE) {
        if (loopDest == 0) {
            Fs f = fs;
            Fs new = malloc(sizeof(Fs));
            new->name = dest;
            new->dir = REGULAR_FILE;
            new->size = 0; 
            if (fs->dir[loopSrc]->dir[1] != NULL) {
                new->dir = malloc(sizeof(Fs) * 2);
                new->dir[0] = fs;
                new->dir[1] = malloc(sizeof(Fs));
                new->dir[1]->name = fs->dir[loopSrc]->dir[1]->name;
            } else {
                new->dir = malloc(sizeof(Fs));
                new->dir[0] = fs;
            }

            f->size++;
            Fs *tempDir = malloc(sizeof(Fs) * (f->size + 1));
            tempDir[f->size] = new;

            for (loop = 0; loop < f->size; loop++) {
                tempDir[loop] = f->dir[loop];
            }

            f->dir = tempDir;

        } else {
            if (fs->dir[loopDest]->type == REGULAR_FILE) {
                if (fs->dir[loopSrc]->dir[1] != NULL) {
                    
                    Fs *tempFs = malloc(sizeof(Fs) * 2);
                    tempFs[0] = fs;
                    tempFs[1] = malloc(sizeof(Fs));
                    tempFs[1]->name = fs->dir[loopSrc]->dir[1]->name;
                    fs->dir[loopDest]->dir = tempFs;
                } 
            } else {
                Fs f = fs->dir[loopDest];
                Fs new = malloc(sizeof(Fs));
                new->name = dest;
                new->dir = REGULAR_FILE;
                new->size = 0; 
                if (fs->dir[loopSrc]->dir[1] != NULL) {
                    new->dir = malloc(sizeof(Fs) * 2);
                    new->dir[0] = f;
                    new->dir[1] = malloc(sizeof(Fs));
                    new->dir[1]->name = fs->dir[loopSrc]->dir[1]->name;
                } else {
                    new->dir = malloc(sizeof(Fs));
                    new->dir[0] = f;
                }

                f->size++;
                Fs *tempDir = malloc(sizeof(Fs) * (f->size + 1));
                tempDir[f->size] = new;

                for (loop = 0; loop < f->size; loop++) {
                    tempDir[loop] = f->dir[loop];
                }

                f->dir = tempDir;
            }
        }
    } else {
        if (recursive == true) {
            Fs new = malloc(sizeof(Fs));
            copy(new, fs->dir[loopSrc]);
            Fs f;
            if (loopDest == 0) {
                f = fs;
            } else {
                f = fs->dir[loopDest];
            }
            new->dir[0] = f;
            f->size++;
            Fs *tempDir = malloc(sizeof(Fs) * (f->size + 1));
            tempDir[f->size] = new;

            for (loop = 0; loop < f->size; loop++) {
                tempDir[loop] = f->dir[loop];
            }

            f->dir = tempDir;
        } else {
            Fs f = fs->dir[loopDest];
            Fs *tempDir = malloc(sizeof(Fs) * (f->size + fs->dir[loopSrc]->size + 1));
            
            for (loop = 0; loop < f->size; loop++) {
                tempDir[loop] = f->dir[loop];
            }
            
            f->size += fs->dir[loopSrc]->size;

            int loopB = 1;
            for (; loop < f->size; loop++, loopB++) {
                tempDir[loop] = malloc(sizeof(Fs));
                copy(tempDir[loop], f->dir[loopSrc]->dir[loopB]);
                tempDir[loop]->dir[0] = tempDir[loop];
            }
      



            f->dir = tempDir;

        }
    }

    blacnceTree(fs);
}



void FsMv(Fs fs, char *src[], char *dest) {
    // TODO
}