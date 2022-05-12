// Command-line interface to the File System ADT

#define _GNU_SOURCE

#include <ctype.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "Fs.h"

#define BLUE        "\033[94m"
#define GREEN       "\033[32m"
#define RESET_COLOR "\033[00m"

#define CLEAR_SCREEN_ANSI "\e[1;1H\e[2J"

static void showHelp(void);
static void showCmdHelp(void);

static void processOptions(int argc, char *argv[]);
static void showWelcomeMessage(void);
static void showUsage(char *progName);

static char *readCommand(Fs fs);
static char **tokenise(char *s, int *ntokens);
static void chomp(char *s);

////////////////////////////////////////////////////////////////////////

typedef struct command Command;
struct command {
    char  *name;
    void (*fn)(Fs, int, char **); // function that executes the command
    char  *argHint;
    char  *helpMsg;
};

static void runMkdir(Fs fs, int argc, char **argv);
static void runMkfile(Fs fs, int argc, char **argv);
static void runCd(Fs fs, int argc, char **argv);
static void runLs(Fs fs, int argc, char **argv);
static void runPwd(Fs fs, int argc, char **argv);
static void runTree(Fs fs, int argc, char **argv);
static void runPut(Fs fs, int argc, char **argv);
static void runCat(Fs fs, int argc, char **argv);
static void runDldir(Fs fs, int argc, char **argv);
static void runDl(Fs fs, int argc, char **argv);
static void runCp(Fs fs, int argc, char **argv);
static void runMv(Fs fs, int argc, char **argv);

#define NUM_COMMANDS 15
static Command COMMANDS[NUM_COMMANDS] = {
    {
        .name    = "mkdir",
        .fn      = runMkdir,
        .argHint = "<path>",
        .helpMsg = "create a new directory"
    },
    {
        .name    = "mkfile",
        .fn      = runMkfile,
        .argHint = "<path>",
        .helpMsg = "create a new regular file"
    },
    {
        .name    = "cd",
        .fn      = runCd,
        .argHint = "[path]",
        .helpMsg = "change working directory"
    },
    {
        .name    = "ls",
        .fn      = runLs,
        .argHint = "[path]",
        .helpMsg = "list files"
    },
    {
        .name    = "pwd",
        .fn      = runPwd,
        .argHint = "",
        .helpMsg = "print working directory"
    },
    {
        .name    = "tree",
        .fn      = runTree,
        .argHint = "[path]",
        .helpMsg = "print the contents of a directory in a tree-like format"
    },
    {
        .name    = "put",
        .fn      = runPut,
        .argHint = "<path> <word>",
        .helpMsg = "set the content of a file"
    },
    {
        .name    = "cat",
        .fn      = runCat,
        .argHint = "<path>",
        .helpMsg = "print the content of a file"
    },
    {
        .name    = "dldir",
        .fn      = runDldir,
        .argHint = "<path>",
        .helpMsg = "delete an empty directory"
    },
    {
        .name    = "dl",
        .fn      = runDl,
        .argHint = "[-r] <path>",
        .helpMsg = "delete a file (-r for recursive)"
    },
    {
        .name    = "cp",
        .fn      = runCp,
        .argHint = "[-r] <source>... <dest>",
        .helpMsg = "copy files (-r for recursive)"
    },
    {
        .name    = "mv",
        .fn      = runMv,
        .argHint = "<source>... <dest>",
        .helpMsg = "move files"
    },

    // Meta-commands
    {
        .name    = "help",
        .fn      = NULL,
        .argHint = "",
        .helpMsg = "display information about commands"
    },
    {
        .name    = "clear",
        .fn      = NULL,
        .argHint = "",
        .helpMsg = "clear the screen"
    },
    {
        .name    = "exit",
        .fn      = NULL,
        .argHint = "",
        .helpMsg = "exit the file system"
    },
};

////////////////////////////////////////////////////////////////////////

bool ECHO = false;
bool QUIET = false;
Command *currCommand = NULL;

int main(int argc, char *argv[]) {
    processOptions(argc, argv);
    showWelcomeMessage();

    Fs fs = FsNew();
    bool done = false;
    char *cmd;

    while (!done && (cmd = readCommand(fs)) != NULL) {
        if (ECHO) {
            printf("%s\n", cmd);
        }

        int ntokens = 0;
        char **tokens = tokenise(cmd, &ntokens);
        if (ntokens == 0) {
            free(tokens);
            free(cmd);
            continue;
        }

        char *cmdname = tokens[0];

        // Meta-commands
        if (strcmp(cmdname, "help") == 0) {
            showHelp();
        } else if (strcmp(cmdname, "clear") == 0) {
            printf("%s", CLEAR_SCREEN_ANSI);
        } else if (strcmp(cmdname, "exit") == 0) {
            done = true;
        
        // Actual commands
        } else {
            bool validCmdName = false;
            for (int i = 0; i < NUM_COMMANDS; i++) {
                if (strcmp(cmdname, COMMANDS[i].name) == 0) {
                    validCmdName = true;
                    currCommand = &COMMANDS[i];
                    COMMANDS[i].fn(fs, ntokens, tokens);
                    break;
                }
            }

            if (!validCmdName) {
                printf("%s: command not found\n", cmdname);
            }
        }

        free(tokens);
        free(cmd);
    }

    printf("\n");
    FsFree(fs);
}

////////////////////////////////////////////////////////////////////////

static void runMkdir(Fs fs, int argc, char **argv) {
    if (argc != 2) {
        showCmdHelp();
        return;
    }

    FsMkdir(fs, argv[1]);
}

static void runMkfile(Fs fs, int argc, char **argv) {
    if (argc != 2) {
        showCmdHelp();
        return;
    }

    FsMkfile(fs, argv[1]);
}

static void runCd(Fs fs, int argc, char **argv) {
    if (argc > 2) {
        showCmdHelp();
        return;
    }

    FsCd(fs, argc == 2 ? argv[1] : NULL);
}

static void runLs(Fs fs, int argc, char **argv) {
    if (argc > 2) {
        showCmdHelp();
        return;
    }

    FsLs(fs, argc == 2 ? argv[1] : NULL);
}

static void runPwd(Fs fs, int argc, char **argv) {
    if (argc != 1) {
        showCmdHelp();
        return;
    }

    FsPwd(fs);
}

static void runTree(Fs fs, int argc, char **argv) {
    if (argc > 2) {
        showCmdHelp();
        return;
    }
    
    FsTree(fs, argc == 2 ? argv[1] : NULL);
}

static void runPut(Fs fs, int argc, char **argv) {
    if (argc != 3) {
        showCmdHelp();
        return;
    }

    if (!QUIET) {
        printf("Enter the text content you want to put in '%s' "
               "and then enter a line containing just '%s'\n",
               argv[1], argv[2]);
    }

    char *end = malloc((strlen(argv[2]) + 2) * sizeof(char));
    if (end == NULL) {
        fprintf(stderr, "error: out of memory\n");
        exit(EXIT_FAILURE);
    }
    strcpy(end, argv[2]);
    strcat(end, "\n");

    size_t len = 0;
    size_t cap = 64;
    char *content = malloc((cap + 1) * sizeof(char));
    if (content == NULL) {
        fprintf(stderr, "error: out of memory\n");
        exit(EXIT_FAILURE);
    }
    content[0] = '\0';

    char *line = NULL;
    size_t n = 0;
    ssize_t size;
    while ((size = getline(&line, &n, stdin)) != -1) {
        if (strcmp(end, line) == 0) {
            break;
        }

        if (len + size > cap) {
            while (len + size > cap) {
                cap *= 2;
            }
            content = realloc(content, (cap + 1) * sizeof(char));
            if (content == NULL) {
                fprintf(stderr, "error: out of memory\n");
                exit(EXIT_FAILURE);
            }
        }

        strcat(content, line);
        len += size;

        free(line);
        line = NULL;
        n = 0;
    }

    free(line);
    FsPut(fs, argv[1], content);
    free(content);
    free(end);
}

static void runCat(Fs fs, int argc, char **argv) {
    if (argc != 2) {
        showCmdHelp();
        return;
    }

    FsCat(fs, argv[1]);
}

static void runDldir(Fs fs, int argc, char **argv) {
    if (argc != 2) {
        showCmdHelp();
        return;
    }

    FsDldir(fs, argv[1]);
}

static void runDl(Fs fs, int argc, char **argv) {
    if (argc > 3 || (argc == 3 && strcmp(argv[1], "-r") != 0) ||
            (argc == 2 && strcmp(argv[1], "-r") == 0)) {
        showCmdHelp();
        return;
    }

    bool recursive = false;
    char *path;
    if (argc == 3) {
        recursive = true;
        path = argv[2];
    } else {
        path = argv[1];
    }

    FsDl(fs, recursive, path);
}

static void runCp(Fs fs, int argc, char **argv) {
    if (argc < 3 || (argc == 3 && strcmp(argv[1], "-r") == 0)) {
        showCmdHelp();
        return;
    }

    bool recursive = false;
    int i = 1;
    if (strcmp(argv[1], "-r") == 0) {
        recursive = true;
        i++;
    }
    char *dest = argv[argc - 1];
    argv[argc - 1] = NULL;
    FsCp(fs, recursive, &argv[i], dest);
}

static void runMv(Fs fs, int argc, char **argv) {
    if (argc < 3) {
        showCmdHelp();
        return;
    }

    char *dest = argv[argc - 1];
    argv[argc - 1] = NULL;
    FsMv(fs, &argv[1], dest);
}

////////////////////////////////////////////////////////////////////////

static void showHelp(void) {
    printf("Commands:\n");
    for (int i = 0; i < NUM_COMMANDS; i++) {
        char str[32];
        sprintf(str, "%s %s", COMMANDS[i].name, COMMANDS[i].argHint);
        printf("%-30s %s\n", str, COMMANDS[i].helpMsg);
    }
    printf("\n");
}

static void showCmdHelp(void) {
    printf("Usage: %s %s\n", currCommand->name, currCommand->argHint);
}

////////////////////////////////////////////////////////////////////////

static void processOptions(int argc, char *argv[]) {
    for (int i = 1; i < argc; i++) {
        if (strcmp(argv[i], "-e") == 0) {
            ECHO = true;
        } else if (strcmp(argv[i], "-h") == 0) {
            showUsage(argv[0]);
            exit(EXIT_SUCCESS);
        } else if (strcmp(argv[i], "-q") == 0) {
            QUIET = true;
        }
    }
}

static void showWelcomeMessage(void) {
    if (!QUIET) {
        printf("mimFs - My In-Memory File System\n");
        printf("Enter 'help' to see the list of commands.\n");
    }
}

static void showUsage(char *progName) {
    printf(
        "Usage: %s [options]...\n"
        "Options:\n"
        "    -e      echo all commands\n"
        "    -h      show this help message\n"
        "    -q      don't display welcome or hint messages\n",
        progName
    );
}

static char *readCommand(Fs fs) {
    char cwd[PATH_MAX] = {0};
    FsGetCwd(fs, cwd);
    printf("%smimFs:%s%s%s$ ", GREEN, BLUE, cwd, RESET_COLOR);

    char *cmd = NULL;
    size_t n = 0;
    ssize_t size = getline(&cmd, &n, stdin);

    if (size == -1) {
        free(cmd);
        cmd = NULL;
    } else {
        chomp(cmd);
    }

    return cmd;
}

static char **tokenise(char *s, int *ntokens) {
    char p;

    // count number of tokens
    *ntokens = 0;
    p = ' ';
    for (char *c = s; *c != '\0'; p = *c, c++) {
        if (isspace(p) && !isspace(*c)) {
            (*ntokens)++;
        }
    }

    char **tokens = malloc((*ntokens + 1) * sizeof(char *));
    int i = 0;
    p = ' ';
    for (char *c = s; *c != '\0'; p = *c, c++) {
        if ((p == '\0' || isspace(p)) && !isspace(*c)) {
            tokens[i++] = c;
        } else if (!isspace(p) && isspace(*c)) {
            *c = '\0';
        }
    }
    tokens[i] = NULL;

    return tokens;
}

static void chomp(char *s) {
    int len = strlen(s);
    if (len > 0 && s[len - 1] == '\n') {
        s[len - 1] = '\0';
    }
}

