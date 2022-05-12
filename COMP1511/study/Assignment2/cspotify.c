/*******************************************************************************
> CSpotify - 20T3 COMP1511 Assignment 2
| cspotify.c
|
| zID: <YOUR-ZID-HERE>
| Name: <YOUR-NAME-HERE>
| Date: <DATE-HERE>
| Program Description:
| <INSERT DESCRIPTION>
|
| Version 1.0.0: Assignment released.
|
 *******************************************************************************/

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <ctype.h>

#include "cspotify.h"

/******************************************************************************/
// TODO: Add any other #defines you need.

/******************************************************************************/
// 'struct library' represents a library, which represents the state of the
// entire program. It is mainly used to point to a linked list of 
// playlists, though you may want to add other fields to it.
//
// You may choose to add or change fields in this struct.
struct library {
    struct playlist *head;
};

// 'struct playlist' represents a playlist. 
// You may choose to add or change fields in this struct.
struct playlist {
    char name[MAX_LEN];
    struct track *tracks;
    struct playlist *next;
};

// 'struct trackLength' represents the length of a track. 
// You may choose to add or change fields in this struct.
struct trackLength {
    int minutes;
    int seconds;
};

// 'struct track' represents a track. 
// You may choose to add or change fields in this struct.
struct track {
    char title[MAX_LEN];
    char artist[MAX_LEN];
    struct trackLength length;
    struct track *next;
};

/******************************************************************************/
// TODO: Add any other structs you define here.


/******************************************************************************/
// TODO: Add prototypes for any extra functions you create here.

// Function prototypes for helper functions. 
static void print_playlist(int number, char playlistName[MAX_LEN]);
static void print_selected_playlist(int number, char playlistName[MAX_LEN]);
static void print_track(char title[MAX_LEN], char artist[MAX_LEN], int minutes, int seconds);

/******************************************************************************/
// You need to implement the following functions.
// In other words, write code to make the function work as described 
// in cspotify.h

/*********
> STAGE 1
*********/

// Create a new Library and return a pointer to it.
Library create_library(void) {
    Library newLibrary = malloc(sizeof(struct library));
    newLibrary->head = NULL;
    return newLibrary;
}

// Add a new Playlist to the Library.
int add_playlist(Library library, char playlistName[MAX_LEN]) {
    for (int loopA = 0; playlistName[loopA] != '\0'; loopA ++) 
        if (!isalnum(playlistName[loopA])) 
            return ERROR_INVALID_INPUTS; 

    struct playlist *p = malloc(sizeof(struct playlist));
    for (int loopA = 0; playlistName[loopA] != '\0'; loopA ++)
        p->name[loopA] = playlistName[loopA];
    p->tracks = NULL;
    p->next = NULL;

    if (library == NULL) {
        library->head = p;
    } else {
        library->head->next = p;
    }    
    return SUCCESS;
}

// Print out the Library.
void print_library(Library library) {
    int num;
    struct playlist *p = library->head;
    for (num = 0; p != NULL; p = p->next, num ++);
    p = library->head;
    int loopB;
    for (loopB = 1; loopB <= num; loopB ++, p = p->next)
        print_playlist(loopB, p->name);
}

// Rename the name of an existing Playlist.
int rename_playlist(Library library, char playlistName[MAX_LEN], char newPlaylistName[MAX_LEN]) {
    //if the given Playlist name is not found otherwise
    struct playlist *p;
    int loopC = 0;
    for (p = library->head; p != NULL; p = p->next) {
        if (p->name == playlistName)
            loopC = 1;
    }
    if (loopC != 1)
        return ERROR_NOT_FOUND;

    //if the new Playlist name is invalid
    for (int loopD = 0; newPlaylistName[loopD] != '\0'; loopD ++) 
        if (!isalnum(newPlaylistName[loopD])) 
            return ERROR_INVALID_INPUTS; 

    for (p = library->head; p->name != playlistName; p = p->next);
    for (int loopD = 0; playlistName[loopD] != '\0'; loopD ++)
        p->name[loopD] = newPlaylistName[loopD];
    return SUCCESS;
}


/*********
> STAGE 2
*********/

// Selects the next Playlist in the Library.
void select_next_playlist(Library library) {
    
}

// Selects the previous Playlist in the Library.
void select_previous_playlist(Library library) {
    
}

// Add a new Track to the selected Playlist.
int add_track(Library library, char title[MAX_LEN], char artist[MAX_LEN], 
    int trackLengthInSec, int position) {
    return SUCCESS;
}

// Calculate the total length of the selected Playlist in minutes and seconds.
void playlist_length(Library library, int *playlistMinutes, int *playlistSeconds) {

}


/*********
> STAGE 3
*********/

// Delete the first instance of the given track in the selected Playlist
// of the Library.
void delete_track(Library library, char track[MAX_LEN]) {

}

// Delete the selected Playlist and select the next Playlist in the Library.
void delete_playlist(Library library) {

}

// Delete an entire Library and its associated Playlists and Tracks.
void delete_library(Library library) {

}


/*********
> STAGE 4
*********/

// Cut the given track in selected Playlist and paste it into the given 
// destination Playlist.
int cut_and_paste_track(Library library, char trackTitle[MAX_LEN], 
    char destPlaylist[MAX_LEN]) {
    return SUCCESS;
}

// Print out all Tracks with artists that have the same Soundex Encoding 
// as the given artist.
void soundex_search(Library library, char artist[MAX_LEN]) {

}


/*********
> STAGE 5
*********/

// Move all Tracks matching the Soundex encoding of the given artist 
// to a new Playlist.
int add_filtered_playlist(Library library, char artist[MAX_LEN]) {
    return SUCCESS;
}

// Reorder the selected Playlist in the given order specified by the order array.
void reorder_playlist(Library library, int order[MAX_LEN], int length) {

}


/*****************
> Helper Functions
*****************/

static void print_playlist(int number, char playlistName[MAX_LEN]) {
    printf("[ ] %d. %s\n", number, playlistName);
}

static void print_selected_playlist(int number, char playlistName[MAX_LEN]) {
    printf("[*] %d. %s\n", number, playlistName);
}

static void print_track(char title[MAX_LEN], char artist[MAX_LEN], int minutes, int seconds) {
    printf("       - %-32s    %-24s    %02d:%02d\n", title, artist, 
        minutes, seconds);
}
