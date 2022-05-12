/*******************************************************************************
> CSpotify - 20T3 COMP1511 Assignment 2
| cspotify.c
|
| zID: z5286124
| Name: Jinghan Wang
| Date: 18-11-2020
| Program Description:
| COMP1511
|
| Version 1.0.0: Assignment released.
|
 *******************************************************************************/

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

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
	int selected;
	int size;
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
Playlist newPlaylist(char name[MAX_LEN], int selected);
int checkValidStrings(char string[MAX_LEN]);
Playlist searchPlaylist(Library library, char target[MAX_LEN]);

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
int add_playlist(Library library, char playlistName[MAX_LEN]);

// Print out the Library.
void print_library(Library library) {
	Playlist curr_p = library->head;
	int i = 0;
	while (curr_p != NULL) 
	{
		if (curr_p->selected == 1) 
		{
			print_selected_playlist(i, curr_p->name);
		} else 
		{
		print_playlist(i, curr_p->name);
		}
		i ++;
	}
	Track curr_track = curr_p->tracks;
	while(curr_track != NULL) {
		print_track(curr_track->title, curr_track->artist, 
curr_track->length.minutes, curr_track->length.seconds);
	curr_track = curr_track->next;
	}
	curr_p = curr_p->next;
}


// Rename the name of an existing Playlist.
int rename_playlist(Library library, char playlistName[MAX_LEN], 
char newPlaylistName[MAX_LEN]) {
	if (checkValidStrings(newPlaylistName) == 0) 
	{
		return ERROR_INVALID_INPUTS;
	}
	Playlist rename_p = searchPlaylist(library, playlistName);
	if (rename_p == NULL) 
	{
		return ERROR_NOT_FOUND;
	}
	strcpy(rename_p->name, newPlaylistName);
    return SUCCESS;
}


/*********
> STAGE 2
*********/

// Selects the next Playlist in the Library.
void select_next_playlist(Library library) 
{
	if (library->head == NULL) 
	{
		return;
	}
	Playlist curr_p = library->head;
	Playlist new_selected = NULL;
	while(curr_p != NULL) 
	{
		if (curr_p->selected == 1 && curr_p->next == NULL) {
			curr_p->selected = 0;
			library->head->selected = 1;
		} else if(curr_p->selected == 1 && curr_p->next != NULL) {
			curr_p->selected = 0;
			new_selected = curr_p->next;
		}
		curr_p = curr_p->next;
	}
	if (new_selected != NULL) 
	{
		new_selected->selected = 1;
	} 
}

// Selects the previous Playlist in the Library.
void select_previous_playlist(Library library) {
	if (library->head == NULL) 
	{
		return;
	}
	Playlist curr_p = library->head;
	Playlist prev_p = NULL;
	if (curr_p->selected == 1) 
	{
		curr_p->selected = 0;
		while (curr_p != NULL) 
		{
			prev_p = curr_p;
			curr_p = curr_p->next;
		}
		prev_p->selected = 1;
	} else 
	{
		while(curr_p != NULL) 
		{
			if (curr_p->selected == 1) 
			{
				curr_p->selected = 0;
				prev_p->selected = 1;
			}
			prev_p = curr_p;
			curr_p = curr_p->next;
		}
	}   
}

// Add a new Track to the selected Playlist.
int add_track(Library library, char title[MAX_LEN], char artist[MAX_LEN], 
    int trackLengthInSec, int position) {
    return SUCCESS;
}

// Calculate the total length of the selected Playlist in minutes and seconds.
void playlist_length(Library library, int *playlistMinutes, 
int *playlistSeconds) 
{
	if (library->head == NULL) {
		return ERROR_NOT_FOUND;
	}
	Playlist curr_p = library->head;
	Playlist selected_p = NULL;
	while(curr_p != NULL) 
	{
		if (curr_p->selected == 1) 
		{
			selected_p = curr_p;
		}
		curr_p = curr_p->next;
	}

	if (checkValidStrings(title) == 0)
	{
		return ERROR_INVALID_INPUTS;
	} else if (checkValidStrings(artist) == 0)
	{
		return ERROR_INVALID_INPUTS;
	} else if (trackLengthInSec <= 0)
	{
		return ERROR_INVALID_INPUTS;
	} else if (position < 0)
	{
		return ERROR_INVALID_INPUTS;
	} else if(position > selected_p->size) 
	{
		return ERROR_INVALID_INPUTS;
	}

	Track new_track = malloc(sizeof(struct track));
	strcpy(new_track->title, title);
	strcpy(new_track->artist, artist);
	new_track->length.minutes = trackLengthInSec / 60;
	new_track->length.seconds = trackLengthInSec % 60;
	new_track->next = NULL;

// Inserting at the front of the Playlist.
	Track curr_t = selected_p->tracks;
	if (position == 0) {
		new_track->next = selected_p->tracks;
		selected_p->tracks = new_track;
	} else if (position == selected_p->size) 
	{
		if (selected_p->size == 0) {
		selected_p->tracks = new_track;
		} else 
		{
			while (curr_t->next != NULL) 
			{
				curr_t = curr_t->next;
			}
			curr_t->next = new_track;
		}
	} else 
	{
		int i = 0;
		while (i < position-1) 
		{
			curr_t = curr_t->next;
			i ++;
		}
		new_track->next = curr_t->next;
		curr_t->next = new_track;
	}
	selected_p->size++;
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






int add_playlist(Library library, char playlistName[MAX_LEN]) {
	if(checkValidStrings(playlistName) == 0)
	{
		return ERROR_INVALID_INPUTS;
	}
	if(library->head == NULL)
	{
		Playlist new_p = newPlaylistName(playlistName, 1);
		library->head = new_p;
	} else if (library->head != NULL)
	{
		Playlist new_p = newPlaylist(playlistName, 0);
		Playlist curr_p = library->head;
		while(curr_p->next != NULL) 
		{
			curr_p = curr_p->next;
		}
		curr_p->next = new_p;
	}
	return SUCCESS;



int checkValidStrings(char string[MAX_LEN]) {
	int i = 0;
	while (string[i] != '\0' && string[i] != '\n') 
	{
		if (! ((string[i] >= 'A' && string[i] <= 'Z') 
|| (string[i] >= 'a' && string[i] <= 'z')
|| (string[i] >= '0' && string[i] <= '9'))) 
		{
			return 0;
		}
		i ++;
	}
	return 1;
}

Playlist searchPlaylist(Library library, char target[MAX_LEN]) {
	Playlist curr_p = library->head;
	while(curr_p != NULL) 
	{
		if (strcmp(target, curr_p->name) == 0)
		{
			return curr_p;
		}
		curr_p = curr_p->next;
	}
	return NULL;
}
