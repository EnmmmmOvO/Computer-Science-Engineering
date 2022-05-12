#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define MAX_TAG_NAME 100

struct tag {
    char tag[MAX_TAG_NAME];
    struct tag *next;
};

void print_html(struct tag *head);
struct tag *tags_to_list(int length, char *tags[length]);
void fix_html(struct tag *head);

void insert_closing_tag(struct tag *prev, char *tag);

int main(void) {
    // First test
    char *bad_html[3] = {
        "<p>",
            "<b>",
        "</p>"
    };
    struct tag *head = tags_to_list(3, bad_html);
    printf("Before fix: ");
    print_html(head);

    fix_html(head);

    printf("After fix: ");
    print_html(head);
    printf("\n");

    // Second test
    char *very_bad_html[5] = {
        "<p>", "<i>", "<b>", "<i>", "</p>",
    };
    head = tags_to_list(5, very_bad_html);
    printf("Before fix: ");
    print_html(head);

    fix_html(head);

    printf("After fix: ");
    print_html(head);
    printf("\n");

    // Third test
    char *third_test[] = {
        "<b>", "<i>", "</i>", "<p>", "</b>", "<p>", "<p>", "<p>", "</p>", "</p>"
    };
    head = tags_to_list(5, third_test);
    printf("Before fix: ");
    print_html(head);

    fix_html(head);

    printf("After fix: ");
    print_html(head);
    printf("\n");

    return 0;
}

// Adds closing tags to a linked list of html tags.
void fix_html(struct tag *head) {
	char stack[100][MAX_TAG_NAME];
	int top = -1;

	char tag[MAX_TAG_NAME];

	struct tag * cur = head;
	struct tag * prev = NULL;
	while (cur != NULL) {
		if (cur->tag[1] != '/') {
			int tagLen = strlen(cur->tag);
			strncpy(stack[++top], cur->tag + 1, tagLen - 2);
			stack[top][tagLen - 2] = '\0';
			prev = cur;
			cur = cur->next;
		} else {
			int tagLen = strlen(cur->tag);
			strncpy(tag, cur->tag + 2, tagLen - 3);
			tag[tagLen - 3] = '\0';
			if (strcmp(stack[top], tag) == 0) {
				top--;
				prev = cur;
				cur = cur->next;
			} else {
				while (top >= 0 && strcmp(stack[top], tag) != 0) {
					insert_closing_tag(prev, stack[top]);
					prev = prev->next;
					top--;
				}
				prev = cur;
				cur = cur->next;
				top--;
			}
		}
	}

	while (top >= 0) {
		insert_closing_tag(prev, stack[top]);
		prev = prev->next;
		top--;
	}
}

void insert_closing_tag(struct tag * prev, char * tag) {
	struct tag * closingTag = malloc(sizeof(struct tag));
	closingTag->tag[0] = '<';
	closingTag->tag[1] = '/';
	strncpy(closingTag->tag + 2, tag, strlen(tag));
	closingTag->tag[strlen(tag) + 2] = '>';
	closingTag->tag[strlen(tag) + 3] = '\0';

	closingTag->next = prev->next;
	prev->next = closingTag;
}

struct tag *tags_to_list(int length, char *tags[length]) {
	int i = length - 1;
    struct tag *head = NULL;
    while (i >= 0) {
        struct tag *new = malloc(sizeof(struct tag));
        new->next = head;
        strcpy(new->tag, tags[i]);
        head = new;
        i--;
    }
    return head;
}

void print_html(struct tag *head) {
    struct tag *curr = head;
    while (curr != NULL) {
        printf("%s", curr->tag);
        curr = curr->next;
    }
    printf("\n");
}
