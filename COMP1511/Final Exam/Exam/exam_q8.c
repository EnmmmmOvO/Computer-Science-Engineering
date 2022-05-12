#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define MAX_WORD_LEN	(51)

struct node {
	long long index;
	char name[MAX_WORD_LEN];
	struct node * next;
};

struct edge {
	int dist;
	char first[MAX_WORD_LEN];
	char second[MAX_WORD_LEN];

	struct edge * next;
};

struct node * find_node(struct node * head, char *name) {
	struct node * cur = head;
	while (cur != NULL) {
		if (strcmp(cur->name, name) == 0) {
			return cur;
		}
		cur = cur->next;
	}
	return NULL;
}

struct node * insert_node(struct node * head, struct node * new) {
	if (head == NULL) {
		return new;
	}
	if (new->index < head->index) {
		new->next = head;
		return new;
	}

	struct node * cur = head;
	struct node * prev = NULL;

	while (cur != NULL && cur->index < new->index) {
		prev = cur;
		cur = cur->next;
	}

	new->next = cur;
	prev->next = new;

	return head;
}

int main(void) {
	int dist;
	char first[MAX_WORD_LEN];
	char second[MAX_WORD_LEN];

	struct node * list = NULL;
	struct edge * edges = NULL;

	// first line;
	scanf("%d %s %s", &dist, first, second);
	struct node * new = malloc(sizeof(struct node));
	new->index = 0;
	strcpy(new->name, first);
	new->next = list;
	list = new;

	new = malloc(sizeof(struct node));
	new->index = dist + list->index;
	strcpy(new->name, second);
	new->next = NULL;
	list->next = new;


	while (scanf("%d %s %s", &dist, first, second) != EOF) {
		struct node * firstNode = find_node(list, first);
		struct node * secondNode = find_node(list, second);

		if (firstNode == NULL && secondNode == NULL) {
			struct edge * edge = malloc(sizeof(struct edge));
			edge->dist = dist;
			strcpy(edge->first, first);
			strcpy(edge->second, second);
			edge->next = edges;
			edges = edge;

		} else if (firstNode == NULL) {
			firstNode = malloc(sizeof(struct node));
			firstNode->index = secondNode->index - dist;
			strcpy(firstNode->name, first);

			list = insert_node(list, firstNode);
		} else if (secondNode == NULL) {
			secondNode = malloc(sizeof(struct node));
			secondNode->index = firstNode->index + dist;
			strcpy(secondNode->name, second);

			list = insert_node(list, secondNode);
		}
	}

	struct edge * curEdge = edges;
	struct edge * prevEdge = NULL;
	while (edges != NULL) {
		curEdge = edges;
		while (curEdge != NULL) {
			struct node * firstNode = find_node(list, curEdge->first);
			struct node * secondNode = find_node(list, curEdge->second);

			if (firstNode == NULL && secondNode == NULL) {
				prevEdge = curEdge;
				curEdge = curEdge->next;
				continue;
			}
			
			if (firstNode == NULL) {
				firstNode = malloc(sizeof(struct node));
				firstNode->index = secondNode->index - dist;
				strcpy(firstNode->name, curEdge->first);

				list = insert_node(list, firstNode);
			} else if (secondNode == NULL) {
				secondNode = malloc(sizeof(struct node));
				secondNode->index = firstNode->index + dist;
				strcpy(secondNode->name, curEdge->second);

				list = insert_node(list, secondNode);
			}

			if (prevEdge == NULL) {
				edges = curEdge->next;
				curEdge = curEdge->next;
			} else {
				prevEdge->next = curEdge->next;
				curEdge = curEdge->next;
			}
		}
	}

	printf("%s", list->name);
	struct node * cur = list->next;
	while (cur != NULL) {
		printf(" %s", cur->name);
		cur = cur->next;
	}
}
