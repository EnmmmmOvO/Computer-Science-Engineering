
#include <stdlib.h>

#include "tree.h"

int TreeSumOdds(Tree t) {
	if (t != NULL) {
		int temp = 0;
		if (t->value % 2 != 0)
			temp = t->value;
		return temp + TreeSumOdds(t->left) + TreeSumOdds(t->right);
	} else {
		return 0;
	}
}
