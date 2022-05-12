
#include <stdlib.h>

#include "tree.h"

int TreeSumOdds(Tree t) {
	if (t == NULL) return 0;
	return TreeSumOdds(t->left) + TreeSumOdds(t->right) + (t->value % 2 == 0 ? 0 : t->value);
}

