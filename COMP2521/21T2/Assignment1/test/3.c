#include <stdio.h>
#include <stdlib.h>
#include <malloc.h>
#define TRUE 1
#define FLASE 0

typedef struct BTree
{
	int data;
	struct BTree *lchild,*rchild;
}BTree,*Root;

int isAVL(Root root);
int getDepth(Root root);
Root createBTree(int arr[],int len,int i);

int isAVL(Root root)
{
	if (!root)  return TRUE;
        int ldepth = getDepth(root->lchild);
        int rdepth = getDepth(root->rchild);
        int abs_depth = abs(ldepth - rdepth);
        printf("ldepth = %d, rdepth = %d\n", ldepth,rdepth);
        return (abs_depth <= 1) && isAVL(root -> lchild) && isAVL(root->rchild);
}
int getDepth(Root root)
{
	int  ldepth, rdepth;
	if (!root)
		return	0;
	else
	{
		rdepth=getDepth(root->rchild);
		ldepth=getDepth(root->lchild);
		return (rdepth>ldepth)?(rdepth+1):(ldepth+1);
	}
}

Root createBTree(int arr[],int len,int i)
{
	Root root;
	if(i>=len||(arr[i]==0))
		return NULL;
//	printf("i=%d,len=%d,arr[i]=%d\n",i,len,arr[i]);
	root=(Root)malloc(sizeof(BTree));
	root->data=arr[i];
	root->lchild=createBTree(arr,len,2*i);
	root->rchild=createBTree(arr,len,2*i+1);

	return root;
}

int main(void)
{
	int arr[]={0,1,2,3,4,0,0,0};
	//int arr[]={0,1,2,0,4,0,0,0,8};
	//Root root=createBTree(arr,9,1);
	Root root=createBTree(arr,8,1);
//	if(root)		printf("ok\n");
	printf("depth=%d",getDepth(root));
	if(isAVL(root))
		printf("是AVL树\n");
	else
		printf("不是AVL树");
}

int GetHeight(Dict t)
{
    if (t == NULL)
        return -1;
    else
    	return t->height;
}
