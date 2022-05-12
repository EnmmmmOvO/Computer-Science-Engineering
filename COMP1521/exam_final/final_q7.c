// COMP1521 21T2 ... final exam, question 7

#include <sys/types.h>
#include <sys/stat.h>

#include <dirent.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

const mode_t NEW_DIR_MODE = S_IRWXU | S_IRWXG | S_IROTH | S_IXOTH;

void
cp_directory (char *dir_from, char *dir_to)
{
	int sfd,tfd;
	struct stat s,t;
	char c;
	sfd = open(dir_from,O_RDONLY);
	tfd = open(dir_to,O_RDWR|O_CREAT);
	while(read(sfd,&c,1)>0)
		write(tfd,&c,1);
	fstat(sfd,&s);
	chown(dir_to,s.st_uid,s.st_gid);
	chmod(dir_to,s.st_mode);

	close(sfd);
	close(tfd);
}
