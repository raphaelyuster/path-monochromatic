/*
* This program computes the value s(Q) for all tournaments Q of order q where s(Q) is define in the paper "Path-monochromatic bounded depth rooted trees in (random) tournaments"
* Recalling the definition: For a tournament Q on q vertices, for a 2-edge coloring c of it, and for a vertex v, let s(Q,c,v) denote the number of vertices (other than v) that are monochromatically
* dominated by v using paths of length at most 2. Let s(Q, c) be the sum of s(Q, c, v) taken over all vertices and let s(Q) be the minimum of s(Q, c) taken over all colorings.
*
* Recall that our goal is to find some tournament for which s(Q)/q(q-1) > 2/3.
*/

/* Prerequisites:
*
* A file containing the databse of all tournaments on q vertices. This is taken from https://users.cecs.anu.edu.au/~bdm/data/digraphs.html for q <= 9.
*
*/

#include <stdio.h>
#include <math.h>
#include <stdlib.h>

const int q = 9;      // order of tournaments to check.
const int C = 2;      // number of colors; we will only use two colors
const int numTournaments[] = { 1,1,1,2,4,12,56,456,6880,191536 };       // number of tournaments on q vertices for q = 0,...,9.  
const int directedTrainglesFilter = 30;									// to speed up the run, only check tournaments with al least this amount of directed triangles.
																		// To check all tournaments, set value to 0
const int resultFilter = 2 * q * (q - 1) / 3;							// discard tournaments which have a coloring that does not reach as least this result

int tournamentDB[191536][q][q];											// any array containing the adjacency matrices of all tournaments of order q

FILE* datafile;

#define DATAFILE "d:\\research\\general\\combinatorial data\\tour"			// prefix of file name containing the tournament database file

// Load the next tournament from the tournament database file into its adjacency matrix.

void nextTournamentFromFile(int r)
{
	char c;
	for (int i = 0; i < q; i++)
	{
		tournamentDB[r][i][i] = 0;
		for (int j = i + 1; j < q; j++)
		{
			c = fgetc(datafile);
			c == '0' ? tournamentDB[r][i][j] = -1 : tournamentDB[r][i][j] = 1;
			tournamentDB[r][j][i] = -tournamentDB[r][i][j];
		}
	}
	fgetc(datafile);
}

void setTournamentDB() {
	for (int counter = 0; counter < numTournaments[q]; counter++)	// loop on all tournaments in the tournamnt database.
		nextTournamentFromFile(counter);							// read the next tournament from the tournament database file.
}

int directedTrianglesDB[q * (q - 1) * (q - 2) / 6][3];
int directedTrianglesCount;  // this will be equal to the number of directed triangles in the current tournament

// determine all directed triangles on {i,j,k} of the current tournament
int directedTrainaglesDBSet(int r) {
	int pos = 0;
	for (int i = 0; i < q; i++)
		for (int j = i + 1; j < q; j++)
			for (int k = j + 1; k < q; k++)
				if (tournamentDB[r][i][j] > 0 && tournamentDB[r][j][k] > 0 && tournamentDB[r][k][i] > 0 || tournamentDB[r][i][j] < 0 && tournamentDB[r][j][k] < 0 && tournamentDB[r][k][i] < 0) {
					directedTrianglesDB[pos][0] = i;
					directedTrianglesDB[pos][1] = j;
					directedTrianglesDB[pos][2] = k;
					pos++;
				}
	directedTrianglesCount = pos;
	return pos;
}


int reachability[q][q];   // recachabilty [i][j] will be 1 if i can reach j in at most two steps. Otherwise 0.

// compuing s(Q,c) for the current coloring c and the current tournament Q

int countDepth2Reachability(int r) {
	for (int i = 0; i < q; i++)
		for (int j = 0; j < q; j++)
			tournamentDB[r][i][j] > 0 ? reachability[i][j] = 1 : reachability[i][j] = 0;
	for (int pos = 0; pos < directedTrianglesCount; pos++) {
		int i = directedTrianglesDB[pos][0];
		int j = directedTrianglesDB[pos][1];
		int k = directedTrianglesDB[pos][2];
		if (tournamentDB[r][i][j] > 0) {
			if (tournamentDB[r][i][j] == tournamentDB[r][j][k])
				reachability[i][k] = 1;
			if (tournamentDB[r][j][k] == tournamentDB[r][k][i])
				reachability[j][i] = 1;
			if (tournamentDB[r][k][i] == tournamentDB[r][i][j])
				reachability[k][j] = 1;
		}
		else {
			if (tournamentDB[r][j][i] == tournamentDB[r][i][k])
				reachability[j][k] = 1;
			if (tournamentDB[r][i][k] == tournamentDB[r][k][j])
				reachability[i][j] = 1;
			if (tournamentDB[r][k][j] == tournamentDB[r][j][i])
				reachability[k][i] = 1;
		}
	}
	int count = 0;
	for (int i = 0; i < q; i++)
		for (int j = 0; j < q; j++)
			count += reachability[i][j];
	return count; // return the value of s(Q,c) for the current tournament Q
}

//generate the next  edge coloring of the current tournament
//an edge color corresponds to the value in the adjacency matrix. For example, if tournamentDB[r][i][j] = 1 means that in the current tournment, the edge i->j has color 1 and
//tournamentDB[r][i][j] = -2 means that in the current tournment, the edge j->i has color 2.

int nextColor(int r) {
	for (int i = 0; i < q; i++)
		for (int j = i + 1; j < q; j++) {
			if (i + j == 1) // this saves half the runtime as the first examined edge can always be fixed some particular color, say color 1. This may be discarded at the expense of runtime
				continue;
			int currentColor = abs(tournamentDB[r][i][j]);
			if (currentColor < C) {
				if (tournamentDB[r][i][j] > 0)
					tournamentDB[r][i][j]++;
				else
					tournamentDB[r][i][j]--;
				tournamentDB[r][j][i] = -tournamentDB[r][i][j];
				return countDepth2Reachability(r);
			}
			else {
				if (tournamentDB[r][i][j] > 0)
					tournamentDB[r][i][j] = 1;
				else
					tournamentDB[r][i][j] = -1;
				tournamentDB[r][j][i] = -tournamentDB[r][i][j];
			}
		}
	return 0; // no more colorings to check
}

// reurn a lower bound for s(Q)
int checkAllColorings(int r) {
	//long count = 0;
	int minimum = 5000;
	int result;
	while ((result = nextColor(r)) > 0) {
		//count++;
		//if (count % 1000000000 == 0)
		//	printf("%ld\n", count);
		if (result < minimum)
			minimum = result;
		if (result <= resultFilter)
			return result;
	}
	return minimum;
}

void printTournament(int r) {
	for (int i = 0; i < q; i++) {
		for (int j = 0; j < q; j++) {
			if (tournamentDB[r][i][j] > 0)
				printf("$1$");
			else
				printf("$0$");
			if (j < q - 1)
				printf(" & ");
			else
				printf(" \\\\");
		}
		printf("\n");
	}
}

int main() {
	char dataFileName[200];
	sprintf_s(dataFileName, "%s%d.txt", DATAFILE, q);    //suffix the file name according to the value of q.
	printf("Checking %d instances on %d vertices.\n", numTournaments[q], q);
	fopen_s(&datafile, dataFileName, "r");
	setTournamentDB();
	fclose(datafile);

	for (int r = 0; r < numTournaments[q]; r++)  // loop on all tournaments in the tournamnt database.
	{
		if (directedTrainaglesDBSet(r) >= directedTrainglesFilter) {
			printf("Checking tournament %d\n", r);
			int result = checkAllColorings(r);
			printf("Minimum reachability count for tournament is %d\n", result);
			if (result > 2 * q * (q - 1) / 3)
				printTournament(r);
		}
	}
}