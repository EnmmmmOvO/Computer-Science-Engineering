//
// Created by Jinghan Wang on 8/6/2022.
//

#ifndef COMP6771_ASS1_LADDER_HPP
#define COMP6771_ASS1_LADDER_HPP

#include <unordered_set>
#include <algorithm>
#include <map>
#include <string>
#include <vector>

// When create the class, it needs the origin english_lexicon , from and to word.
// function (create_newLexicon)
// First, create a vector and record all lexicon words with the same length of
// start word, and compare the number of characters that differ from the end word.
// Then compare the words in each newLexicon with each other. If the difference is
// one character, it is recorded in adjacent. Put the same number of difference with
// end word into a vector, and map the number of characters that differ from end word
// into the target vector.
// function (find)
// first, start with start word, first sort the keys of adjacent and find the vector
// that is less different with end word.
// Check the status of adjacent vertices in the vector:
// 	if the depth of the next depth is greater than the existing minimum number, or the vertices
// 	have been known, skip;
//		If it is the same as end word, record the experienced vertex;
// 	If else, mark the next vertex known, then record the current index in the last of the next
//    vertex, and then go to the next layer.
//    After the next vertex is completed, mark it with unknown to find other suitable ones
class ladder {
private:
	struct Vertex {
		// The Node in the newLexicon's position
		int index;

		// Record all word with the one character diff
		// map <int(Record the number of different With End Word), std::vector<int>(Record all word
		// with the one character diff and has same different with end word)>
		std::map<int, std::vector<int>> adjacent;
		std::string word;

		// Record the number of difference with the end word;
		// i.e. this : work,  end : play, diffWithEndWord : 4;
		//      this : plan,  end : play, diffWithEndWord : 1;
		int diffWithEndWord;

		// Record the word point to this vertex
		int last;

		// Record the word is used or not
		bool known;
	};

	int startPosition = 0;
	int endPosition = 0;
	std::vector<std::vector<std::string>> result;
	int shortest;
	bool check = false;
	std::vector<Vertex> newLexicon;
	std::vector<std::string> tempstring;

	auto create_newVertex(std::string word, int diffWithEndWord, int index) -> Vertex;
	auto get_char_diff(std::string word1, std::string word2) -> int;
	auto create_newLexicon(std::unordered_set<std::string> const& lexicon,
	                       int length,
	                       std::string const& from,
	                       std::string const& to) -> std::vector<Vertex>;
	auto find(int pos, int n, std::vector<Vertex>& newLexicon) -> void;
	auto record_result(int n, std::vector<Vertex> const& newLexicon) -> void;

public:
	ladder(std::string const& from,
	       std::string const& to,
	       std::unordered_set<std::string> const& lexicon) {
		if (from.length() == to.length()) {
			check = true;
			newLexicon = create_newLexicon(lexicon, from.length(), from, to);
		}
	}

	auto start() -> std::vector<std::vector<std::string>>;
};

#endif // COMP6771_ASS1_LADDER_HPP
