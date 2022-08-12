//
// Created by Jinghan Wang z5286124 on 8/6/2022.
//
#include <comp6771/ladder.hpp>

auto ladder::create_newVertex(std::string word, int diffWithEndWord, int index) -> Vertex {
	Vertex v;
	v.index = index;
	v.diffWithEndWord = diffWithEndWord;
	v.word = word;
	v.last = -1;
	v.known = false;
	return v;
}

auto ladder::get_char_diff(std::string word1, std::string word2) -> int {
	int totalDiff = 0;
	for (int loop = 0; loop < word1.length(); loop++)
		if (word1[loop] != word2[loop])
			totalDiff++;
	return totalDiff;
}

auto ladder::create_newLexicon(std::unordered_set<std::string> const& lexicon,
                               int length,
                               std::string const& from,
                               std::string const& to) -> std::vector<Vertex> {
	// Create a new Vector which the word is equal start and end's word length and
	// record the difference between the word and the end
	std::vector<Vertex> newLexicon;
	for (auto word : lexicon) {
		if (word.length() == length)
			newLexicon.push_back(create_newVertex(word, get_char_diff(word, to), newLexicon.size()));
	}

	bool checkStart = true;
	bool checkEnd = true;
	// Record all word which has one character different into adjacent
	for (int i = 0; i < newLexicon.size(); i++) {
		// Find the position of from and to word in the new Vector
		if (checkStart && newLexicon[i].word == from) {
			startPosition = i;
			checkStart = false;
		}
		if (checkEnd && newLexicon[i].word == to) {
			endPosition = i;
			checkEnd = false;
		}

		for (int j = i + 1; j < newLexicon.size(); j++) {
			if (get_char_diff(newLexicon[i].word, newLexicon[j].word) == 1) {
				// In order of the same number of differences
				if (newLexicon[i].adjacent.find(newLexicon[j].diffWithEndWord)
				    == newLexicon[i].adjacent.cend()) {
					newLexicon[i].adjacent.insert({newLexicon[j].diffWithEndWord, std::vector{j}});
				}
				else {
					newLexicon[i].adjacent.at(newLexicon[j].diffWithEndWord).push_back(j);
				}

				if (newLexicon[j].adjacent.find(newLexicon[i].diffWithEndWord)
				    == newLexicon[j].adjacent.cend()) {
					newLexicon[j].adjacent.insert({newLexicon[i].diffWithEndWord, std::vector{i}});
				}
				else {
					newLexicon[j].adjacent.at(newLexicon[i].diffWithEndWord).push_back(i);
				}
			}
		}
	}

	// If checkStart and checkEnd is true, it means the lexicon is not included the word
	if (checkEnd || checkStart)
		check = false;
	return newLexicon;
}

auto ladder::find(int pos, int n, std::vector<Vertex>& newLexicon) -> void {
	// Go to every adjacent element
	// If (the position == the end position) goto record the passing
	// If (the Vertex not passed && the depth is not larger than the shortest depth)
	//     record this word in next word last place and sign is known
	//     after visited the word, sign the word is unknown
	for (auto pair : newLexicon[pos].adjacent) {
		for (auto key : pair.second) {
			if (key == endPosition) {
				newLexicon[key].last = pos;
				record_result(n, newLexicon);
				break;
			}
			else if (n + 1 <= shortest && !newLexicon[key].known) {
				newLexicon[key].known = true;
				newLexicon[key].last = pos;
				find(key, n + 1, newLexicon);
				newLexicon[key].known = false;
			}
		}
	}
}

auto ladder::record_result(int n, std::vector<Vertex> const& newLexicon) -> void {
	// From the end word, record the word and visit last word, until reach the front word
	std::vector<std::string> process;
	for (int temp = endPosition; temp != startPosition; temp = newLexicon[temp].last)
		process.push_back(newLexicon[temp].word);
	process.push_back(newLexicon[startPosition].word);
	std::reverse(process.begin(), process.end());

	// if the depth is equal than the shortest depth, record it
	// if is less than, clear the last record and change the shortest depth
	if (n == shortest) {
		result.push_back(process);
	}
	else if (n < shortest) {
		shortest = n;
		result.clear();
		result.push_back(process);
	}
}

auto ladder::start() -> std::vector<std::vector<std::string>> {
	if (!check)
		return {};
	find(startPosition, 0, newLexicon);
	std::sort(result.begin(), result.end());
	return result;
}
