from copy import deepcopy
import os
import re

range_re = re.compile('\d+(?:\.\d+)?\.\.\d+(?:\.\d+)?')

def get_input_file_name():
	input_file_name = input('Enter input file name: ')
	while input_file_name == '' or not os.path.exists(input_file_name):
		print('Error: invalid file name')
		input_file_name = input('Enter input file name: ')
	return input_file_name

def parse_lers_file(lers_file_name):
	"""Reads LERS file, removes comments, returns attributes, decision, dataset"""

	# Read file
	contents = open(lers_file_name).read().splitlines()

	# Remove comments
	for line in contents:
		for i, char in enumerate(line):
			if char == '!':
				line = line[:i]
	contents = [i for i in contents if i]

	# Parse LERS file
	dataset = []
	attributes = contents[1][1:-2].split()
	for line in contents[2:]:
		row = {}
		values = line.split()
		for attribute, value in zip(attributes, values):
			row[attribute] = value
		dataset.append(row)

	return attributes[:-1], attributes[-1], dataset

def get_concepts(dataset, decision):
	"""Returns a list of all concepts, i.e. cases corresponding to each possible decision value, and the concept names"""
	decision_values_set = set()
	decision_values = []

	# Get unique decision values
	for row in dataset:
		if row[decision] not in decision_values_set:
			decision_values.append(row[decision])
			decision_values_set.add(row[decision])

	concepts = [[] for _ in range(len(decision_values))]

	# Get cases corresponding to each decision value
	for i, decision_value in enumerate(decision_values):
		for j, row in enumerate(dataset):
			if row[decision] == decision_value:
				concepts[i].append(j + 1)
	
	return concepts, decision_values

def get_attribute_value_pairs(attributes, dataset):
	"""Returns sets of all possible values for all attributes (a,v)"""
	attribute_value_pairs = []
	for attribute in attributes:
		possible_values = set()
		for row in dataset:
			value = row[attribute]
			if value not in possible_values:
				possible_values.add(value)
				attribute_value_pairs.append((attribute, value))
	return attribute_value_pairs

def get_set_av_pairs(av_pairs, dataset):
	"""Returns the set of all cases matching an attribute value pair [(a,v)]"""
	set_av_pairs = []
	for av_pair in av_pairs:
		cases = set()
		row_counter = 0
		for row in dataset:
			row_counter += 1
			if row[av_pair[0]] == av_pair[1]:
				cases.add(row_counter)
		set_av_pairs.append(cases)
	return set_av_pairs

def get_ints_and_cards(concept, set_av_pairs):
	"""Calculates intersections between the given concept and attribute value pairs, includes cardinality"""
	ints_and_cards = []
	concept = set(concept)
	for cases in set_av_pairs:
		intersection = concept.intersection(cases)
		cardinality = len(cases)
		ints_and_cards.append((intersection, cardinality))
	return ints_and_cards

def get_best_intersection(ints_and_cards):
	"""Finds the best intersection for rule induction"""
	s = sorted(enumerate(ints_and_cards), key=lambda x: (len(x[1][0]), -x[1][1]), reverse=True)
	if len(s[0][1][0]) == len(s[1][1][0]) and s[0][1][1] == s[1][1][1]:
		# Heuristic, pick the first value with the appropriate intersection size and cardinality
		for index, i in enumerate(ints_and_cards):
			if len(i[0]) == len(s[0][1][0]) and i[1] == s[0][1][1]:
				return index, i
	else:
		return s[0]

def mlem2(lers_file_name):
	attributes, decision, dataset = parse_lers_file(lers_file_name)
	concepts, concept_names = get_concepts(dataset, decision)
	initial_av_pairs = get_attribute_value_pairs(attributes, dataset)
	initial_set_av_pairs = get_set_av_pairs(initial_av_pairs, dataset)

	attribute_value_pairs = deepcopy(initial_av_pairs)
	set_av_pairs = deepcopy(initial_set_av_pairs)

	covered_cases = set()
	
	rules = []

	for concept, concept_name in zip(concepts, concept_names):
		current_concept = set(concept)
		temp_intersection = set(range(1, len(dataset) + 1))
		conditions = []
		
		while len(current_concept) != 0:
			ints_and_cards = get_ints_and_cards(current_concept, set_av_pairs)
			best_av_pair_index, best_int_and_card = get_best_intersection(ints_and_cards)
			best_av_pair = set_av_pairs[best_av_pair_index]
			condition = attribute_value_pairs[best_av_pair_index]
			conditions.append(condition)

			temp_intersection = best_av_pair.intersection(temp_intersection)

			if temp_intersection.issubset(current_concept):
				# TODO: SIMPLIFY RULE

				# while RULE - FIRST CONDITION STILL WORKS
					# REMOVE FIRST CONDITION

				covered_cases = covered_cases.union(temp_intersection)
				current_concept = set(concept) - covered_cases
				rules.append((conditions, (decision, concept_name)))
				attribute_value_pairs = deepcopy(initial_av_pairs)
				set_av_pairs = deepcopy(initial_set_av_pairs)
				conditions = []
				temp_intersection = set(range(1, len(dataset) + 1))
			else:
				current_concept = current_concept.intersection(temp_intersection)
				del set_av_pairs[best_av_pair_index]
				del attribute_value_pairs[best_av_pair_index]

	# TODO: SIMPLIFY RULE SET

	for rule in rules:
		conditions = [str(x) for x in rule[0]]
		decision = rule[1]
		
		x = len(conditions)
		y = 0
		z = 0
		for row in dataset:
			match = True
			for condition in rule[0]:
				if row[condition[0]] != condition[1]:
					match = False
					break
			if match:
				z += 1
				if row[decision[0]] == decision[1]:
					y += 1

		print('{}, {}, {}'.format(x, y, z))
		print(' & '.join(conditions), end='')
		print(' -> ', end='')
		print(decision)

def main():
	# input_file_name = get_input_file_name()
	input_file_name = 'test.txt'
	mlem2(input_file_name)

if __name__ == '__main__':
	main()