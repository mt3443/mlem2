from copy import deepcopy
import os
import re

numerical_re = re.compile('-?\d+(?:\.\d+)?')
range_re = re.compile('-?\d+(?:\.\d+)?\.\.-?\d+(?:\.\d+)?')

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
	for i, line in enumerate(contents):
		for j, char in enumerate(line):
			if char == '!':
				contents[i] = line[:j]
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

	# Check what attributes, if any, have numerical values
	numerical_attributes = []
	for attribute in attributes:
		for case in dataset:
			value = case[attribute]

			if value in ['*', '-', '?']:
				continue

			if numerical_re.match(value):
				numerical_attributes.append(attribute)

			break

	attribute_value_pairs = []
	for attribute in attributes:
		# If attribute is numeric
		if attribute in numerical_attributes:

			# Get all values
			values = set()
			for case in dataset:
				value = case[attribute]
				if value not in ['*', '-', '?']:
					values.add(float(value))

			# Calculate cutpoints
			cutpoints = []
			values = sorted(values)
			for i, value in enumerate(values):
				if i + 1 in range(len(values)):
					next_value = values[i + 1]
					cutpoint = (value + next_value) / 2
					cutpoints.append(cutpoint)

			# Calculate ranges
			for cutpoint in cutpoints:
				r1 = '{}..{}'.format(values[0], cutpoint)
				r2 = '{}..{}'.format(cutpoint, values[-1])
				attribute_value_pairs.append((attribute, r1))
				attribute_value_pairs.append((attribute, r2))

		else:

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
	for attribute, value in av_pairs:
		cases = set()
		row_counter = 0
		for row in dataset:
			row_counter += 1
			
			# Match symbolic values
			if row[attribute] == value:
				cases.add(row_counter)
				continue

			# Match numerical values
			if range_re.match(value):
				lower_bound = float(value.split('..')[0])
				upper_bound = float(value.split('..')[1])
				if float(row[attribute]) >= lower_bound and float(row[attribute]) <= upper_bound:
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

# TODO: ADD CUTPOINTS FOR NUMERICAL VALUES
# TODO: ADD ? - AND * VALUES

def mlem2(lers_file_name):
	attributes, decision, dataset = parse_lers_file(lers_file_name)
	concepts, concept_names = get_concepts(dataset, decision)
	initial_av_pairs = get_attribute_value_pairs(attributes, dataset)
	initial_set_av_pairs = get_set_av_pairs(initial_av_pairs, dataset)

	attribute_value_pairs = deepcopy(initial_av_pairs)
	set_av_pairs = deepcopy(initial_set_av_pairs)
	av_pair_dict = {}

	for k, v in zip(attribute_value_pairs, set_av_pairs):
		av_pair_dict[k] = v

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

			# Check for attempted addition of nonsensical numerical ranges
			# If the rule we're trying to add has a range
			if range_re.match(condition[1]):
				bad_rule = False
				for c_attribute, c_value in conditions:
					# And there exists another rule with a range
					if condition[0] == c_attribute and range_re.match(c_value):
						a = float(c_value.split('..')[0]) # old lower bound
						b = float(c_value.split('..')[1]) # old upper bound
						c = float(condition[1].split('..')[0]) # new lower bound
						d = float(condition[1].split('..')[1]) # new upper bound

						# New range is more general or no overlap
						if (a == c and d > b) or (c < a and d == b) or (b < c) or (d < a):
							del set_av_pairs[best_av_pair_index]
							del attribute_value_pairs[best_av_pair_index]
							bad_rule = True
							break
					
				if bad_rule:
					continue

			conditions.append(condition)

			temp_intersection = best_av_pair.intersection(temp_intersection)

			if temp_intersection.issubset(current_concept):

				# Simplify the rule if possible

				# Try to simplify ranges
				range_attributes = set()
				for attribute, value in conditions:
					if range_re.match(value):
						range_attributes.add(attribute)

				for range_attribute in range_attributes:
					highest_lower_bound = None
					lowest_upper_bound = None

					conditions_to_remove = []

					for attribute, value in conditions:
						if attribute == range_attribute:
							lower_bound = float(value.split('..')[0])
							upper_bound = float(value.split('..')[1])

							if lowest_upper_bound is None or upper_bound < lowest_upper_bound:
								lowest_upper_bound = upper_bound

							if highest_lower_bound is None or lower_bound > highest_lower_bound:
								highest_lower_bound = lower_bound

							conditions_to_remove.append((attribute, value))

					for condition in conditions_to_remove:
						conditions.remove(condition)

					new_range = '{}..{}'.format(highest_lower_bound, lowest_upper_bound)
					conditions.append((range_attribute, new_range))

				# Try to drop unnecessary conditions
				for i, condition in enumerate(conditions):
					new_rule = conditions[:i] + conditions[i + 1:]
					new_cover = set(range(1, len(dataset) + 1))

					for c in new_rule:
						new_cover.intersection_update(av_pair_dict[c])

					if new_cover.issubset(concept):
						conditions.remove(condition)

				covered_cases = covered_cases.union(temp_intersection)
				current_concept = set(concept) - covered_cases
				rules.append((conditions, (decision, concept_name), temp_intersection))
				attribute_value_pairs = deepcopy(initial_av_pairs)
				set_av_pairs = deepcopy(initial_set_av_pairs)
				conditions = []
				temp_intersection = set(range(1, len(dataset) + 1))
			else:
				current_concept.intersection_update(temp_intersection)
				del set_av_pairs[best_av_pair_index]
				del attribute_value_pairs[best_av_pair_index]

	# Simplify ruleset if possible
	for i, rule in enumerate(rules):
		# Remove a rule
		new_ruleset = rules[:i] + rules[i + 1:]
		all_cases = set(range(1, len(dataset) + 1))
		temp_covered_cases = set()

		# Check which cases are covered while omitting the rule
		for r in new_ruleset:
			temp_covered_cases = temp_covered_cases.union(r[2])

		# If all cases are still covered, remove the rule, as it is redundant
		if len(all_cases - temp_covered_cases) == 0:
			rules.remove(rule)

	# Print rules
	for rule in rules:
		conditions = [str(x) for x in rule[0]]
		decision = rule[1]
		
		x = len(conditions)
		y = 0
		z = 0
		for row in dataset:
			match = True
			for attribute, value in rule[0]:
				if range_re.match(value):
					lower_bound = float(value.split('..')[0])
					upper_bound = float(value.split('..')[1])
					if float(row[attribute]) < lower_bound or float(row[attribute]) > upper_bound:
						match = False
						break
				elif row[attribute] != value:
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