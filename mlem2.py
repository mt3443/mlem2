from copy import deepcopy
import os
import re

numerical_re = re.compile('^-?\d+(?:\.\d+)?$')
range_re = re.compile('^-?\d+(?:\.\d+)?\.\.-?\d+(?:\.\d+)?$')

class Dataset:

	def __init__(self, input_file_name, concept_approximation, output_file_name):
		self.input_file_name = input_file_name
		self.concept_approximation = concept_approximation
		self.output_file_name = output_file_name

	def mlem2(self):
		self.parse_lers_file()
		self.get_av_pairs()
		self.get_av_pair_cases()
		self.get_goals()
		self.induce_rules()
		self.log_rules()

	def parse_lers_file(self):
		"""Reads LERS file, removes comments, returns attributes, decision, dataset"""

		self.numerical_attributes = set()

		# Read file
		contents = open(self.input_file_name).read().splitlines()

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

				if numerical_re.match(value):
					self.numerical_attributes.add(attribute)

			dataset.append(row)

		self.attributes = attributes[:-1]
		self.decision = attributes[-1]
		self.dataset = dataset
		self.universe = set(range(1, len(dataset) + 1))

	def is_incomplete(self):
		for row in self.dataset:
			for key, value in row.items():
				if value in ['?', '-', '*']:
					return True
		return False

	def get_av_pairs(self):
		self.ordered_av_pairs = []
		self.av_pairs = {}
		for attribute in self.attributes:
			if attribute in self.numerical_attributes:
				# get all values
				all_values = set()
				for row in self.dataset:
					value = row[attribute]
					if value not in ['*', '-', '?']:
						all_values.add(float(value))

				# calculate cutpoints and intervals
				all_values = sorted(all_values)
				for i, value in enumerate(all_values):
					if i + 1 < len(all_values):
						next_value = all_values[i + 1]
						cutpoint = (float(value) + float(next_value)) / 2
						self.av_pairs[(attribute, '{}..{}'.format(all_values[0], cutpoint))] = set()
						self.av_pairs[(attribute, '{}..{}'.format(cutpoint, all_values[-1]))] = set()
						self.ordered_av_pairs.append((attribute, '{}..{}'.format(all_values[0], cutpoint)))
						self.ordered_av_pairs.append((attribute, '{}..{}'.format(cutpoint, all_values[-1])))
			else:
				# get possible values
				possible_values = set()
				for row in self.dataset:
					value = row[attribute]
					if value not in ['*', '-', '?'] and value not in possible_values:
						possible_values.add(value)
						self.av_pairs[(attribute, value)] = set()
						self.ordered_av_pairs.append((attribute, value))

	def get_av_pair_cases(self):
		self.v = {}
		for i, row in enumerate(self.dataset):
			case = i + 1
			for attribute in self.attributes:
				value = row[attribute]

				if numerical_re.match(value):
					# put in all ranges
					for a, v in self.av_pairs:
						if a == attribute and range_re.match(v):
							lower_bound = float(v.split('..')[0])
							upper_bound = float(v.split('..')[1])

							if float(value) <= upper_bound and float(value) >= lower_bound:
								self.av_pairs[(attribute, v)].add(case)
				elif value == '*':
					# put in all av_pairs that have the attribute
					for a, v in self.av_pairs:
						if a == attribute:
							self.av_pairs[(attribute, v)].add(case)
				elif value == '-':
					# add to attribute-concept av pairs
					concept_values = set()
					for r in self.dataset:
						if r[self.decision] == row[self.decision] and r[attribute] not in ['-', '?', '*']:
							concept_values.add(r[attribute])
					self.v[(case, attribute)] = concept_values
					for concept_value in concept_values:
						if numerical_re.match(concept_value):
							for a, v in self.av_pairs:
								if a == attribute and range_re.match(v):
									lower_bound = float(v.split('..')[0])
									upper_bound = float(v.split('..')[1])

									if float(value) <= upper_bound and float(value) >= lower_bound:
										self.av_pairs[(attribute, v)].add(case)
						else:
							for a, v in self.av_pairs:
								if a == attribute and v == concept_value:
									self.av_pairs[(attribute, v)].add(case)
				elif value != '?':
					# add to correct av pair
					self.av_pairs[(attribute, value)].add(case)

	def get_goals(self):
		self.decision_values = []
		self.goals = []
		for row in self.dataset:
			if row[self.decision] not in self.decision_values:
				self.decision_values.append(row[self.decision])

		for decision_value in self.decision_values:
			goal = []
			for i, row in enumerate(self.dataset):
				case = i + 1
				if row[self.decision] == decision_value:
					goal.append(case)
			self.goals.append(goal)

		if self.is_incomplete():
			self.get_concept_approximations()

	def get_concept_approximations(self):
		self.get_characteristic_sets()
		for i, goal in enumerate(self.goals):
			approximation = set()
			for j, characteristic_set in enumerate(self.characteristic_sets):
				case = j + 1
				if self.concept_approximation == 'lower':
					if case in goal and characteristic_set.issubset(goal):
						approximation = approximation.union(characteristic_set)
				else:
					if case in goal:
						approximation = approximation.union(characteristic_set)
			self.goals[i] = sorted(approximation)

	def get_characteristic_sets(self):
		self.characteristic_sets = []
		for i, row in enumerate(self.dataset):
			case = i + 1
			characteristic_set = deepcopy(self.universe)
			for attribute in self.attributes:
				value = row[attribute]

				if value == '-':
					if len(self.v[(case, attribute)]) != 0:
						s = set()
						for v in self.v[(case, attribute)]:
							s = s.union(self.av_pairs[(attribute, v)])
						characteristic_set.intersection_update(s)
				elif value not in ['*', '?']:
					characteristic_set.intersection_update(self.av_pairs[(attribute, value)])
			self.characteristic_sets.append(characteristic_set)

	def induce_rules(self):
		self.rules = []
		self.cases_covered = []

		for decision_value, goal in zip(self.decision_values, self.goals):
			concept = set(goal)
			remaining_cases = set(goal)
			conditions = []
			cases_covered = set()
			temp_intersection = deepcopy(self.universe)
			
			while len(remaining_cases) != 0:
				ints_and_cards = self.get_ints_and_cards(remaining_cases)
				best_condition = self.get_best_condition(ints_and_cards, conditions)

				if best_condition is None:
					print('Could not find a better condition')
					exit()

				conditions.append(best_condition)
				temp_intersection.intersection_update(self.av_pairs[best_condition])

				if temp_intersection.issubset(concept):
					rule = self.simplify_rule(conditions, concept)
					rule = (rule, (self.decision, decision_value))
					self.rules.append(rule)
					self.cases_covered.append(temp_intersection)
					cases_covered = cases_covered.union(temp_intersection)
					remaining_cases = concept - cases_covered
					conditions = []
					temp_intersection = deepcopy(self.universe)
				else:
					remaining_cases.intersection_update(temp_intersection)

		self.simplify_ruleset()

	def get_ints_and_cards(self, remaining_cases):
		"""Calculates intersections and cardinalities"""
		ints_and_cards = []
		for av_pair in self.ordered_av_pairs:
			intersection = remaining_cases.intersection(self.av_pairs[av_pair])
			cardinality = len(self.av_pairs[av_pair])
			ints_and_cards.append({'intersection': intersection, 'cardinality': cardinality})
		return ints_and_cards

	def get_best_condition(self, ints_and_cards, conditions):
		candidates = sorted(zip(self.ordered_av_pairs, ints_and_cards), key=lambda x: (len(x[1]['intersection']), -x[1]['cardinality']), reverse=True)
		valid_candidates = []

		for candidate in candidates:
			valid_condition = True

			if candidate[0] in conditions:
				continue

			for attribute, value in conditions:
				if candidate[0][0] == attribute:
					if range_re.match(candidate[0][1]):
						# check if new range overlaps/is a subset of the 
						a = float(value.split('..')[0])
						b = float(value.split('..')[1])
						c = float(candidate[0][1].split('..')[0])
						d = float(candidate[0][1].split('..')[1])

						if b < c or d < a or (a == c and b < d) or (b == d and c < a):
							valid_condition = False
							break
					else:
						valid_condition = False
						break

			if valid_condition:
				valid_candidates.append(candidate)

		if len(valid_candidates) == 0:
			return None
		
		if len(valid_candidates) == 1:
			return valid_candidates[0][0]

		# Heuristic
		if (
			len(valid_candidates[0][1]['intersection']) == len(valid_candidates[1][1]['intersection']) 
			and valid_candidates[0][1]['cardinality'] == valid_candidates[1][1]['cardinality']
		):
			for candidate in zip(self.ordered_av_pairs, ints_and_cards):
				if (
					len(candidate[1]['intersection']) == len(valid_candidates[0][1]['intersection'])
					and candidate[1]['cardinality'] == valid_candidates[0][1]['cardinality']
					and candidate[0] not in conditions
				):
					return candidate[0]
		else:
			return valid_candidates[0][0]

	def simplify_rule(self, conditions, concept):

		# drop redundant conditions
		i = 0
		while i < len(conditions):
			new_rule = conditions[:i] + conditions[i + 1:]
			new_covering = deepcopy(self.universe)
			for c in new_rule:
				new_covering.intersection_update(self.av_pairs[c])
			if new_covering.issubset(concept):
				conditions = new_rule
			else:
				i += 1

		# simplify ranges
		for numerical_attribute in self.numerical_attributes:
			new_conditions = []
			highest_lower_bound = None
			lowest_upper_bound = None
			for attribute, value in conditions:
				if attribute == numerical_attribute and range_re.match(value):
					lower_bound = float(value.split('..')[0])
					upper_bound = float(value.split('..')[1])

					if highest_lower_bound is None or lower_bound > highest_lower_bound:
						highest_lower_bound = lower_bound

					if lowest_upper_bound is None or upper_bound < lowest_upper_bound:
						lowest_upper_bound = upper_bound
				else:
					new_conditions.append((attribute, value))
			if highest_lower_bound is not None and lowest_upper_bound is not None:
				new_conditions.append((numerical_attribute, '{}..{}'.format(highest_lower_bound, lowest_upper_bound)))
				conditions = new_conditions

		return conditions

	def simplify_ruleset(self):
		for i in reversed(range(len(self.cases_covered))):
			new_cases_covered = self.cases_covered[:i] + self.cases_covered[i + 1:]
			new_cases_covered_set = set()
			for c in new_cases_covered:
				new_cases_covered_set = new_cases_covered_set.union(c)
			if new_cases_covered_set == self.universe:
				del self.rules[i]
				del self.cases_covered[i]

	def log_rules(self):
		output = open(self.output_file_name, 'w')
		for rule in self.rules:
			conditions = [str(x) for x in rule[0]]
			decision = str(rule[1])

			x = len(conditions)
			y = 0
			z = 0

			for row in self.dataset:
				match = True
				for attribute, value in rule[0]:
					if range_re.match(value):
						lower_bound = float(value.split('..')[0])
						upper_bound = float(value.split('..')[1])
						
						if range_re.match(row[attribute]):
							lower_bound_1 = float(row[attribute].split('..')[0])
							upper_bound_1 = float(row[attribute].split('..')[1])

							if lower_bound != lower_bound_1 or upper_bound != upper_bound_1:
								match = False
								break
						else:
							if float(row[attribute]) < lower_bound or float(row[attribute]) > upper_bound:
								match = False
								break
					elif row[attribute] != value:
						match = False
						break
				if match:
					z += 1
					if row[self.decision] == rule[1][1]:
						y += 1

			print('{}, {}, {}'.format(x, y, z))
			print(' & '.join(conditions), end='')
			print(' -> ', end='')
			print(decision)

			output.write('{}, {}, {}\n'.format(x, y, z))
			output.write(' & '.join(conditions))
			output.write(' -> ')
			output.write(decision + '\n')


def get_input_file_name():
	input_file_name = input('Enter input file name: ')
	while input_file_name == '' or not os.path.exists(input_file_name):
		print('Error: invalid file name')
		input_file_name = input('Enter input file name: ')
	return input_file_name

def get_concept_approximation():
	concept_approximation = input('Would you like to use upper or lower concept approximations? Enter "upper" or "lower": ').lower()
	while concept_approximation not in ['upper', 'lower']:
		print('Error: invalid choice')
		concept_approximation = input('Would you like to use upper or lower concept approximations? Enter "upper" or "lower": ').lower()
	return concept_approximation

def get_output_file_name():
	output_file_name = input('Enter output file name: ')
	while output_file_name.strip() == '':
		print('Error: invalid file name')
		output_file_name = input('Enter output file name: ')
	return output_file_name

def main():

	# input_file_name = get_input_file_name()
	# concept_approximation = get_concept_approximation()
	# output_file_name = get_output_file_name()

	input_file_name = 'austr-aca-35.txt'
	concept_approximation = 'upper'
	output_file_name = 'a.txt'

	d = Dataset(input_file_name, concept_approximation, output_file_name)
	d.mlem2()

if __name__ == '__main__':
	main()