import time as t
import copy

TIME_LIMIT = 20
MAX_DEPTH = 120
DUPLICATE_COUNT = 15
FAILING_RESOLUTION = "failing_resolution"
COMPLETE_RESOLUTION = "complete_resolution"
TRUE, FALSE = "TRUE", "FALSE"


class KB:
    def __init__(self):
        self.positive_predicates = {}
        self.negated_predicates = {}
        self.all_predicates = set()
        self.visited = {}
        self.all_sentences = []
        self.sentence_count = 0
        self.constants = set()
        self.variables = set()

    def create_KB(self, input_sentences):
        self.convert_to_CNF(input_sentences)
        self.sentence_count = len(self.all_sentences)
        self.assign_dictionaries()
        # self.print_KB()

    def is_positive(self, predicate):
        if predicate[0] == "~":
            return False
        return True

    def return_conclusion(self, conclusion, count):
        conclusion_name, variable_list = self.return_name_and_variables(conclusion)
        final_conclusion = conclusion_name + "("
        for k in variable_list:
            if k.islower():
                final_conclusion += k + str(count) + ","
            else:
                final_conclusion += k + ","
        final_conclusion = final_conclusion[:-1] + ")"
        return final_conclusion

    def return_name_and_variables(self, predicate):

        return predicate[:predicate.find("(")], predicate[predicate.find("(") + 1:predicate.find(")")].split(",")

    def assign_dictionaries(self):
        count = 0
        for i in self.all_sentences:
            # print(i, "  ", i.split(" | "))
            for j in i.split(" | "):
                predicate_name, variable_list = self.return_name_and_variables(j)
                # print(i, "    ", predicate_name, variable_list)
                if predicate_name not in self.all_predicates:
                    if self.is_positive(predicate_name):
                        self.positive_predicates[predicate_name] = []
                    else:
                        self.negated_predicates[predicate_name] = []
                    self.all_predicates.add(predicate_name)
                if self.is_positive(predicate_name):
                    self.positive_predicates[predicate_name].append(count)
                else:
                    self.negated_predicates[predicate_name].append(count)
            count += 1

    def convert_to_CNF(self, input_sentences):
        for count, i in enumerate(input_sentences):
            temp_input_sentence = i.split("=>")
            final_sentence = ""
            if len(temp_input_sentence) == 2:
                # the sentence has premise and conclusion.
                final_premise = ""
                premise, conclusion = temp_input_sentence[0], temp_input_sentence[1]
                temp_premise = premise.split("&")

                # print(premise, "    ", temp_premise)
                for j in temp_premise:
                    predicate_name, variable_list = self.return_name_and_variables(j)
                    # print(j, "  ", predicate_name, variable_list)
                    final_premise += self.negate_predicate(predicate_name) + "("
                    for k in variable_list:
                        if k.islower():
                            final_premise += k + str(count) + ","
                        else:
                            final_premise += k + ","
                    final_premise = final_premise[:-1] + ")"
                    final_premise += " | "
                # print(premise, "  ", final_premise)
                conclusion = self.return_conclusion(conclusion, count)
                # print(conclusion)
                final_sentence = final_premise + conclusion

            else:
                # the sentence has only one predicate
                conclusion = self.return_conclusion(i, count)
                final_sentence = conclusion

            # print(i, "      ", final_sentence)
            if final_sentence not in self.all_sentences:
                self.all_sentences.append(final_sentence)

    def print_KB(self):
        print("Positive Predicates in the KB:", self.positive_predicates)
        print("Negated Predicates in the KB: ", self.negated_predicates)
        print("All Predicates: ", self.all_predicates)
        print("All Sentences: ", self.all_sentences)
        print("Number of sentences in the KB: ", self.sentence_count)
        print("Variables in the KB: ", self.variables)
        print("Constants in the KB: ", self.constants)

    def negate_predicate(self, predicate):
        if predicate[0] == "~":
            return predicate[1:]
        else:
            return "~" + predicate

    def do_queries(self, query):

        self.all_sentences.append(query)
        predicate_name, variable_list = self.return_name_and_variables(query)
        self.variables.add(str(variable_list))
        if predicate_name not in self.all_predicates:
            if self.is_positive(predicate_name):
                self.positive_predicates[predicate_name] = [self.sentence_count]
            else:
                self.negated_predicates[predicate_name] = [self.sentence_count]
        else:
            if self.is_positive(predicate_name):
                self.positive_predicates[predicate_name].append(self.sentence_count)
            else:
                self.negated_predicates[predicate_name].append(self.sentence_count)
        self.all_predicates.add(predicate_name)
        self.sentence_count += 1
        # self.print_KB()

    def is_terminal(self, depth):
        return depth > MAX_DEPTH

    def kb_length(self):
        return self.sentence_count

    def do_unify_dict(self, uni_dict, predicate_name):

        # finds all the negated version of the predicate in the sentences
        to_find_predicate = self.negate_predicate(predicate_name)

        if self.is_positive(predicate_name) and to_find_predicate in self.negated_predicates:
            uni_dict[predicate_name] = self.negated_predicates[to_find_predicate]
        elif not self.is_positive(predicate_name) and to_find_predicate in self.positive_predicates:
            uni_dict[predicate_name] = self.positive_predicates[to_find_predicate]
        return uni_dict

    def perform_unification(self, predicate1, predicate2):
        # 4 cases
        # print(predicate1, predicate2)
        unify_dict, no_constants = {}, True
        predicate1_name, variable1_list = self.return_name_and_variables(predicate1)
        predicate2_name, variable2_list = self.return_name_and_variables(predicate2)
        # print(predicate1_name, variable1_list)
        # print(predicate2_name, variable2_list)
        if len(variable1_list) != len(variable2_list):
            # no unification possible
            return {}, True

        for i, v1 in enumerate(variable1_list):
            v2 = variable2_list[i]
            if v2.islower() and not (v1.islower()):
                if v2 not in unify_dict:
                    unify_dict[v2], no_constants = v1, False

                elif unify_dict[v2] != v1:
                    return {}, no_constants
            elif v1.islower() and not (v2.islower()):
                if v1 not in unify_dict:
                    unify_dict[v1] = v2
                    no_constants = False
                elif unify_dict[v1] != v2:
                    return {}, no_constants
            elif v1.islower() and v2.islower():
                if v1 not in unify_dict and v2 not in unify_dict:
                    unify_dict[v1] = v2
            else:
                # v1 and v2 both are constants
                if v1 != v2:
                    return {}, no_constants
                else:
                    unify_dict[v1] = v2
                    no_constants = False

        return unify_dict, no_constants

    def get_index(self, predicates, negated_resol_name):
        indices = []
        count = 0
        for p in predicates:
            name, variables = self.return_name_and_variables(p)
            if name == negated_resol_name:
                indices.append(count)
            count += 1
        return indices

    def perform_string_tinkering(self, x, y):
        return '%s(%s) | ' % (x, ','.join(y))

    def return_resolved_sentence(self, uni_d, predicates_in_s, resolved_sentence):
        for i, i_ in enumerate(predicates_in_s):
            predicate_name, variable_list = self.return_name_and_variables(i_)
            for j, j_ in enumerate(variable_list):
                if j_ in uni_d:
                    variable_list[j] = uni_d[j_]

            resolved_sentence += self.perform_string_tinkering(predicate_name, variable_list)

        return uni_d, resolved_sentence

    def perform_resolution(self, predicates_in_s1, predicates_in_s2, resolving_name):

        unification_possile, resolved_sentence = False, ""
        ind_1 = self.get_index(predicates_in_s1, self.negate_predicate(resolving_name))
        ind_2 = self.get_index(predicates_in_s2, resolving_name)
        # print("sentence 1 predicates ", predicates_in_s1)
        # print("sentence 2 predicates ", predicates_in_s2)
        # print("resolving name :", resolving_name)
        # print("index1: ", ind_1)
        # print("index2: ", ind_2)

        for i, i_ in enumerate(ind_1):
            for j, j_ in enumerate(ind_2):
                uni_d, no_constants = self.perform_unification(predicates_in_s1[i_],
                                                               predicates_in_s2[j_])
                if uni_d:
                    unification_possile, buff_1, buff_2 = True, i, j
                    break

        if not unification_possile:
            return FAILING_RESOLUTION, True

        predicates_in_s1.pop(ind_1[buff_1])
        predicates_in_s2.pop(ind_2[buff_2])

        uni_d, resolved_sentence = self.return_resolved_sentence(uni_d, predicates_in_s1, resolved_sentence)
        uni_d, resolved_sentence = self.return_resolved_sentence(uni_d, predicates_in_s2, resolved_sentence)

        '''for i, i_ in enumerate(predicates_in_s1):
            predicate_name, variable_list = self.return_name_and_variables(i_)
            for j, j_ in enumerate(variable_list):
                if j_ in uni_d:
                    variable_list[j] = uni_d[j_]
            # resolved_sentence += '%s(%s) | ' % (name, ','.join(variables))
            resolved_sentence += self.perform_string_tinkering(predicate_name, variable_list)

        for i, predicate in enumerate(predicates_in_s2):
            name, variables = self.return_name_and_variables(predicate)
            for j, variable in enumerate(variables):
                if variable in uni_d:
                    variables[j] = uni_d[variable]
            resolved_sentence += '%s(%s) | ' % (name, ','.join(variables))'''

        # resolved_sentence == ''

        if not resolved_sentence:
            return COMPLETE_RESOLUTION, True
        else:
            resolved_sentence = resolved_sentence[:-3]
            resolved_sentence = resolved_sentence.split(" | ")
            resolved_predicates = set(resolved_sentence)

            remaining_predicates = []
            for i_ in resolved_predicates:
                if self.negate_predicate(i_) not in resolved_predicates:
                    remaining_predicates.append(i_)
            if not remaining_predicates:
                return FAILING_RESOLUTION, True
            else:
                remaining_predicates = sorted(remaining_predicates)
                resol_s = " | ".join(remaining_predicates)
                return resol_s, no_constants

    def add_predicates_to_dict(self, uni_d, predicate_name):
        if self.is_positive(predicate_name) and self.negate_predicate(predicate_name) in self.negated_predicates:
            uni_d[predicate_name] = self.negated_predicates[self.negate_predicate(predicate_name)]
        elif not self.is_positive(predicate_name) and self.negate_predicate(predicate_name) in self.positive_predicates:
            uni_d[predicate_name] = self.positive_predicates[self.negate_predicate(predicate_name)]
        return uni_d

    def resolvable(self, query, depth, start_time):

        # print(depth)
        # print("\n\n")
        # print("\n start_time: ", start_time)
        # print("\n current_time: ", t.time()-start_time)
        current_time = t.time() - start_time
        if self.is_terminal(depth):
            return False

        uni_d = {}
        # predicates = query.split(' | ')
        # print("depth: ", depth)
        # print("query: ", query)
        # print("predicates: ", predicates)
        # print("\n")
        for i_ in query.split(" | "):
            predicate_name, variable_list = self.return_name_and_variables(i_)
            uni_d = self.add_predicates_to_dict(uni_d, predicate_name)
            self.variables.add(str(variable_list))

        # print("uni_dict: ", uni_d)
        # print("\n")

        if uni_d:
            for i_ in uni_d:
                for j_ in uni_d[i_]:
                    resolved_sentence, buff_const = self.perform_resolution(self.all_sentences[j_].split(" | "),
                                                                            query.split(" | "), i_)
                    # print("resolved_sentence , no_constants ", resolved_sentence, buff_const)
                    # print("resolved_sentence: ", resolved_sentence)
                    # print("checked sentences: ", self.visited)

                    if resolved_sentence in self.visited:
                        if self.visited[resolved_sentence] >= DUPLICATE_COUNT:
                            continue
                    if resolved_sentence not in self.visited:
                        self.visited[resolved_sentence] = 0

                    if resolved_sentence == FAILING_RESOLUTION:
                        continue
                    if resolved_sentence == COMPLETE_RESOLUTION:
                        return True

                    # is_resolvable = self.resolvable(resolved_sentence, self.visited, depth + 1, start_time)
                    is_resolvable = self.resolvable(resolved_sentence, depth + 1, start_time)
                    if current_time > TIME_LIMIT:
                        return False

                    if is_resolvable:
                        return True
                    self.visited[resolved_sentence] += 1

        return False

    def ask_queries(self, query):
        # the query that we are getting here is the negated query
        self.do_queries(query)
        # print("\n\n")
        # self.print_KB()
        # print("\n\n")
        start_time = t.time()
        # print(start_time)
        # self.resolvable(query, self.visited, 0, start_time):
        if self.resolvable(query, 0, start_time):
            # print(True)
            print("time taken: ", t.time() - start_time)
            return TRUE
        else:
            # print(False)
            print("time taken: ", t.time() - start_time)
            return FALSE


class Solution:
    def __init__(self):
        self.input_q, self.input_s = self.get_input()
        output = self.do_tasks()
        self.print_outputs(output)
        # self.print_inputs()

    def remove_space(self, temp_buffer):
        temp_buffer = [x.replace(" ", "") for x in temp_buffer]
        return temp_buffer

    def get_input(self):
        file = open("input.txt", "r")
        n = int(file.readline().strip())
        input_q = [file.readline().strip() for _ in range(n)]
        input_q = self.remove_space(input_q)
        k = int(file.readline().strip())
        input_s = [file.readline().strip() for _ in range(k)]
        input_s = self.remove_space(input_s)
        return input_q, input_s

    def do_tasks(self):
        self.kb = KB()
        self.kb.create_KB(self.input_s)
        # self.kb.print_KB()
        outputs = []
        for i in self.input_q:
            self.temp_kb = copy.deepcopy(self.kb)
            # we are passing the negated query.
            output = self.temp_kb.ask_queries(self.temp_kb.negate_predicate(i))
            outputs.append(output)
        return outputs

    def print_inputs(self):
        print("Input Queries ", self.input_q)
        print("Input Sentences ", self.input_s)

    def print_outputs(self, outputs):
        file = open("output.txt", "w")
        for i in range(len(outputs)):
            if i == len(outputs) - 1:
                file.write(outputs[i])
            else:
                file.write(outputs[i] + "\n")


solution = Solution()
