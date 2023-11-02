"""
Name : Adil Aman Mohammed
Course : Formal language theory
Assignment no: 5
CWID : A20395630
Description: the below code is an implementation of taking input CFG and applying 3 algorithms (Remove immediate left recursion, Remove left recursion, Remove unit productions)
"""

import sys

def readGrammarSymbols(filename):
    #initialize sets and start symbol
    terminal_symbols_set, non_terminal_symbols_set = set(), set()
    start_symbol = None
    
    #open grammar file
    with open(filename, 'r') as grammar_file:
        for line_number, grammar_rule in enumerate(grammar_file):
            #strip whitespaces
            grammar_rule = grammar_rule.strip()

            #split grammar rule
            parts = grammar_rule.split('::=')
            left_part, right_part = parts if len(parts) > 1 else (parts[0], '')

            #first line gives start symbol
            if line_number == 0:
                start_symbol = left_part.strip()

            #process left part for non-terminals
            non_terminals = []
            is_non_terminal = False
            for char in left_part:
                if char == '<':
                    is_non_terminal = True
                    non_terminal = char
                elif char == '>' and is_non_terminal:
                    non_terminal += char
                    non_terminals.append(non_terminal)
                    is_non_terminal = False
                elif is_non_terminal:
                    non_terminal += char
            non_terminal_symbols_set.update(non_terminals)

            #process right part for terminals and non-terminals
            symbols = right_part.split()
            for symbol in symbols:
                if '<' in symbol and '>' in symbol:
                    non_terminal_symbols_set.add(symbol)
                else:
                    terminal_symbols_set.add(symbol)

    #return sets and start symbol
    return terminal_symbols_set, non_terminal_symbols_set, start_symbol


#get symbols combinations from nullable set 
def generateAllSymbolCombinations(symbol_sequence, nullable_symbols):
    #base case: if there's no symbols, just return a list with an empty list
    if not symbol_sequence:
        return [[]]

    #grab the first symbol from the sequence
    current_symbol = symbol_sequence[0]
    
    #recursively find all combinations for the rest of the sequence
    combinations_for_rest = generateAllSymbolCombinations(symbol_sequence[1:], nullable_symbols)
    
    #initialize a list to store all possible combinations
    all_combinations = []

    #if the current symbol can be nullable, add combinations with and without it
    if current_symbol in nullable_symbols:
        #with current symbol
        with_current = [[current_symbol] + combo for combo in combinations_for_rest]
        #without current symbol
        without_current = [combo for combo in combinations_for_rest]
        #add both to all combinations
        all_combinations = with_current + without_current
    else:
        #if it's not nullable, just add combinations with the current symbol
        all_combinations = [[current_symbol] + combo for combo in combinations_for_rest]
    
    #returning all the combinations
    return all_combinations


#Function to identify nullable non-terminals in a set of production rules
def removalofepsilon(grammar_rules):
    #Initializing the set for nullable non-terminals
    nullable_non_terminals = set()

    #Initializing a list to keep track of non-terminals to be processed
    to_process = list()

    #First pass: identify non-terminals that directly produce epsilon
    for non_terminal, productions in grammar_rules.items():
        if '' in productions:
            nullable_non_terminals.add(non_terminal)
            to_process.append(non_terminal)

    #Processing until there are no more non-terminals to check
    while to_process:
        #Popping a non-terminal from the processing list
        current_non_terminal = to_process.pop()

        #Checking other productions to see if they can now be considered nullable
        for non_terminal, productions in grammar_rules.items():
            if non_terminal not in nullable_non_terminals:
                for production in productions:
                    production_symbols = production.split()
                    #If all symbols in the production are nullable
                    if all(symbol in nullable_non_terminals or symbol == '' for symbol in production_symbols):
                        nullable_non_terminals.add(non_terminal)
                        to_process.append(non_terminal)
                        break

    return nullable_non_terminals


#function to merge productions after removing epsilons
def mergeProductionsPostEpsilonElimination(rule_set, nullable_symbols_set):
    new_grammar_rules = {}

    #Looping over the grammar rules
    for head, body in rule_set.items():
        combined_rules = set()
        
        #Going over the production of a non-terminal
        for production in body:
            #Splitting the production into its basic symbols
            symbol_list = production.split()
            
            #Generating all possible variations considering nullable symbols
            generated_combinations = generateAllSymbolCombinations(symbol_list, nullable_symbols_set)
            
            #Adding the new rules to our set
            for variant in generated_combinations:
                new_rule = ' '.join(variant).replace('<>', '')
                combined_rules.add(new_rule)

        #Assigning the updated rules to the head of the production
        new_grammar_rules[head] = list(combined_rules)
        
        #Cleaning up in case an empty production got introduced
        if '' in new_grammar_rules[head]:
            new_grammar_rules[head].remove('')

    return new_grammar_rules

#function for extracting new grammar rules
def fetchUpdatedGrammarRules(filepath):
    #obtaining terminal symbols, non_terminal symbols, and start symbol
    terminalSymbols, nonTerminalSymbols, startSymbol = readGrammarSymbols(filepath)
    
    #initializing dictionary to store updated production rules
    updatedGrammarRules = {}
    
    with open(filepath, 'r') as file:
        #iterating through each production rule in the file
        for production in file:
            #splitting left and right side of production rule
            left, right = production.strip().split('::=')
            #trimming any leading or trailing whitespace
            left = left.strip()
            right = right.strip()
            
            #if left side not in dictionary, add it with an empty list
            if left not in updatedGrammarRules:
                updatedGrammarRules[left] = []
            #add right side to the list of productions for this non-terminal
            updatedGrammarRules[left].append(right)
    
    #returning updated grammar rules along with terminal and non-terminal symbols, and start symbol
    return updatedGrammarRules, terminalSymbols, nonTerminalSymbols, startSymbol

#Function for removing productions that aren't reachable
def discardUnreachableProductions(grammar_rules, start_symbol):
    #Only start symbol is reachable initially
    reachable = {start_symbol}
    #We'll store and update the list of newly found reachable symbols here
    newly_reachable = [start_symbol]

    #Keep searching until no new reachable symbols are found in an iteration
    while newly_reachable:
        current_symbol = newly_reachable.pop()
        #Check the productions of the current reachable symbol
        if current_symbol in grammar_rules:
            for production in grammar_rules[current_symbol]:
                for symbol in production.split():
                    #If we find a new reachable symbol, add it to the list
                    if symbol not in reachable:
                        reachable.add(symbol)
                        newly_reachable.append(symbol)

    #Filtering out unreachable productions
    filtered_grammar = {key: value for key, value in grammar_rules.items() if key in reachable}
    return filtered_grammar

#Eliminating unproductive rules from the grammar
def eliminateUnproductiveRules(grammar, terminals, nonTerminals, startSymbol):
    #Starting with terminals which are always productive
    productiveSymbols = set(terminals)
    previousProductiveCount = 0

    #Iterate until no new productive non-terminals are found
    while len(productiveSymbols) > previousProductiveCount:
        previousProductiveCount = len(productiveSymbols)

        #Checking each production rule
        for nonTerminal, productions in grammar.items():
            for production in productions:
                productionSymbols = set(production.split())

                #If all symbols in the production are productive, mark the non-terminal as productive
                if productionSymbols.issubset(productiveSymbols):
                    productiveSymbols.add(nonTerminal)
    
    #Filtering out unproductive productions from the grammar
    for nonTerminal in list(grammar.keys()):
        for production in grammar[nonTerminal]:
            productionSymbols = set(production.split())

            #If any non-terminal in the production is not productive, remove the production
            if not productionSymbols.issubset(productiveSymbols):
                grammar[nonTerminal].remove(production)

        #If all productions for a non-terminal are removed, remove the non-terminal
        if not grammar[nonTerminal]:
            del grammar[nonTerminal]
    return grammar

def handleNullableStart(productions, originalStart, nullableSymbols):
    #If the original start symbol can produce epsilon, we need to add a new start symbol
    if originalStart in nullableSymbols:
        newStartSymbol = '<new_start>'
        # Checking if new start symbol already exists in our production rules
        if newStartSymbol not in productions:
            productions[newStartSymbol] = []
        #Adding epsilon and the original start symbol to the productions of new start symbol
        productions[newStartSymbol].extend(['', originalStart])
        # Updating original start to be the new start symbol
        originalStart = newStartSymbol
    
    result = []
    #Formatting and adding productions to result list
    for left, rightList in productions.items():
        for right in rightList:
            production = f"{left} ::= {right}"
            result.append(production)
    
    #returning formatted grammar rules and updated start symbol
    return result, originalStart

#Function to get rid of unit productions in the grammar.
def eliminateUnitProductions(grammar_rules):
    # Finding all unit productions directly from the grammar
    direct_units = {(lhs, rhs) for lhs, prods in grammar_rules.items() for rhs in prods if rhs in grammar_rules}
    
    # Calculating transitive closure to catch indirect unit productions
    transitive_units = set(direct_units)
    changes_made = True
    while changes_made:
        changes_made = False
        for (A, B) in list(transitive_units):
            for (C, D) in list(transitive_units):
                if B == C and (A, D) not in transitive_units:
                    transitive_units.add((A, D))
                    changes_made = True
    
    # Creating new set of productions without the unit productions
    updated_rules = {}
    for lhs, rhs_list in grammar_rules.items():
        updated_rules[lhs] = [rhs for rhs in rhs_list if rhs not in grammar_rules]
    
    # Adding non-unit productions back
    for (A, B) in transitive_units:
        updated_rules[A].extend(production for production in updated_rules[B] if production not in grammar_rules)
    
    # Eliminate duplicate productions and sort them
    for lhs in updated_rules:
        updated_rules[lhs] = sorted(set(updated_rules[lhs]))

    return updated_rules

def removeImmLeftRecursion(rules):
    #Creating a new grammar without left recursion
    new_grammar = {}

    #Identifying immediate left recursions in the grammar
    lrr = identifyImmediateLeftRecursions(rules)

    #Iterating through production rules to eliminate left recursion
    for lhs, rhs_list in rules.items():
        #Checking if current non-terminal has immediate left recursion
        if lhs in lrr:
            alpha_set = [] #List to store α where A → Aα
            beta_set = []  #List to store β where A → β

            #Creating new non-terminal B as A'
            non_terminal_new = f"<{lhs[1:-1]}'>"

            #Dividing productions into alpha_set and beta_set
            for production in rhs_list:
                symbols = production.split()
                if symbols[0] == lhs: #Checking if production is of the form A → Aα
                    alpha_set.append(symbols[1:])
                else: #Production is of the form A → β
                    beta_set.append(symbols)

            #Adding non-left-recursive productions A → βA'
            new_grammar[lhs] = [' '.join(beta) for beta in beta_set]

            #If there are left-recursive alpha_set, create new productions with B
            if alpha_set:
                new_grammar[lhs] += [f"{' '.join(beta)} {non_terminal_new}" for beta in beta_set]
                #Creating productions for B → αB | α
                new_grammar[non_terminal_new] = [f"{' '.join(alpha)} {non_terminal_new}" for alpha in alpha_set]
                new_grammar[non_terminal_new] += [' '.join(alpha) for alpha in alpha_set]
        else:
            #If no left recursion for this non-terminal, keep productions as they are
            new_grammar[lhs] = rhs_list

    return new_grammar

def identifyImmediateLeftRecursions(grammar_rules):
    #Dictionary to store left recursive rules
    lrr = {}

    #Iterating through the grammar rules
    for lhs, rhs_list in grammar_rules.items():
        #Checking each production rule
        for rule in rhs_list:
            #Splitting the production into symbols
            rule_symbols = rule.split()
            #Checking if the first symbol is the same as lhs, indicating left recursion
            if rule_symbols and rule_symbols[0] == lhs:
                #If lhs is not in the dictionary, add it
                if lhs not in lrr:
                    lrr[lhs] = []
                #Add the left recursive rule to the dictionary
                lrr[lhs].append(rule)
    #Returning the dictionary with left recursive rules
    return lrr

def sortNonTerminals(grammar_rules):
    # List for storing non-terminals in order they appear
    sorted_non_terminals = []

    #Iterating through each production in the grammar
    for rule in grammar_rules:
        #Extracting non-terminal by splitting at ::= and trimming white space
        current_non_terminal = rule.split('::=')[0].strip()
        #Adding non-terminal to list if not already present
        if current_non_terminal not in sorted_non_terminals:
            sorted_non_terminals.append(current_non_terminal)
            
    #Returning the list of non-terminals in order
    return sorted_non_terminals

def identifyRequiredSubstitutions(sorted_non_terminals, grammar_rules):
    #Dictionary for keeping track of substitutions that need to be made
    substitutions_needed = {}
    
    #Iterate through the sorted non-terminals with their indices
    for index, current_non_terminal in enumerate(sorted_non_terminals):
        #Getting the productions for the current non-terminal
        current_productions = grammar_rules[current_non_terminal]
        
        #Iterate through each production of the current non-terminal
        for production in current_productions:
            #Splitting production to get the first symbol and handling empty productions
            first_symbol_in_production = production.split()[0] if production.split() else ""
            
            #Check if first symbol is a non-terminal and appears earlier in the order
            if first_symbol_in_production in sorted_non_terminals and sorted_non_terminals.index(first_symbol_in_production) < index:
                #If the current non-terminal is not already in the dictionary, add it with an empty list
                if current_non_terminal not in substitutions_needed:
                    substitutions_needed[current_non_terminal] = []
                
                #Add the production to the list of productions that need substitution
                substitutions_needed[current_non_terminal].append(production)
                
    #Return the dictionary containing non-terminals and the productions that need substitutions
    return substitutions_needed

def performSubstitutionProcess(sorted_non_terminals, initial_grammar, substitutions_to_apply):
    #Making a deep copy to avoid changes during iteration
    updated_grammar_rules = {non_term: rules[:] for non_term, rules in initial_grammar.items()}

    #Going through the non-terminals in specified order
    for current_non_terminal in sorted_non_terminals:
        if current_non_terminal in substitutions_to_apply:
            #Creating a list to store new productions after substitution
            additional_productions = []

            #Iterating through productions of the current non-terminal that need substitution
            for production in substitutions_to_apply[current_non_terminal]:
                #Identifying the first symbol of the production
                leading_symbol = production.split()[0]
                
                #Substituting productions of the leading non-terminal into the current production
                for substitute_production in initial_grammar[leading_symbol]:
                    #Performing the substitution
                    substituted_production = production.replace(leading_symbol, substitute_production, 1)

                    #Avoiding cycles by preventing self-references in the productions
                    if not substituted_production.startswith(current_non_terminal):
                        additional_productions.append(substituted_production)

            #Removing old productions that have been substituted
            updated_grammar_rules[current_non_terminal] = [rule for rule in updated_grammar_rules[current_non_terminal] if rule not in substitutions_to_apply[current_non_terminal]]
            
            #Adding the new productions after substitution
            updated_grammar_rules[current_non_terminal].extend(additional_productions)

    #Returning the grammar with substitutions applied
    return updated_grammar_rules


def removeLeftRecursion(production_rules):
    # Find sortNonTerminals of the non-terminals.
    order = sortNonTerminals(production_rules)

    # Keep applying substitutions and removing left recursion until it's resolved.
    while True:
        # Find what productions need substitution.
        needs_substitution = identifyRequiredSubstitutions(order, production_rules)
        
        # If there are productions that need substituting, apply the substitutions.
        if needs_substitution:
            production_rules = performSubstitutionProcess(order, production_rules, needs_substitution)
        else:
            # If no more substitutions are needed, break the loop.
            break

    # After substitutions, check if the grammar has any left recursions.
    while True:
        left_recursive = identifyImmediateLeftRecursions(production_rules)
        if left_recursive:
            production_rules = removeImmLeftRecursion(production_rules)
        else:
            break
    return production_rules

def eliminateLeftRecursion(grammar_rules):
    #Sorting the non-terminals to establish a processing order
    processing_order = sortNonTerminals(grammar_rules)

    #Iteratively apply substitutions and eliminate left recursion until it's resolved
    while True:
        #Identifying productions that require substitution
        substitutions_needed = identifyRequiredSubstitutions(processing_order, grammar_rules)

        #If there are productions that require substitution, proceed to apply them
        if substitutions_needed:
            grammar_rules = performSubstitutionProcess(processing_order, grammar_rules, substitutions_needed)
        else:
            #If no further substitutions are necessary, exit the loop
            break

    #Post-substitution, check and remove any remaining left recursions in the grammar
    while True:
        #Identifying left recursive productions
        left_recursive_productions = identifyImmediateLeftRecursions(grammar_rules)
        if left_recursive_productions:
            grammar_rules = removeImmLeftRecursion(grammar_rules)
        else:
            #If no left recursive productions are found, exit the loop
            break
    
    #Returning the modified grammar without left recursion
    return grammar_rules          
            
def Main(inputFilePath, outputFilePath):
    #Acquiring grammar rules from input
    grammarRules, terminals, nonTerminals, startSymbol = fetchUpdatedGrammarRules(inputFilePath)

    #Implementing the algorithm to remove unproductive rules from the grammar
    grammarRules = eliminateUnproductiveRules(grammarRules, terminals, nonTerminals, startSymbol)  

    #Executing the procedure to eliminate unreachable rules from the grammar
    grammarRules = discardUnreachableProductions(grammarRules, startSymbol)

    #Running epsilon removal procedure
    nullableSymbols = removalofepsilon(grammarRules)
    grammarRules = mergeProductionsPostEpsilonElimination(grammarRules, nullableSymbols)

    #Handling the special case where the start symbol might be nullable
    rulesInFormat, startSymbol = handleNullableStart(grammarRules, startSymbol, nullableSymbols)

    #Reformatting the rules for further processing
    restructuredGrammar = {}
    for rule in rulesInFormat:
        lhs, rhs = map(str.strip, rule.split("::="))
        if lhs not in restructuredGrammar:
            restructuredGrammar[lhs] = []
        restructuredGrammar[lhs].append(rhs)

    #Applying algorithm to remove unit productions
    restructuredGrammar = eliminateUnitProductions(restructuredGrammar)
    
    print("Final Productions:")

    #Removing any remaining left recursion in the grammar
    restructuredGrammar = eliminateLeftRecursion(restructuredGrammar)

    #Displaying the final set of production rules
    for lhs, rhsList in restructuredGrammar.items():
        for rhs in rhsList:
            print(f"{lhs} ::= {rhs}")

    #Converting the grammar back to the original format for output
    finalFormattedRules = [f"{lhs} ::= {rhs}" for lhs, rhsList in restructuredGrammar.items() for rhs in rhsList]

    #Writing the final set of production rules to the output file
    with open(outputFilePath, 'w') as outputFile:
        for rule in finalFormattedRules:
            outputFile.write(f"{rule}\n")


if __name__ == "__main__":
    if len(sys.argv) != 3:
        print("wrong arguments")
        sys.exit(1)

    input_filename = sys.argv[1]
    output_filename = sys.argv[2]
    Main(input_filename, output_filename)
