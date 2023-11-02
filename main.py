def remove_units(grammar):
    G_prime = {k: [prod for prod in v if len(prod) != 1 or prod[0] not in grammar] for k, v in grammar.items()}
    
    unit_productions = []
    for nonterminal, productions in grammar.items():
        for production in productions:
            if len(production) == 1 and production[0] in grammar:
                unit_productions.append((nonterminal, production[0]))

    while unit_productions:
        X, Y = unit_productions.pop()
        for rule in grammar[Y]:
            if rule not in G_prime[X]:
                G_prime[X].append(rule)
                if len(rule) == 1 and rule[0] in grammar:
                    unit_productions.append((X, rule[0]))

    return G_prime

if __name__ == "__main__":
    # Reading grammar from file
    with open("input_grammar.txt", "r") as f:
        input_grammar_str = f.read()

    input_grammar = parse_grammar(input_grammar_str)
    print("Input Grammar:")
    print_grammar(input_grammar)
    
    modified_grammar = remove_units(input_grammar)
    print("\nModified Grammar:")
    print_grammar(modified_grammar)
