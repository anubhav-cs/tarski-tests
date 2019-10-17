'''
Anu-References:-
1.  "Combining the Expressivity of UCPOP with the Efficiency of Graphplan"
    by B.Cenk Gazen and Craig A. Knoblock
'''

import os
import itertools
import shutil
import tarski

from tarski.reachability.asp import *
from tarski.reachability import create_reachability_lp

from tarski.io import FstripsReader
from tarski.grounding import LPGroundingStrategy, NaiveGroundingStrategy
from tarski.syntax.transform.quantifier_elimination import QuantifierElimination, QuantifierElimination
from tarski.syntax.formulas import QuantifiedFormula, CompoundFormula
from tarski.syntax.formulas import Quantifier, land
from tarski.syntax.transform.substitutions import create_substitution
from tarski.syntax.transform import term_substitution, PrenexTransformation
from tarski.fstrips import UniversalEffect, AddEffect, DelEffect

if shutil.which("gringo") is None :
    import pytest
    pytest.skip('Install the Clingo ASP solver and put the "gringo" binary on your PATH in order to test ASP-based '
                "reachability analysis", allow_module_level=True)



def process_formula(formula, lang) :
    """
    Recursively eliminate quantified formulas in formulas

    Arguments
    =========
    formula: CompoundFormula or QuantifiedFormula

    Returns
    =======
    Transformed formula
    """
    if isinstance(formula, CompoundFormula) :
        sub_f = []
        #print(formula.subformulas)
        for f in formula.subformulas :
            #print("here")
            sub_f.append(process_formula(f, lang))
            #print(sub_f)
        formula.subformulas = sub_f
        #print("\n")
        return formula
    elif isinstance(formula, QuantifiedFormula) :
        #print("QE ",formula)
        return (QuantifierElimination.rewrite( lang, formula, 
            QuantifierEliminationMode.All)).result
    else :
        return formula



def eliminate_universal_effects_quantifiers(problem) :
    """
    Elimates univeral effects from problem by transforming to multiple
    conditional effects

    Arguments
    =========
    problem: object of Problem class

    Returns
    =======
    None
    """
    for _, action in problem.actions.items() :
        effects = []
        for effect in action.effects :
            if isinstance(effect, UniversalEffect) :
                effects += transform_universal_effects(problem.language, effect)
            else :
                effects.append(effect)
        action.effects = effects
        action.precondition = process_formula(action.precondition,
                problem.language)
    return

def transform_universal_effects(lang, uni_eff) :
    """
    Elimates univeral effects by transforming to multiple conditional effects

    Arguments
    =========
    lang: object of type FirstOrderLanguage
    uni_effect: object of type UniversalEffect

    Returns
    =======
    list: list of instantiated effects
    """
    assert isinstance(uni_eff, UniversalEffect)
    effect_l = [] # new list of effects
    for effect in uni_eff.effects :
        # eliminate quantifiers from formula
        effect.condition = process_formula(effect.condition, lang)

        # if effect is Uni. Effect then transform to a list of Add/Del effects
        if isinstance(effect, UniversalEffect):
            effect_l += transform_universal_effects(lang, effect)
            continue

        # else if Add/Del effect, just instantiate condition and atom
        assert isinstance(effect, AddEffect) or isinstance(effect, DelEffect)

        card, syms, substs = _enumerate_instantiations(uni_eff.variables)
        if card == 0 :
            raise TransformationError("universal effect elimination",
                    uni_eff, "No constants were defined!")
        cond_effects    = []
        for values in itertools.product(*substs) :
            subst       = create_substitution(syms, values)
            cond_sub    = term_substitution(lang, effect.condition, subst)
            atom_sub    = term_substitution(lang, effect.atom, subst)
            if isinstance(effect, AddEffect) :
                ce = AddEffect(atom_sub, cond_sub)
            elif isinstance(effect, DelEffect) :
                ce = DelEffect(atom_sub, cond_sub)
            else :
                raise TransformationError("universal effect elimination",
                        uni_eff, "Effect type can't be handled!")
            cond_effects.append(ce)
        effect_l = effect_l + cond_effects
    return effect_l

def _enumerate_instantiations(variables) :
    """
    Enumerate Instantiations

    Argument
    ========
    variables: iterator of type class Variable

    Returns
    =======
    cardinality: int
    symbols: list
    instantiations: list
    """
    syms = []
    instantiations = []
    cardinality = 1
    for st in variables :
        if st.sort.builtin :
            raise TransformationError("universal effect elimination", phi,
                    "Variable found of built-in sort '{}', domain is too large!".
                    format(st.sort.name))
        syms.append(st)
        instantiations.append(list(st.sort.domain()))
        cardinality *= len(instantiations[-1])
    return cardinality, syms, instantiations

if __name__ == "__main__" :
    reader = FstripsReader(raise_on_error=True, theories=None)
    problem = reader.read_problem("domain.pddl","p02.pddl")
    #problem = reader.read_problem("scanalyzer_domain.pddl","scanalyzer_p01.pddl")
    #problem = reader.read_problem("organic-synthesis-split-ipc18_domain.pddl","organic-synthesis-split-ipc18_p01.pddl")
    #eliminate_universal_effects_quantifiers(problem)
    grounding = LPGroundingStrategy(problem)
    actions = grounding.ground_actions()
    actions = grounding.ground_state_variables()
    print(actions)
    print("Tests passed")
