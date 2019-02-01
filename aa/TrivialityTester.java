package aa;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;

public class TrivialityTester {

	private ArrayList<String> elements;

	public TrivialityTester(ArrayList<String> e){
		elements = e;
	}

	
	
	
	
	/**
	 * Remove any common axioms with a trivial structure.
	 */
	public void removeAllTrivialAxioms(Map<String, CommonAxiom> axioms){
		Iterator<CommonAxiom> iter  = axioms.values().iterator();	
		while (iter.hasNext()){
			FormulaTree f = (FormulaTree)iter.next();
			if (containsTrivial(f)){
				iter.remove();
			}
		}
	}
	
	
	/**
	 * Remove any formula with a trivial structure.
	 * Void method removes formulas in-place
	 * @param formulas
	 */
	public void removeAllTrivial(Map<String, FormulaTree> formulas){
		Iterator<FormulaTree> iter  = formulas.values().iterator();
		while (iter.hasNext()){
			
			FormulaTree next = iter.next();
			
			if (containsTrivial(next)){
				iter.remove();
			}
		}		
	}
	
	
	
	/**
	 * Return true if a formula has a trivial subformula.
	 * @see {{@link #isTrivial(FormulaTree)}}
	 * @param f
	 * @return
	 */
	public boolean containsTrivial(FormulaTree f){
		boolean containsTrivial = false;
				
		if(f.root() instanceof Implies || f.root() instanceof Or){
			containsTrivial = isTrivial(f);
			if(containsTrivial){
				return true;
			}
		}
		FormulaTree left = f.left();
		FormulaTree right = f.right();		
		
		if (left != null){
			containsTrivial = containsTrivial(left);
			if (containsTrivial){
				return true;
			}
		}
		if (right != null){
			containsTrivial = containsTrivial(right);			
		}
		return containsTrivial;
	}
	
	
	/**
	 * Return true if this formula is trivial.
	 * Trivial formulas are: <p>
	 * 
	 * implications with an antecedent that is always false<p>
	 * implications with an consequent that is always true<p>
	 * implications of the form A -> (B -> A)<p>
	 * 
	 * disjunctions where one disjunct is always false <p>
	 * disjunctions of the form A v ¬A<p>
	 * 
	 * biconditionals of the form A <-> A<p>
	 * (These are eliminated by design where A is atomic, but are possible otherwise)
	 *
	 * @param f FormulaTree
	 * @return true if f is trivial
	 */
	public boolean isTrivial(FormulaTree f){
		if (f.root() instanceof Implies){return isTrivialImplication(f);}
		if (f.root() instanceof Or){return isTrivialDisjunction(f);}
		if (f.root() instanceof Iff){return isTrivialBiconditional(f);}
		
		return false;
	}
	
	/**
	 * Test if an implication is trivial.
	 * An implication is trivial if the antecedent is always false, 
	 * or the consequent is always true. 
	 * 
	 * @param f the formula for an implication
	 * @return true if f trivial
	 */
	private boolean isTrivialImplication(FormulaTree f){
		FormulaTree antecedent = f.left();
		FormulaTree consequent = f.right();
		
		//trivial if a chain of implications A -> (B -> A)
		if (consequent.root() instanceof Implies 
				&& antecedent.outputTextFormula().equals(consequent.right().outputTextFormula())){
			
		//	System.out.println("TRIVIAL CHAIN: " + f.outputTextFormula());
			
			return true;
		}
		if (alwaysFalse(antecedent)){
			return true;
		}
		if (alwaysTrue(consequent)){
			return true;
		}
		return false;
	}
	
	
	//TODO: remove whitespace from strings ************************************
	
	/**
	 * Test if an disjunction is trivial (if either disjunct is always false).
	 * 
	 * @param f the formula for an implication
	 * @return true if f trivial
	 */
	private boolean isTrivialDisjunction(FormulaTree f){
		//deepCopy need for alwaysFalse
		FormulaTree formula = f.deepCopy();
		FormulaTree left = formula.left();
		FormulaTree right = formula.right();
		if (alwaysFalse(left) || alwaysFalse(right)){
			return true;
		}
		
		String leftString = left.outputTextFormula().trim();
		String rightString = right.outputTextFormula().trim();
		
		if (leftString.equals("¬" + rightString) || rightString.equals("¬" + leftString)){
			return true;
		}
		return false;
	}
	
	
	/**
	 * Change the first character of a formula from a space to a negation character
	 * @param f
	 * @return
	 */
	private String negatedFormula(FormulaTree f){
		return "¬" + f.outputTextFormula().substring(1);
	}
	
	
	
	//A v ¬A  or ¬A v A
	
	/* f.left.out = ¬+f.rightout
	 * 
	 * 
	 * 
	 * 
	 * 
	 */
	
	
	
	
	
	/**
	 * Test if a biconditional is trivial. 
	 * Biconditionals are trivial if they have the form A <-> A. 
	 * Also eliminates statements where both sides are always false
	 * These are eliminated by design if A is atomic, but are possible otherwise.
	 * @param f
	 * @return
	 */
	private boolean isTrivialBiconditional(FormulaTree f){
		if (f.root() instanceof Iff && f.left().outputTextFormula().equals(f.right().outputTextFormula())){
			
		//	System.out.println("TRIVIAL BICONDITIONAL: " + f.outputTextFormula());
			
			return true;
		}
		if (f.root() instanceof Iff && alwaysFalse(f.left()) && alwaysFalse(f.right())){
			
			System.out.println("BAD BICON: " + f.outputTextFormula());
			
			return true;
		}
		
		return false;
	}
	
	
	
	
	
	
	/**
	 * Determine if an expression is always false.
	 * P(x) & Q(y) is always false if ∀x∀y ¬(P(x) & Q(y)) is true.
	 * Any free variables are bound to universal quantifiers
	 * @param f a formula
	 * @return true if formula is always false
	 */
	public boolean alwaysFalse(FormulaTree f){
		ArrayList<Character> freevars = freeVariables(f);		
		FormulaTree[] quantifierPrefix = universalQuantiferPrefix(freevars);
		FormulaTree negation = new FormulaTree(new Not());

		//construct tree
		if (quantifierPrefix.length > 0){
			quantifierPrefix[quantifierPrefix.length-1].setLeft(negation);
		}
		negation.setLeft(null);
		negation.setRight(f.deepCopy());

		
		FormulaTree universalNegated = null;
		
		if (quantifierPrefix.length > 0){
			universalNegated = quantifierPrefix[0];
		} else {
			universalNegated = negation;
		}
		
		//if true, f is always false
		if (universalNegated.value(elements)){
			return true;
		}		
		return false;
	}
	
	
	
	/**
	 * Determine if an expression is always true.
	 * P(x) & Q(y) is always true if ∀x∀y (P(x) & Q(y)) is true.
	 * Any free variables are bound to universal quantifiers.
	 * @param f a formula
	 * @return true if formula is always true
	 */
	public boolean alwaysTrue(FormulaTree f){
		
		//x==y cannot always be true if more than one element
		if (f.root() instanceof Equals && elements.size() > 1){
			return false;
		}
		
		ArrayList<Character> freevars = freeVariables(f);		
		FormulaTree[] quantifierPrefix = universalQuantiferPrefix(freevars);
		
		//construct tree
		if (quantifierPrefix.length > 0){
			quantifierPrefix[quantifierPrefix.length-1].setLeft(f.deepCopy());
		}
		
		FormulaTree fullExpression = null;
			
		if (quantifierPrefix.length > 0){
			fullExpression = quantifierPrefix[0];
		} else {
			fullExpression = f.deepCopy();
		}
		
		//if true, f is trivial
		if (fullExpression.value(elements)){
			return true;
		}		
		
		return false;
	}
	
	
	/**
	 * Check if a predicate is always false. 
	 * P(x) is always false if ∀x ¬P(x) is true. 
	 * @param p
	 * @return
	 */
	public boolean predicateAlwaysFalse(Predicate p){
		//universally quantify all variables in p
		FormulaTree[] quantifierPrefix = universalQuantiferPrefix(variablesForThisPredicate(p));
		
		FormulaTree negation = new FormulaTree(new Not());
		FormulaTree predicate = new FormulaTree(p);
		FormulaTree prefixEnd = quantifierPrefix[quantifierPrefix.length-1];
		
		//construct expression
		prefixEnd.setRight(null);
		prefixEnd.setLeft(negation);		
		negation.setRight(predicate);
		negation.setLeft(null);

		//if true then predicate is trivial 
		if(quantifierPrefix[0].value(elements)){
			return true;
		}
		return false;
	}


	
	/**
	 * Check if a predicate is always true, ie for P(x), 
	 * see if ∀x P(x) is true. 
	 * @param p
	 * @return
	 */
	public boolean predicateAlwaysTrue(Predicate p){
		//universally quantify all variables in p
		FormulaTree[] quantifierPrefix = universalQuantiferPrefix(variablesForThisPredicate(p));
		
		//FormulaTree negation = new FormulaTree(new Not());
		FormulaTree predicate = new FormulaTree(p);
		FormulaTree prefixEnd = quantifierPrefix[quantifierPrefix.length-1];
		
		//construct expression
		prefixEnd.setRight(null);
		prefixEnd.setLeft(predicate);		

		//if true then predicate is trivial 
		if(quantifierPrefix[0].value(elements)){
			return true;
		}
		return false;
	}
	
	

	/**
	 * Create a prefix that universally quantifies all variables for a given predicate
	 * variable tuple. For triviality testing only, not a generated formula, so the rule 
	 * for variable ranges is ignored. Quantifier order is also irrelevant, since all 
	 * quantifiers are universal. 
	 * @param vartuple
	 * @return a FormulaTree quantifier prefix of all universal quantifiers
	 */
	private FormulaTree[] universalQuantiferPrefix(ArrayList<Character> variables){
		//if no variables, return an empty array
		if (variables.size() == 0){
			return new FormulaTree[0];
		}
		
		FormulaTree[] quantifierPrefix = new FormulaTree[variables.size()];
		quantifierPrefix[0] = new FormulaTree(new UniversalQuantifier(variables.get(0)));
		
		for (int i = 1; i< variables.size(); i++){
			FormulaTree quantifier = new FormulaTree(new UniversalQuantifier(variables.get(i)));
			quantifierPrefix[i] = quantifier;
			quantifierPrefix[i-1].setRight(null);
			quantifierPrefix[i-1].setLeft(quantifierPrefix[i]);			
		}
		quantifierPrefix[quantifierPrefix.length-1].setRight(null);
		quantifierPrefix[quantifierPrefix.length-1].setLeft(null);		
		
		//return top of tree
		return quantifierPrefix;
	}


	/**
	 * Return the variables in this predicate term.
	 * Ignores the usual variable range rules. 
	 * @param p a predicate
	 * @return an ArrayList of the variable terms in p
	 */
	private ArrayList<Character> variablesForThisPredicate(Predicate p){
		ArrayList<Character> variables = new ArrayList<Character>();
		for (char v : p.varTuple()){
			if (!variables.contains(v)){
				variables.add(v);
			}
		}
		return variables;
	}
	
	
	/**
	 * Return all the free variables in an expression
	 * Calls the related tree-search function {{@link #getFreeVariables(FormulaTree)}. 
	 */
	public ArrayList<Character> freeVariables(FormulaTree f){
		Map<Character, Boolean> map = getFreeVariables(f);
		ArrayList<Character> free = new ArrayList<Character>();

		for(char v : map.keySet()){
			if (map.get(v)){
				free.add(v);
			}
		}
		return free;
	}
	
	
	
	
	/**
	 * Return all free variables in an expression. 
	 * Input formulas are not assumed to be in prenex normal form.
	 * @param f an expression
	 * @return a collection of the free variables in f
	 */
	public Map<Character, Boolean> getFreeVariables(FormulaTree f){
		Map<Character, Boolean> variableMap = new HashMap<Character, Boolean>();
				
		//iterate through tree 
		if (f.root() instanceof Quantifier){
			//mark as bound, ie not free
			variableMap.put(((Quantifier)f.root()).variable(), false);
						
		}
		if (f.root() instanceof Predicate){
			char[] variables = ((Predicate)f.root()).varTuple();
						
			for (char v : variables){
				//mark as free unless already bound
				if (variableMap.get(v) == null || !variableMap.get(v)){
					variableMap.put(v, true);										
				}
			}
		}
		if (f.left()!=null){
			variableMap.putAll(getFreeVariables(f.left()));
		}
		if (f.right()!=null){
			variableMap.putAll(getFreeVariables(f.right()));			
		}
		return variableMap;
	}
	
	

	/**
	 * Debugging print function
	 */
	public String listString(ArrayList<Character> vars){
		StringBuilder s = new StringBuilder();
		s.append("[");
		for (char c : vars){
			s.append(c);
		}
		s.append("]");
		return s.toString();
	}
	
	


}
