package aa;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Map;
import java.util.LinkedHashMap;
import java.util.Set;
import java.util.Stack;

import javax.swing.SwingWorker;



//TODO: turn off hand elim if domain has only one element
//only needed if we turn back on elimination false prefixes


//SwingWorker<T,V>

//T: return type of doInBackground() and get()
//V: type used by publish() and process()

/* Extends Swing's "SwingWorker" class for performing lengthy tasks
 * without freezing the GUI
 */

/**
 * Class for generating all possible formulas in the search space specified in the input file. 
 *
 */
public class FormulaGenerator extends SwingWorker<Map<String, FormulaTree>, Void> {
	
	//input from file
	private Input input;
	
	//formula set to return
	private Map<String, FormulaTree> formulaSet;

	private TrivialityTester trivial;
	
	private boolean useHandElimination = true;
	private final boolean DEBUG = false;
	
	public FormulaGenerator(Input i){
		super();
		input = i;
		formulaSet = new LinkedHashMap<String, FormulaTree>();
		trivial = new TrivialityTester(input.elements());
	}

	
	/**
	 * Background task for formula generation
	 * @return a HashMap of all formulas
	 */
	@Override
	public Map<String, FormulaTree> doInBackground() {					
		
		
	//	System.err.print("Formula Generation: ");
		firePropertyChange("generation", 0, 1);
		
		int formulaCount = 0;

		//read data from input
		ArrayList<Relation> relations = input.relations();
		int varLimit = input.varLimit();
		int sizeLimit = input.sizeLimit();
		int order = input.numElements();
		
		if (order == 0){
			useHandElimination = false;
			System.err.println("WARNING: empty domain");
		}
		
		//NEW: add common mathematical axioms
		if (input.searchCommonAxioms()){
			firePropertyChange("common", -1, 0);
			
			//System.out.println("generating common axioms");
			
			Map<String, CommonAxiom> commonAxioms = commonAxioms(input.relations(), input.elements());
			trivial.removeAllTrivialAxioms(commonAxioms);	
			
			formulaSet.putAll(commonAxioms);
		//	System.out.println("generated " + commonAxioms.size() + " common axioms");		
		} 

		
		//tell GUI we are beginning size zero
		firePropertyChange("generation", 0, 1);
		
		//all predicates (size zero terms)
		ArrayList<Predicate> predicates = generatePredicates(relations, varLimit);

		//remove
		//System.err.println("generated " + predicates.size() + " predicates");
	
		//same message to standard error  (remove)
		//System.err.print("generating size 0: ");

		//generate and verify size zero formulas
		//loop over all predicates
		for (Predicate p : predicates){
			int numvars = FormulaTree.numVarsForThisRange(p.variableRange());

			//if a valid predicate for size zero, do hand elim search for true formulas
			if (numvars > 0){
				//wrap Tree object around Predicate
				FormulaTree term = new FormulaTree(p);

				//min set of true formulas for this term
				
				ArrayList<FormulaTree> f;
				
				if (DEBUG){
					f = debugHandEliminationSearch(term);
				} else {
					f = handEliminationSearch(term);
				}
				
				//add all
				for (FormulaTree t : f){
					formulaSet.put(t.outputTextFormula(), t);
					formulaCount++;
				}
			}
		}

		//show number of size zero formulas
		//System.err.println(formulaCount + " formulas");
		formulaCount = 0;

		if (sizeLimit < 1) {
			return formulaSet;
		}

		//tell GUI we are building size 1
		firePropertyChange("generation", 1, 2);

		//same message to standard error
		//System.err.print("generating size 1: ");
		
		//all possible one-operator subtree terms, over all predicates (size one terms)
		ArrayList<FormulaTree> subtrees = generateSubtrees(predicates, trivial);


		//generate size one terms
		//loop over all subtree terms (nodes with one or two children)
		for (FormulaTree term : subtrees){

			//stop if cancelled by GUI
			if (isCancelled()){								
				//System.err.println("FormGen cancelled ");
				return null;
			}
			
			int numvars = FormulaTree.numVarsForThisRange(term.variableRange());

			//if valid variable range, get min set of true formulas for this term
			if (numvars > 0){

				ArrayList<FormulaTree> f;

				if (DEBUG){
					f = debugHandEliminationSearch(term);
				} else {

					//min set of true formulas for this term
					f = handEliminationSearch(term);
				}

				
				//add all
				for (FormulaTree t : f){
					formulaSet.put(t.outputTextFormula(), t);
					formulaCount++;
				}			
			}
		}

		//System.err.println(formulaCount + " formulas");
		formulaCount = 0;

		if (sizeLimit < 2) {
			return formulaSet;
		}

		//older terms to iterate over, declare outside of loop 
		Collection<FormulaTree> oldTerms = deepCopyTreeCollection(subtrees);

		for (int size = 2; size <= sizeLimit; size++){

			//update GUI 
			firePropertyChange("generation", size, size+1);

			//same message to standard error  (remove)
			//System.err.print("generating size " + size + ": ");

			Map<String, FormulaTree> higherTerms = higherSizeTerms(oldTerms, subtrees);

		//	System.err.println("higher size " + size + " num formulas: " + higherTerms.size());
			
			//remove trivial formulas in-place
			trivial.removeAllTrivial(higherTerms);
			
		//	System.err.println("higher size after trivial: " + higherTerms.size());
			
			
			for (FormulaTree term : higherTerms.values()){

				//stop if cancelled by GUI
				if(isCancelled()){
					//System.err.println("FormGen cancelled ");
					return null;
				}
		
				int numvars = FormulaTree.numVarsForThisRange(term.variableRange());

				//if valid term, get min set of true formulas
				if (numvars > 0){
					ArrayList<FormulaTree> f = handEliminationSearch(term);

					//add all
					for (FormulaTree t : f){
						formulaSet.put(t.outputTextFormula(), t);
						formulaCount++;
					}	
				}
			} //end this round of higher sizes

			//System.err.println(formulaCount + " formulas");
			formulaCount = 0;

			//update oldTerms for next round
			oldTerms = higherTerms.values();	

		}//end higher sizes

		trivial.removeAllTrivial(formulaSet);
		return formulaSet;		
	}

	
	//currently not used, calls get() from GUI thread after execution instead
	//@Override
	//public void done() {}


	/**
	 * A method that takes a SINGLE TERM as input, outputs min set of formulas for that term.
	 * This avoids redundancy at the level of quantification. 
	 * 
	 * @param term an unquantified formula
	 * @return a minimal set of true formulas that are quantified versions of the input formula
	 * @see aa.HandElimination
	 */
	public ArrayList<FormulaTree> handEliminationSearch(FormulaTree term){

		//min set to return
		ArrayList<FormulaTree> minSet = new ArrayList<FormulaTree>();

		int numVars = term.numVars();

		//redundant sanity check on term
		if (numVars == 0){return null;}
		
		//three kinds of quantifiers: universal, uniqueness, existential
		final int NUM_QUANTIFIERS = 3;

		//generate set of quantifier prefixes with the correct number of variables
		Set<int[]> qSet = HandElimination.makeCombinations(numVars, NUM_QUANTIFIERS);
		Set<Prefix> prefixes = HandElimination.generatePrefixSet(qSet);

		//debugging ints
		int prefixSetSize = prefixes.size();
		int prefixesInspected = 0;
		int prefixRemovalCount = 0;
						
		//main loop for removing redundant prefixes
		for (Prefix p : prefixes){
			if (p.included()){

				prefixesInspected ++;
				
				//construct formula and check truth value
				FormulaTree prefixTree = HandElimination.getQuantifierPrefix(p.vector());
				FormulaTree formula = new FormulaTree(prefixTree, term);
								
				//get truth value over these elements
				//why are elements here, aren't they known by Relations? 
				boolean formulaIsTrue;
				
				if (DEBUG){
					System.out.print(formula.outputTextFormula() + " ");
					formulaIsTrue = formula.debugValue(input.elements());
					System.out.println(formulaIsTrue+"\n\n");

				} else {
					formulaIsTrue = formula.value(input.elements());
				}

				if (formulaIsTrue){
					//add to minSet of formulas
					minSet.add(formula);

					//stop here if skipping hand elimination
					if (!useHandElimination){
						continue;
					}
					
					//get prefixes redundant to this one
					Set<int[]> redundantPrefixes = HandElimination.redundantPrefixes(p.vector());

					
					//removed, currently incorrect
					//get prefixes contradicting this one
					//Set<int[]> falsePrefixes = HandElimination.falsePrefixes(p.vector());

					//remove redundant prefixes
					HandElimination.betterRemove(prefixes, redundantPrefixes);
					
					//remove false prefixes, currently not implemented
					//HandElimination.betterRemove(prefixes, falsePrefixes);	
					
					//print both
					//System.out.println("false prefixes for formula " + formula.outputTextFormula());
					//printVectorSet(falsePrefixes);
					
					//System.out.println("redundant prefixes for formula " + formula.outputTextFormula());
					//printVectorSet(redundantPrefixes);
					
					//keep count
					prefixRemovalCount += redundantPrefixes.size();
					//prefixRemovalCount += falsePrefixes.size();
					
					
				} else {
					//else false, remove this prefix
					//all we really need to do here is NOT add, 
					//so do nothing
				}
			}
		}

		//System.out.println(prefixesInspected + " prefixes inspected");
		//System.out.println( (prefixSetSize - prefixesInspected) + " prefixes uninspected");

		return minSet;
	}


	


	/**
	 * A method to generate all predicates inhabited with variables.
	 * Input is a set of predicates and the maximum number of variables to use.
	 * output is an ArrayList of predicate objects.
	 * eg: input: (P(_,_), 2), output: <P(x,x), P(x,y), P(y,x), P(y,y)>
	 * 
	 * @param relations the set of relations in the input
	 * @param numVars the maximum number of variables to use
	 * @return an ArrayList of predicate objects
	 */
	public static ArrayList<Predicate> generatePredicates(ArrayList<Relation> relations, int numVars){
		ArrayList<Predicate> predicateSet = new ArrayList<Predicate>();

		for (Relation r : relations){
			//get all variable tuples, attach to relation name
			char[][] varTuples = fillVars(r.arity(), numVars);

			for (char[] tuple : varTuples){
				Predicate p = new Predicate(r, tuple);
				predicateSet.add(p);
			}
		}
		return predicateSet;
	}



	
	/**
	 * Returns table of variables for given arity & number of variables
	 * eg: for arity 2 and 2 variables, returns "[[x,x], [x,y], [y,x], [y,y]]" 
	 * 
	 * @param arity the size of tuples to generate 
	 * @param numVars the max number of variables to use in each tuple.
	 * @return all tuples of variables
	 */
	public static char[][] fillVars(int arity, int numVars){
		final char[] varNames = {'x','y','z','w'};
		int currentVar = 0;
		int varChangeCounter;
		int leftToRightColumnIndex;
		int numEntries = (int)Math.pow(numVars, arity);
		char[][] variableArray = new char[numEntries][arity];

		//outer loop for columns
		for (int i=0; i < arity; i++){
			currentVar = 0;
			leftToRightColumnIndex = arity - i - 1;
			varChangeCounter = (int) Math.pow(numVars,leftToRightColumnIndex);

			//inner loop for rows
			for (int j = 0; j< numEntries; j++){
				variableArray[j][i] = varNames[currentVar];

				//switch to next variable
				if ((j+1)%varChangeCounter == 0){
					currentVar = (currentVar +1) % numVars;
				}
			}
		}
		return variableArray; 
	}


	
	
	//TODO:what order are they added in? backwards?? *****
	
	/** Generates all subtrees of an operator and two predicates (or one predicate for negation).
	 *  For a given set of Predicates, makes all unquantified formulas with a single operator. 
	 * 	
	 * Does not require the "number of variables" parameter, this is relevant only at Predicate 
	 * generation time. 
	 * 
	 * Uses a simple scheme to avoid creating tautologies and redundant formulas: 
	 * Predicates are combined into pairs using an n x n matrix 
	 * (only the list of size n is actually created in memory):<p>
	 * avoid terms of the form "A & A" or "A -> A" by ignoring entries on the main diagonal<p>
	 * avoid redundant pairs like "A & B" and "B & A" by only taking the triangle above the main diagonal<p>
	 * 
	 * for conjunction: form all subtrees from upper triangle
	 * for disjunction: form all subtrees from upper triangle
	 * for biconditional: form all subtrees from upper triangle
	 * for implication: form all subtrees from upper and lower triangles
	 * for negation: all n subtrees 
	 * 
	 * @param predicateList an ArrayList of Predicates
	 * @return all subtree formulas
	 * 
	 */
	public static ArrayList<FormulaTree> generateSubtrees (ArrayList<Predicate> predicateList, 
			TrivialityTester trivial){
		ArrayList<FormulaTree> subtrees = new ArrayList<FormulaTree>();
		Operator[] operators = {new And(), new Or(), new Implies(), new Iff(), new Not()}; 
	
		
		int numPredicates = predicateList.size();
		Predicate leftPredicate, rightPredicate;

		for (Operator o : operators){
			if (o instanceof And || o instanceof Or || o instanceof Iff){
				//upper triangle only
				for (int i = 0;i < numPredicates-1; i++){
					for (int j = i+1; j < numPredicates; j++){
						leftPredicate = predicateList.get(i);
						rightPredicate = predicateList.get(j);
						FormulaTree subtree = new FormulaTree(o.getOperator(), new FormulaTree(leftPredicate), new FormulaTree(rightPredicate));
						if (!trivial.isTrivial(subtree)){
							subtrees.add(subtree);
						}
					}
				}
			}
			if (o instanceof Implies){
				//upper and lower triangle
				for (int i = 0; i < numPredicates; i++){
					for (int j=0; j < numPredicates; j++){
						if (i==j){
							continue;
						}
						//make new subtree rooted with operator o and these two children
						//add to subtrees arraylist
						leftPredicate = predicateList.get(i);
						rightPredicate = predicateList.get(j);
						FormulaTree subtree = new FormulaTree(new Implies(), new FormulaTree(leftPredicate), new FormulaTree(rightPredicate));
						
						//new
						if (trivial.predicateAlwaysFalse(rightPredicate)){
							//System.out.println("PREDICATE ALWAYS FALSE: " + rightPredicate.outputName());
							continue;
						}
						
						if (!trivial.isTrivial(subtree)){
							subtrees.add(subtree);
						}
					}
				}
			}
			if (o instanceof Not){
				//two node subtree, just (NOT) + (predicate)
				for (int i = 0; i < numPredicates; i++){
					rightPredicate = predicateList.get(i); //right child only
					//form new subtree rooted at NOT with a single child predicate on RIGHT, left child null
					FormulaTree subtree = new FormulaTree(new Not(), null, new FormulaTree(rightPredicate));
					subtrees.add(subtree);
				}
			} 
		} //end operators loop 
		return subtrees;
	}





	/**
	 * Separate method to generate formulas with 2 operators or more.
	 * This is called the first time as size2 = higherSizeFormulas(subtrees, subtrees), 
	 * the second time as size3 = higherSizeFormulas(size2, subtrees), and so on. 
	 * 
	 * Both input and output are formulas without quantifiers.
	 *	 
	 * @param sizeMinusOneTerms the set of all formulas of size s-1
	 * @param subtrees all possible one-operator formulas, see {@link #generateSubtrees(ArrayList)}
	 * @return a new set of formulas all of size s
	 */
	public Map<String, FormulaTree> higherSizeTerms(Collection<FormulaTree> sizeMinusOneTerms, ArrayList<FormulaTree> subtrees){
		//new terms to return
		Map<String, FormulaTree> newTerms = new LinkedHashMap<String, FormulaTree>();

		//main loop over smaller terms
		for (FormulaTree oldTerm : sizeMinusOneTerms){

			ArrayList<FormulaTree> leaves = getLeaves(oldTerm);
			
			for (FormulaTree leaf : leaves){
	
				//stop if cancelled by GUI
				if (isCancelled()){
					//System.err.println("FormulaGenerator cancelled at higher terms");
					return null;
				}
				
				Node toReplace = new Predicate((Predicate)leaf.root());
				
				for(FormulaTree subtree : subtrees){

					//double negation elimination
					if (subtree.root() instanceof Not && leaf.parent().root() instanceof Not){
						continue;
					}

					//replace designated leaf node with subtree
					leaf.setRoot(subtree.root());
					leaf.setLeft(subtree.left());
					leaf.setRight(subtree.right());

					//make new tree, update variable range, save
					FormulaTree newTerm = oldTerm.deepCopy();
					newTerm.updateRange();
					newTerms.put(newTerm.outputTextFormula(), newTerm);												
				}

				//replace the old predicate leaf
				//continue loop with any other leaves in this term
				leaf.setRoot(toReplace); 
				leaf.setLeft(null);
				leaf.setRight(null);										

			}

		} //end main loop 

		return newTerms;
	}


	
	
	

	/**
	 * Given a FormulaTree, return an ArrayList of all its leaf nodes
	 * @param t a FormulaTree 
	 * @return an ArrayList of all leaf nodes in t
	 */
	public static ArrayList<FormulaTree> getLeaves(FormulaTree t){
		
		ArrayList<FormulaTree> leaves = new ArrayList<FormulaTree>();

		Stack<FormulaTree> s = new Stack<FormulaTree>();
		s.add(t);

		//main DFS loop 
		while (!s.isEmpty()){
			FormulaTree currentNode = s.pop();
			if (currentNode.right() != null) s.add(currentNode.right());
			if (currentNode.left() != null) s.add(currentNode.left());	
			if (currentNode.root() instanceof Predicate){
				leaves.add(currentNode);
			}	
		} //end DFS

		return leaves; 
	}

	

	/**
	 * Given a collection of FormulaTrees representing subtrees, produce a deep copy.
	 * @param subtrees a collection of formulas 
	 * @return a deep copy of the collection
	 */
	public static ArrayList<FormulaTree> deepCopyTreeCollection(ArrayList<FormulaTree> subtrees){
		ArrayList<FormulaTree> treesCopy = new ArrayList<FormulaTree>();
		for (FormulaTree s : subtrees){
			treesCopy.add(s.deepCopy());
		}
		return treesCopy;
	}


	
	
	
	
	
	
	
	
	//DEBUGGING CODE
	
	
	
	//method that takes a SINGLE TERM as input, outputs min set of formulas for that term
	//not tested
	
	/**
	 * Debugging-focused version of {@link #handEliminationSearch(FormulaTree)}
	 * @param term the FormulaTree for an unquantified formula
	 * @return an ArrayList of true quantified formulas using term
	 */
	public ArrayList<FormulaTree> debugHandEliminationSearch(FormulaTree term){

		//min set to return
		ArrayList<FormulaTree> minSet = new ArrayList<FormulaTree>();

		int numVars = term.numVars();

		//redundant sanity check on term
		if (numVars == 0){return null;}
		
		//three kinds of quantifiers: universal, uniqueness, existential
		final int NUM_QUANTIFIERS = 3;

		//generate set of quantifier prefixes with the correct number of variables
		Set<int[]> qSet = HandElimination.makeCombinations(numVars, NUM_QUANTIFIERS);
		Set<Prefix> prefixes = HandElimination.generatePrefixSet(qSet);

		
		//prints
		System.out.println("\nHand Elimination for " + term.outputTextFormula());
		System.out.println("Start prefix set: ");
		System.out.println(HandElimination.prefixSetString(prefixes));
		
		
		//debugging ints
		int prefixSetSize = prefixes.size();
		int prefixesInspected = 0;
		int prefixRemovalCount = 0;
						
		//main loop for removing redundant prefixes
		for (Prefix p : prefixes){
			if (p.included()){

				prefixesInspected ++;
				
				//construct formula and check truth value
				FormulaTree prefixTree = HandElimination.getQuantifierPrefix(p.vector());
				FormulaTree formula = new FormulaTree(prefixTree, term);
								
				//get truth value over domain elements
				boolean formulaIsTrue;
				
				if (DEBUG){
					System.out.print(formula.outputTextFormula() + " ");
					formulaIsTrue = formula.debugValue(input.elements());
					System.out.println(formulaIsTrue+"\n\n");

				} else {
					formulaIsTrue = formula.value(input.elements());
				}

				if (formulaIsTrue){
					//add to minSet of formulas
					minSet.add(formula);

					//stop here if skipping hand elimination
					if (!useHandElimination){
						continue;
					}
					
					//get prefixes redundant to this one
					Set<int[]> redundantPrefixes = HandElimination.redundantPrefixes(p.vector());

					//remove redundant prefixes
					HandElimination.betterRemove(prefixes, redundantPrefixes);
					
					//keep count
					prefixRemovalCount += redundantPrefixes.size();
	
					
					//debug prints
					System.out.println(formula.outputTextFormula() + " " + formulaIsTrue);
					System.out.println("Redundant prefixes removed:");
					System.out.println(HandElimination.vectorSetString(redundantPrefixes));

					
				} else {
					//else false, remove this prefix
					//all we really need to do here is NOT add, 
					//so do nothing
				}
			}
		}

		System.out.println("Hand Elim complete.");
		System.out.println(prefixesInspected + " prefixes inspected");
		System.out.println( (prefixSetSize - prefixesInspected) + " prefixes uninspected" + "\n");

		return minSet;
	}

	
	
	
	
	/**
	 * Generate a set of formulas commonly found as axioms.
	 * 
	 * Produces expressions for all the relations in the input, covering typical algebraic
	 * properties. Applies only to relations with arity 3, these correspond to standard 
	 * arithmetic function that take two inputs and produce a single output.
	 * Eg, addition, normally written as "x + y = z", can be represented as "+(x,y,z) true".
	 * 
	 * <ul>
	 * <li>commutativity:   ∀x∀y∀z P(x,y,z) <-> P(y,x,z)  </li> 
	 * <li>associativity:  ∀x ∀y ∀z ∀u ∀v ∀w (*(y,z,u) & *(x,y,v) ) -> (*(v,z,w) <-> *(x,u,w)) </li>
	 * <li>closure:  ∀x∀y∃z P(x,y,z)  </li>						
	 * <li> left identity: ∃x∀y P(x,y,y)  </li>						
	 * <li> right identity: ∃x∀y P(y,x,y)  </li>					
	 * <li> left identity left inverse:∃x ∀y ∃z P(x,y,y) & P(z,y,x) </li>
	 * <li> left identity right inverse:∃x ∀y ∃z P(x,y,y) & P(y,z,x) </li>
	 * <li> right identity left inverse:∃x ∀y ∃z P(y,x,y) & P(z,y,x) </li>
	 * <li> right identity right inverse:∃x ∀y ∃z P(y,x,y) & P(y,z,x)  </li>
	 * <li>reflexivity ∀x R(x,x) </li>
	 * <li>symmetry ∀x ∀y R(x,y) <-> R(y,x)  </li>
	 * <li> transitivity  ∀x ∀y ∀z (R(x,y) & R(y,z)) -> R(x,z)</li>
	 * <li>antisymmetry ∀x ∀y (R(x, y) & R(y, x)) ⊃ (x = y)</li>
	 * <li> congruence  ∀x ∀y *(x,y) <-> *(y,x)</li>
	 * <li>transitivity of congruence ∀x ∀y ∀z ∀u ∀v ∀w (*(x,y) <-> *(z,u) & *(x,y) <-> *(v,w)) -> (*(z,u) <-> *(v,w))</li>
	 * </ul>
	 * 
	 * 
	 * @param relations
	 * @return
	 */
	public static Map<String, CommonAxiom> commonAxioms(ArrayList<Relation> relations, 
			ArrayList<String> elements){
		ArrayList<CommonAxiom> formulas = new ArrayList<CommonAxiom>();
		Map<String, CommonAxiom> formulaMap = new LinkedHashMap<String, CommonAxiom>();
		
		//generate axioms related to arithmetic
		for (Relation r : relations){
			if (r.arity()!= 3) {continue;}
			
			formulas.add(isAFunction(r));
			formulas.add(associativity(r)); 
			formulas.add(commutativity(r)); 
			formulas.add(closure(r)); 
			formulas.add(leftIdentity(r)); 
			formulas.add(rightIdentity(r)); 
			formulas.add(leftIdentityLeftInverse(r)); 
			formulas.add(leftIdentityRightInverse(r)); 
			formulas.add(rightIdentityLeftInverse(r)); 
			formulas.add(rightIdentityRightInverse(r)); 
		}
		
		
		//generate some axioms from geometry
		for (Relation r : relations){
			if (r.arity()!=2){continue;}
			formulas.add(antisymmetry(r));
			formulas.add(congruence(r));

			if (elements.size() <= 12){
				formulas.add(transitivityOfCongruence(r));
			}
		}
		
		//add equivalence relation properties
		for (Relation r : relations){
			if (r.arity() != 2){continue;}
			formulas.add(reflexivity(r));
			formulas.add(symmetry(r));
			formulas.add(transitivity(r));
		}
		
		
		//truth-value check everything, add anything true 
		int count = 0;
		for (CommonAxiom f : formulas){
			
			count++;
			//System.out.println(count + " " + f.outputTextFormula() + f.label());
			
			
			if (f.value(elements)){
				formulaMap.put(f.outputTextFormula(), f);
			}
		}
				
		
		return formulaMap;
	}
	
	
	

	
	/**
	 * Given a relation, return the formula expressing that the relation represents a binary function,
	 * i.e. P(x,y,z) represents some operation x*y = z, where each input (x,y) has a unique output z:
	 * ∀x ∀y ∃z ∀w (P (x, y, w) ≡ (w = z))
	 * @param r a relation
	 * @return a FormulaTree asserting that r represents a binary function
	 */
	public static CommonAxiom isAFunction(Relation r){
		//build prefix
		FormulaTree allX = new FormulaTree(new UniversalQuantifier('x'));
		FormulaTree allY = new FormulaTree(new UniversalQuantifier('y'));
		FormulaTree existsZ = new FormulaTree(new ExistentialQuantifier('z'));
		FormulaTree allW = new FormulaTree(new UniversalQuantifier('w'));
		
		//build operators
		FormulaTree iff = new FormulaTree(new Iff());
		FormulaTree equals = new FormulaTree(new Equals('w', 'z'));
		
		//predicate
		FormulaTree predicate = new FormulaTree(new Predicate(r, new char[]{'x','y','w'}));
		
		//construct tree
		allX.setRight(null);
		allX.setLeft(allY);
		allY.setRight(null);
		allY.setLeft(existsZ);
		existsZ.setRight(null);
		existsZ.setLeft(allW);
		allW.setRight(null);
		allW.setLeft(iff);
		iff.setLeft(predicate);
		iff.setRight(equals);
		equals.setRight(null);
		equals.setLeft(null);
		
		return new CommonAxiom(allX, r.name() + " represents a function");
	}
	
	
	
	/**
	 * Given a relation, return the formula expressing that the relation is associative. 
	 * The usual definition of associativity (x * (y * z) = (x * y) * z)) involves nesting
	 * of functions, something not really possible with the corresponding predicate respresentation. 
	 * 
	 * Given:<p>
	 * (x * (y * z) = (x * y) * z))<p>
	 * 
	 * Let:<p>
	 * y * z = u<p>
	 * x * y = v<p>
	 * 
	 * So now x * u = v * z, let x * u = v * z = w.
	 * 
	 * So the facts are: <p>
	 * y * z = u<p>
	 * x * y = v<p>
	 * x * u = w<p>
	 * v * z = w<p>
	 * 
	 * in predicate format:
	 * 
	 * *(y,z,u)<p>
	 * *(x,y,v)<p>
	 * *(x,u,w)<p>
	 * *(v,z,w)<p>
	 * 
	 * If * is associative, when the first two terms are true, the second two must be
	 * either both true or both false. So associativity takes the form:
	 * 
	 * (*(y,z,u) & *(x,y,v)) -> (*(v,z,w) <-> *(x,u,w))
	 * 
	 *
	 * Quantification: <p>
	 * This should work for all values of x,y,z (∀x ∀y ∀z)<p>
	 * 
	 * As for u,v, these will also be particular values (y*z and x*y respectively), 
	 * but the claim should be true for all values: either or both of u or v are
	 * an "incorrect" value, making *(y,z,u) or *(x,y,v) false), then the antecedent 
	 * of the conditional is false, making the claim true. Likewise, u,v are both
	 * "correct" values, the antecedent is true and the consequent must be so as well. <p>	 
	 *  
	 *  ∀x ∀y ∀z ∀u ∀v ∀w (*(y,z,u) & *(x,y,v) ) -> (*(v,z,w) <-> *(x,u,w))
	 *  
	 * @param r a particular relation
	 * @return a FormulaTree asserting associativity of r
	 */
	public static CommonAxiom associativity(Relation r){


		//build second prefix
		FormulaTree allX = new FormulaTree(new UniversalQuantifier('x'));
		FormulaTree allY = new FormulaTree(new UniversalQuantifier('y'));
		FormulaTree allZ = new FormulaTree(new UniversalQuantifier('z'));
		FormulaTree allW = new FormulaTree(new UniversalQuantifier('w'));
		FormulaTree allU = new FormulaTree(new UniversalQuantifier('u'));
		FormulaTree allV = new FormulaTree(new UniversalQuantifier('v'));
		
		//build operators
		FormulaTree and = new FormulaTree(new And());
		FormulaTree implies = new FormulaTree(new Implies());
		FormulaTree iff = new FormulaTree(new Iff());
		

		//build predicates
		FormulaTree yzu = new FormulaTree(new Predicate(r, new char[]{'y','z','u'}));
		FormulaTree xyv = new FormulaTree(new Predicate(r, new char[]{'x','y','v'}));
		FormulaTree xuw = new FormulaTree(new Predicate(r, new char[]{'x','u','w'}));
		FormulaTree vzw = new FormulaTree(new Predicate(r, new char[]{'v','z','w'}));


		allX.setRight(null);
		allX.setLeft(allY);
		allY.setRight(null);		
		allY.setLeft(allZ);
		allZ.setRight(null);
		allZ.setLeft(allU);
		allU.setRight(null);
		allU.setLeft(allV);
		allV.setRight(null);
		allV.setLeft(allW);
		allW.setRight(null);
		allW.setLeft(implies);
		
		implies.setLeft(and);
		implies.setRight(iff);
		
		and.setLeft(yzu);
		and.setRight(xyv);
		
		iff.setLeft(vzw);
		iff.setRight(xuw);
		
		//return top node
		return new CommonAxiom(allX, "associativity (" + r.name() + ")");
	}
	
	
	
	
	
	/**
	 * Given a relation, return the formula expressing that the relation is commutative
	 * @param r a relation
	 * @return a FormulaTree asserting commutativity of r
	 */
	public static CommonAxiom commutativity(Relation r){
		//build nodes
		FormulaTree allX = new FormulaTree(new UniversalQuantifier('x'));
		FormulaTree allY = new FormulaTree(new UniversalQuantifier('y'));
		FormulaTree allZ = new FormulaTree(new UniversalQuantifier('z'));
		FormulaTree iff = new FormulaTree (new Iff());
		FormulaTree left = new FormulaTree(new Predicate(r, new char[]{'x','y','z'}));
		FormulaTree right = new FormulaTree(new Predicate(r, new char[]{'y','x','z'}));
		
		//construct tree
		allX.setRight(null);
		allX.setLeft(allY);
		allY.setRight(null);
		allY.setLeft(allZ);
		allZ.setRight(null);
		allZ.setLeft(iff);
		iff.setLeft(left);
		iff.setRight(right);
		//predicate nodes already set null by constructor
		
		//return top node
		return new CommonAxiom(allX, "commutativity (" + r.name() + ")");
	}
	
	/**
	 * Given a relation, return the formula expressing that the relation has the closure property.
	 * @param r a relation
	 * @return a FormulaTree asserting commutativity of r
	 */
	public static CommonAxiom closure(Relation r){
		//build nodes
		FormulaTree allX = new FormulaTree(new UniversalQuantifier('x'));
		FormulaTree allY = new FormulaTree(new UniversalQuantifier('y'));
		FormulaTree existsZ = new FormulaTree(new ExistentialQuantifier('z'));
		FormulaTree closurePredicate = new FormulaTree(new Predicate(r, new char[]{'x','y','z'}));
		
		//construct tree
		allX.setRight(null);
		allX.setLeft(allY);
		allY.setRight(null);
		allY.setLeft(existsZ);
		existsZ.setRight(null);
		existsZ.setLeft(closurePredicate);

		//return top node
		return new CommonAxiom(allX, "closure (" + r.name() + ")");
	}
	
	

	
	
	
	
	/**
	 * Given a relation, return the formula expressing that the relation has a left identity element.
	 * ∃x ∀y P(x,y,y) .
	 *
	 * @param r a relation
	 * @return a FormulaTree asserting r has a left identity element.
	 */
	public static CommonAxiom leftIdentity(Relation r){
		//build nodes
		FormulaTree existsX = new FormulaTree(new ExistentialQuantifier('x'));
		FormulaTree allY = new FormulaTree(new UniversalQuantifier('y'));
		FormulaTree leftIdentity = new FormulaTree(new Predicate(r, new char[]{'x','y','y'}));
		
		//construct tree;
		existsX.setRight(null);
		existsX.setLeft(allY);
		allY.setRight(null);
		allY.setLeft(leftIdentity);
		
		//return top node
		return new CommonAxiom(existsX, "left identity (" + r.name() + ")");
	}
	
	
	
	
	/**
	 * Given a relation, return the formula expressing that the relation has a right identity element.
	 *  ∃x ∀y P(y,x,y).
	 * @param r a relation
	 * @return a FormulaTree asserting r has a right identity element.
	 */
	public static CommonAxiom rightIdentity(Relation r){
		//build nodes
		FormulaTree existsX = new FormulaTree(new ExistentialQuantifier('x'));
		FormulaTree allY = new FormulaTree(new UniversalQuantifier('y'));
		FormulaTree rightIdentity = new FormulaTree(new Predicate(r, new char[]{'x','y','x'}));
		
		//construct tree;
		existsX.setRight(null);
		existsX.setLeft(allY);
		allY.setRight(null);
		allY.setLeft(rightIdentity);
		
		//return top node
		return new CommonAxiom(existsX, "right identity (" + r.name() + ")");
	}
	

	
	/**
	 * Given a relation, return the formula expressing that the relation has left identity 
	 * and left inverse elements.
	 * ∃x ∀y ∃z ( *(x,y,y) & *(z,y,x)).
	 * 
	 * @param r a relation
	 * @return a FormulaTree asserting r has left identity, left inverse 
	 */
	public static CommonAxiom leftIdentityLeftInverse(Relation r){
		char[] leftIdentity = new char[]{'x','y','y'};
		char[] leftInverse = new char[]{'z','y','x'};

		return new CommonAxiom(identityInverseGenerator(r, leftIdentity, leftInverse), 
				"left identity, left inverse (" + r.name() + ")");
	}
	
	/**
	 * Given a relation, return the formula expressing that the relation has right identity 
	 * and left inverse elements.
	 * ∃x ∀y ∃z ( *(y,x,y) & *(z,y,x)).
	 * 
	 * @param r a relation
	 * @return a FormulaTree asserting r has left identity, left inverse 
	 */
	public static CommonAxiom rightIdentityLeftInverse(Relation r){
		char[] rightIdentity = new char[]{'y','x','y'};
		char[] leftInverse = new char[]{'z','y','x'};
		
		return new CommonAxiom(identityInverseGenerator(r, rightIdentity, leftInverse), 
				"right identity, left inverse (" + r.name() + ")");
	}
	
	/**
	 * Given a relation, return the formula expressing that the relation has left identity 
	 * and right inverse elements.
	 * ∃x ∀y ∃z ( *(x,y,y) & *(y,z,x)).
	 * 
	 * @param r a relation
	 * @return a FormulaTree asserting r has left identity, left inverse 
	 */
	public static CommonAxiom leftIdentityRightInverse(Relation r){
		char[] leftIdentity = new char[]{'x','y','y'};
		char[] rightInverse = new char[]{'y','z','x'};

		return new CommonAxiom(identityInverseGenerator(r, leftIdentity, rightInverse), 
				"left identity, right inverse (" + r.name() + ")");
	}
	
	/**
	 * Given a relation, return the formula expressing that the relation has right identity 
	 * and right inverse elements.
	 * ∃x ∀y ∃z ( *(y,x,y) & *(y,z,x)).
	 * 
	 * @param r a relation
	 * @return a FormulaTree asserting r has left identity, left inverse 
	 */
	public static CommonAxiom rightIdentityRightInverse(Relation r){
		char[] rightIdentity = new char[]{'y','x','y'};
		char[] rightInverse = new char[]{'y','z','x'};
		
		return new CommonAxiom(identityInverseGenerator(r, rightIdentity, rightInverse), 
				"right identity, right inverse (" + r.name() + ")");
	}
	
	/**
	 * Parent function to produce all four left/right identity, left/right inverse claims
	 * @param r
	 * @param identity the variable tuple for the identity predicate
	 * @param inverse the variable tuple for the inverse predicate
	 * @return a FormulaTree for the appropriate inverse/identity claim
	 */
	public static FormulaTree identityInverseGenerator(Relation r, char[] identity, char[] inverse){
		//build nodes
		FormulaTree existsX = new FormulaTree(new ExistentialQuantifier('x'));
		FormulaTree allY = new FormulaTree(new UniversalQuantifier('y'));
		FormulaTree existsZ = new FormulaTree(new ExistentialQuantifier('z'));
		FormulaTree and = new FormulaTree(new And());
		FormulaTree identityNode = new FormulaTree(new Predicate(r, identity));
		FormulaTree inverseNode = new FormulaTree(new Predicate(r, inverse));
		
		//construct tree
		existsX.setRight(null);
		existsX.setLeft(allY);
		allY.setRight(null);
		allY.setLeft(existsZ);
		existsZ.setRight(null);
		existsZ.setLeft(and);
		and.setLeft(identityNode);
		and.setRight(inverseNode);
		
		//return top node
		return existsX;
	}

	
	
	/**
	 * Given a relation, return the formula expressing the claim that the relation is reflexive. ∀x R(x,x) 
	 * @param r a Relation
	 * @return the FormulaTree asserting that r is reflexive
	 */
	public static CommonAxiom reflexivity(Relation r){
		//build nodes
		FormulaTree allX = new FormulaTree(new UniversalQuantifier('x'));
		FormulaTree predicate = new FormulaTree(new Predicate(r, new char[]{'x','x'}));
		
		//construct tree
		allX.setRight(null);
		allX.setLeft(predicate);
		
		//return top node
		return new CommonAxiom(allX, "reflexivity (" + r.name() + ")");
	}
	

	/**
	 * Given a relation, return the formula expressing the claim that the relation is symmetric: 
	 * ∀x ∀y R(x,y) <-> R(y,x) 
	 * @param r a Relation
	 * @return the FormulaTree asserting that r is symmetric
	 */
	public static CommonAxiom symmetry(Relation r){
		//build nodes
		FormulaTree allX = new FormulaTree(new UniversalQuantifier('x'));
		FormulaTree allY = new FormulaTree(new UniversalQuantifier('y'));
		FormulaTree xy = new FormulaTree(new Predicate(r, new char[]{'x','y'}));
		FormulaTree yx = new FormulaTree(new Predicate(r, new char[]{'y','x'}));
		FormulaTree iff = new FormulaTree(new Iff());
		
		//construct tree
		allX.setRight(null);
		allX.setLeft(allY);
		allY.setRight(null);
		allY.setLeft(iff);
		iff.setLeft(xy);
		iff.setRight(yx);
		
		//return top node
		return new CommonAxiom(allX, "symmetry (" + r.name() + ")");
	}
	
	
	/**
	 * Given a relation, return the formula expressing the claim that the relation is transitive: 
	 * ∀x ∀y ∀z (R(x,y) & R(y,z)) -> R(x,z)
	 * @param r a Relation
	 * @return the FormulaTree asserting that r is transitive
	 */
	public static CommonAxiom transitivity(Relation r){
		//build nodes
		FormulaTree allX = new FormulaTree(new UniversalQuantifier('x'));
		FormulaTree allY = new FormulaTree(new UniversalQuantifier('y'));
		FormulaTree allZ = new FormulaTree(new UniversalQuantifier('z'));
		FormulaTree implies = new FormulaTree(new Implies());
		FormulaTree and = new FormulaTree(new And());
		FormulaTree xy = new FormulaTree(new Predicate(r, new char[]{'x','y'}));
		FormulaTree yz = new FormulaTree(new Predicate(r, new char[]{'y','z'}));
		FormulaTree xz = new FormulaTree(new Predicate(r, new char[]{'x','z'}));
		
		//construct tree
		allX.setRight(null);
		allX.setLeft(allY);
		allY.setRight(null);
		allY.setLeft(allZ);
		allZ.setRight(null);
		allZ.setLeft(implies);
		implies.setRight(xz);
		implies.setLeft(and);
		and.setRight(yz);
		and.setLeft(xy);
		
		//return top node
		return new CommonAxiom(allX, "transitivity (" + r.name() + ")");
	}
	
	/**
	 * Given a relation, return the formula expressing the claim that the relation is antisymmetric: 
	 * ∀x ∀y (R(x, y) & R(y, x)) ⊃ (x = y)
	 * @param r a Relation
	 * @return the FormulaTree asserting that r is transitive
	 */
	public static CommonAxiom antisymmetry(Relation r){
		//build nodes
		FormulaTree allX = new FormulaTree(new UniversalQuantifier('x'));
		FormulaTree allY = new FormulaTree(new UniversalQuantifier('y'));
		FormulaTree implies = new FormulaTree(new Implies());
		FormulaTree and = new FormulaTree(new And());
		FormulaTree xy = new FormulaTree(new Predicate(r, new char[]{'x','y'}));	
		FormulaTree yx = new FormulaTree(new Predicate(r, new char[]{'y','x'}));	
		FormulaTree equal = new FormulaTree(new Equals('x', 'y'));
		
		//construct tree
		allX.setRight(null);
		allX.setLeft(allY);
		allY.setRight(null);
		allY.setLeft(implies);
		implies.setRight(equal);
		implies.setLeft(and);
		and.setLeft(xy);
		and.setRight(yx);
		
		//return top node
		return new CommonAxiom(allX, "antisymmetry (" + r.name() + ")");
	}
	
	
	/**
	 * Given a relation, return the formula expressing that the relation has the congruence
	 * property.
	 * 
	 * ∀x ∀y *(x,y) <-> *(y,x)
	 * 
	 * @param r a relation
	 * @return a FormulaTree asserting congruence of r
	 */
	public static CommonAxiom congruence(Relation r){
		//build nodes
		FormulaTree allX = new FormulaTree(new UniversalQuantifier('x'));
		FormulaTree allY = new FormulaTree(new UniversalQuantifier('y'));
		FormulaTree iff = new FormulaTree(new Implies());
		FormulaTree xy = new FormulaTree(new Predicate(r, new char[]{'x','y'}));
		FormulaTree yx = new FormulaTree(new Predicate(r, new char[]{'y','x'}));
		
		//construct tree
		allX.setRight(null);
		allX.setLeft(allY);
		allY.setRight(null);
		allY.setLeft(iff);
		iff.setLeft(xy);
		iff.setRight(yx);

		//return top node
		return new CommonAxiom(allX, "congruence (" + r.name() + ")");
	}
	

	
	/**
	 * Given a relation, return the formula expressing that the relation has the transitivity
	 * of congruence property:
	 * 
	 * ∀x ∀y ∀z ∀u ∀v ∀w (*(x,y) <-> *(z,u) & *(x,y) <-> *(v,w)) -> (*(z,u) <-> *(v,w))
	 * @param r a relation
	 * @return the FormulaTree expressing transitivity of congruence
	 */
	public static CommonAxiom transitivityOfCongruence(Relation r){
		//build nodes
		FormulaTree allX = new FormulaTree(new UniversalQuantifier('x'));
		FormulaTree allY = new FormulaTree(new UniversalQuantifier('y'));
		FormulaTree allZ = new FormulaTree(new UniversalQuantifier('z'));
		FormulaTree allU = new FormulaTree(new UniversalQuantifier('u'));
		FormulaTree allV = new FormulaTree(new UniversalQuantifier('v'));
		FormulaTree allW = new FormulaTree(new UniversalQuantifier('w'));

		FormulaTree iff1 = new FormulaTree(new Iff());
		FormulaTree iff2 = new FormulaTree(new Iff());
		FormulaTree iff3 = new FormulaTree(new Iff());
		FormulaTree and = new FormulaTree(new And());
		FormulaTree implies = new FormulaTree(new Implies());
		FormulaTree xy1 = new FormulaTree(new Predicate(r, new char[]{'x','y'}));
		FormulaTree xy2 = new FormulaTree(new Predicate(r, new char[]{'x','y'}));
		FormulaTree zu1 = new FormulaTree(new Predicate(r, new char[]{'z','u'}));
		FormulaTree vw1 = new FormulaTree(new Predicate(r, new char[]{'v','w'}));
		FormulaTree zu2 = new FormulaTree(new Predicate(r, new char[]{'z','u'}));
		FormulaTree vw2 = new FormulaTree(new Predicate(r, new char[]{'v','w'}));
	
		//construct tree
		allX.setRight(null);
		allX.setLeft(allY);
		allY.setRight(null);
		allY.setLeft(allZ);
		allZ.setRight(null);
		allZ.setLeft(allU);
		allU.setRight(null);
		allU.setLeft(allV);
		allV.setRight(null);
		allV.setLeft(allW);
		allW.setRight(null);
		allW.setLeft(implies);
		implies.setRight(iff3);
		iff3.setLeft(zu2);
		iff3.setRight(vw2);
		implies.setLeft(and);
		and.setLeft(iff1);
		and.setRight(iff2);
		iff1.setLeft(xy1);
		iff1.setRight(zu1);
		iff2.setLeft(xy2);
		iff2.setRight(vw1);
	
		//return top node
		return new CommonAxiom(allX, "transitivity of congruence(" + r.name() + ")" );
	}
	
}

