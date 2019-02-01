package aa;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Iterator;
import java.util.Map;
import java.util.LinkedHashMap;
import java.util.Set;

import javax.swing.SwingWorker;


/* old FormGen
 * create all predicate terms P
 * create all subtrees S
 * 
 * size zero is P + quantifiers 
 * size one is S + quantifiers
 * size two is tree sugery on size one
 * etc.
 * 
 * given an unquantified formula f:
 * 		check the variable range
 * 		if valid, attach appropriate sized quantifier prefixes
 * 
 * 
 * Typed Formula Generation
 * 
 * predicates are the same! The type constraint is stored in the parent relation, 
 * so no changes to predicates are needed
 * subtrees the same
 * 
 * 
 * given an unquantified formula f:
 * 		check variable range
 * 		if valid, attach appropriate sized quantifier prefixes
 * 
 *  	number of quantifiers no longer fixed at three
 *  	there will now be 3 * (number of types) 
 *  	do simple Cartesian product of quantifiers and types to generate
 *  	attach as normal
 *  
 *  	(faster, but worse code: 
 *  	type equivalent of "variable range": check all types present and use only those
 *  	... but this is probably not helpful, since type order matters also)
 *  
 *  
 *  	Then type-check resulting trees: recursive search with substitutions almost exactly like 
 *  	truth-value checking 
 * 
 * 		to start: figure out how the old one works! it's not immediately obvious
 * 
 * 		easier: 
 * 		unquantified formula f
 * 		generate regular prefix set Q as usual
 * 		make cartesian product of Q x T, add all
 *  
 *  	prefix objects are turned into quantifier prefix trees by FormulaGenerator.getQuantifierPrefix()
 *  	
 *  	this calls further accessory methods to attach the appropriate number of quantifiers
 *  
 *  	can call HandElimination.makeCombinations() to get collection of all vectors over a particular number of elements
 *  	can generate typed prefixes this way, by numbering typed quantifiers appropriately
 *  	
 *  	problem: number of types will not be known at runtime. 
 *  	
 *  	with two types, have 3 x 2 = 6 typed quantifiers. 
 *   	with three types, have 3 x 3 = 9 typed quantifiers. 
 *   	with t types, have 3t typed quantifiers
 *  	with t types and v vars, have 3*v*t quantifier prefixes 
 *  
 *  
 *  		Set<int[]> qSet = HandElimination.makeCombinations(numVars, NUM_QUANTIFIERS);
 *  		Set<Prefix> prefixes = HandElimination.generatePrefixSet(qSet);
 * 
 *  	get set of all 3 quantifiers
 *  	get set of all types
 *  	do cross product
 *  	those are your quantifiers to choose from 
 *  
 * 
 * 	make TypedPrefix type that has two vectors: one for quantifiers, the other for types
 * 	to make them, make all quantifier prefixes as usual, then use combo code to make a type vector
 * 	of the same length (will need to enumerate types somehow. No! they are already ordered in the input.types() collection.) 
 *  Then do cartesian product of both, and 
 * 	create a TypedPrefix for each one. The write a new TypedPrefix -> FormulaTree method and the type 
 * 	checking method. Done!
 * 
 */




/**
 * Formula Generator for Typed Formulas
 * @see {aa.FormulaGenerator}
 *
 */
public class TypedFormulaGenerator extends SwingWorker<Map<String, FormulaTree>, Void> {

	//input from file
	private Input input;

	//formula set to return
	private Map<String, FormulaTree> formulaSet;

	//Relations for untyped translations of typed expressions
	private ArrayList<Relation> translatedTypes;

	//Union of all the typed elements
	private ArrayList<String> untypedElements;

	private TrivialityTester trivial;
	
	private final boolean DEBUG = false;

	//three untyped quantifiers: universal, existential, uniqueness
	final int NUM_QUANTIFIERS = 3;

	public TypedFormulaGenerator(Input i){
		super();
		input = i;
		formulaSet = new LinkedHashMap<String, FormulaTree>();
		translatedTypes = translateTypesToRelations(input.types());
		untypedElements = untypeElements(input.types());
		trivial = new TrivialityTester(untypedElements);
	}

	/**
	 * Background task for typed formula generation
	 * @return a HashMap of all formulas
	 */
	@Override
	public Map<String, FormulaTree> doInBackground() {					
		//System.err.print("Typed Formula Generation: ");
		
		//tell GUI we are starting
		firePropertyChange("typed generation", 0, 1);
		
		
		int formulaCount = 0;
		int numTypes = input.types().size();
		if (numTypes == 0){
			System.err.println("Error, TypedFormulaGenerator called on untyped input");
		}

		//read data from input
		int varLimit = input.varLimit();
		int sizeLimit = input.sizeLimit();
		
		//remove
		//System.out.println(formulaSet.size() + " existence claims generated.");
		
		
		//.................................................................

		
		//add type existence claims
		formulaSet.putAll(typeExistenceClaims());

		//add common mathematical axioms
		if (input.searchCommonAxioms()){

			firePropertyChange("common", -1, 0);
			
			Map<String, CommonAxiom> commonAxioms = commonAxioms(input.relations());
			trivial.removeAllTrivialAxioms(commonAxioms);
			formulaSet.putAll(commonAxioms);

//			System.out.println("generated " + commonAxioms.size() + " common axioms");
//			for (CommonAxiom t : commonAxioms.values()){
//				System.out.println("   " + t.outputTextFormula());
//				System.out.println("   " + t.outputProverFormula());
//				System.out.println(t.label()+ "\n");
//			}
		}
		
		//all predicates (size zero terms)
		ArrayList<Predicate> predicates = FormulaGenerator.generatePredicates(input.relations(), varLimit);

		//remove
		//System.err.println("generated " + predicates.size() + " predicates");

		//tell GUI we are building size zero formulas
		firePropertyChange("typed generation", 0, 1);

		//same message to standard error  (remove)
		//System.err.print("generating typed size 0: ");

		//generate and verify size zero formulas
		//loop over all predicates
		for (Predicate p : predicates){
			int numvars = FormulaTree.numVarsForThisRange(p.variableRange());

			//if valid term
			if (numvars > 0){
				//wrap this predicate in a FormulaTree
				FormulaTree pTree = new FormulaTree(p);

				//add quantifiers, type-check, translate to untyped, truth-value check	
				Map<String, FormulaTree> formulas = generateFormulas(pTree, numvars);

				//add all
				for (FormulaTree t : formulas.values()){
					formulaSet.put(t.outputTextFormula(), t);
					formulaCount++;
				}
			}
		}

		//show number of size zero formulas
	//	System.err.println(formulaCount + " formulas");
		formulaCount = 0;

		if (sizeLimit < 1) {
			return formulaSet;
		}

		//tell GUI we are building size 1
		firePropertyChange("typed generation", 1, 2);

		//same message to standard error				//TODO: remove
		//System.err.print("generating size 1: ");


		//all possible one-operator subtree terms, over all predicates (size one terms)
		ArrayList<FormulaTree> subtrees = FormulaGenerator.generateSubtrees(predicates, trivial);

		//remove
		//System.err.println("generated " + subtrees.size() + " subtrees");

		//generate size one terms
		//loop over all subtree terms (nodes with one or two children)
		for (FormulaTree term : subtrees){

			//stop if cancelled by GUI
			if (isCancelled()){								
				//System.err.println("Typed FormGen cancelled ");
				return null;
			}

			int numvars = FormulaTree.numVarsForThisRange(term.variableRange());

			//if valid variable range, get min set of true formulas for this term
			if (numvars > 0){

				//add quantifiers, type-check, remove types, truth-value check	
				Map<String, FormulaTree> formulas = generateFormulas(term, numvars);

				//add all
				for (FormulaTree t : formulas.values()){
					formulaSet.put(t.outputTextFormula(), t);
					formulaCount++;
				}			
			}
		}


		//REMOVE
		//System.err.println(formulaCount + " formulas");
		formulaCount = 0;

		if (sizeLimit < 2) {
			return formulaSet;}

		//older terms to iterate over, declare outside of loop 
		Collection<FormulaTree> oldTerms = FormulaGenerator.deepCopyTreeCollection(subtrees);

		for (int size = 2; size <= sizeLimit; size++){

			//update GUI 
			firePropertyChange("typed generation", size, size+1);

			//same message to standard error  (remove)
			//System.err.print("generating size " + size + ": ");

			Map<String, FormulaTree> higherTerms = higherSizeTerms(oldTerms, subtrees);

			//System.err.println("higher size " + size + " num formulas: " + higherTerms.size());
			trivial.removeAllTrivial(higherTerms);
			//System.err.println("higher size after trivial: " + higherTerms.size());
			
			for (FormulaTree term : higherTerms.values()){

				//stop if cancelled by GUI
				if(isCancelled()){
				//	System.err.println("Typed FormGen cancelled ");
					return null;
				}

				int numvars = FormulaTree.numVarsForThisRange(term.variableRange());

				//if valid term
				if (numvars > 0){

					//add quantifiers, type-check, remove types, truth-value check	
					Map<String, FormulaTree> formulas =	generateFormulas(term, numvars);

					//add all
					for (FormulaTree t : formulas.values()){
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

		//stop if cancelled by GUI
		if(isCancelled()){
			//System.err.println("Typed FormGen cancelled ");
			return null;
		}
		
		trivial.removeAllTrivial(formulaSet);
		return formulaSet;
		
	}

	
	
	 
	
	
	
	
	
	


	public ArrayList<FormulaTree> getTypedPrefixes(Set<int[]> quantifierPrefixSet, Set<int[]> typePrefixSet) {
		ArrayList<FormulaTree> prefixes = new ArrayList<FormulaTree>();

		for (int[] qprefix : quantifierPrefixSet){
			for (int[] typeprefix : typePrefixSet){
				FormulaTree f = getTypedPrefixTree(qprefix, typeprefix);
				prefixes.add(f);	
			}
		}
		return prefixes;
	}


	public FormulaTree getTypedPrefixTree(int[] qprefix, int[] typeset){
		switch(qprefix.length){
		case 1: return getTypedPrefix1(qprefix, typeset);
		case 2: return getTypedPrefix2(qprefix, typeset);
		case 3: return getTypedPrefix3(qprefix, typeset);
		case 4: return getTypedPrefix4(qprefix, typeset);
		default: System.err.println("quantifier prefix error");
		}
		return null;
	}


	/**
	 * Given quantifier and type vectors, returns a typed quantifier prefix over one variable.
	 * @param qVector
	 * @param typeVector
	 * @return a FormulaTree quantifier prefix
	 */
	public FormulaTree getTypedPrefix1(int[] qVector, int[] typeVector){
		return new FormulaTree(getTypedQuantifierWithVar(qVector[0], input.types().get(typeVector[0]), 'x'));
	}


	/**
	 * Given quantifier and type vectors, returns a typed quantifier prefix over two variables.
	 * @param 
	 * @param
	 * @return a FormulaTree quantifier prefix
	 */
	public  FormulaTree getTypedPrefix2(int[] qVector, int[] typeVector){
		FormulaTree qx = new FormulaTree(getTypedQuantifierWithVar(qVector[0], input.types().get(typeVector[0]), 'x'));
		FormulaTree qy = new FormulaTree(getTypedQuantifierWithVar(qVector[1], input.types().get(typeVector[1]), 'y'));

		qx.setLeft(qy);
		return qx;
	}

	/**
	 * Given quantifier and type vectors, returns a typed quantifier prefix over three variables.
	 * @param 
	 * @param 
	 * @return a FormulaTree quantifier prefix
	 */
	public FormulaTree getTypedPrefix3(int[] qVector, int[] typeVector){
		FormulaTree qx = new FormulaTree(getTypedQuantifierWithVar(qVector[0], input.types().get(typeVector[0]), 'x'));
		FormulaTree qy = new FormulaTree(getTypedQuantifierWithVar(qVector[1], input.types().get(typeVector[1]), 'y'));
		FormulaTree qz = new FormulaTree(getTypedQuantifierWithVar(qVector[2], input.types().get(typeVector[2]), 'z'));

		qx.setLeft(qy);
		qy.setLeft(qz);
		return qx;
	}

	/**
	 * Given quantifier and type vectors, returns a typed quantifier prefix over four variables.
	 * @param 
	 * @param 
	 * @return a FormulaTree quantifier prefix
	 */
	public FormulaTree getTypedPrefix4(int[] qVector, int[] typeVector){
		FormulaTree qx = new FormulaTree(getTypedQuantifierWithVar(qVector[0], input.types().get(typeVector[0]), 'x'));
		FormulaTree qy = new FormulaTree(getTypedQuantifierWithVar(qVector[1], input.types().get(typeVector[1]), 'y'));
		FormulaTree qz = new FormulaTree(getTypedQuantifierWithVar(qVector[2], input.types().get(typeVector[2]), 'z'));
		FormulaTree qw = new FormulaTree(getTypedQuantifierWithVar(qVector[3], input.types().get(typeVector[3]), 'w'));

		qx.setLeft(qy);
		qy.setLeft(qz);
		qz.setLeft(qw);
		return qx;
	}



	/**
	 * Given a set of quantifier prefix trees and a single predicate, return all possible combinations
	 * as a set of FormulaTree objects.
	 * @param prefixes
	 * @param p
	 * @return
	 */
	public Map<String, FormulaTree> getAllFormulas(ArrayList<FormulaTree> prefixes, FormulaTree term){
		Map<String, FormulaTree> formulas = new LinkedHashMap<String, FormulaTree>();
		for (FormulaTree prefix : prefixes){
			FormulaTree t = new FormulaTree(prefix, term);
			formulas.put(t.outputTextFormula(), t);
		}
		return formulas;
	}



	public static TypedQuantifier getTypedQuantifierWithVar(int q, Type t, char v){
		switch(q){
		case 0: return new TypedUniversalQuantifier(t,v);
		case 1: return new TypedUniquenessQuantifier(t,v);
		case 2: return new TypedExistentialQuantifier(t,v);
		default: System.err.println("quantifier error");
		}
		return null;	
	}


	/**
	 * Given a set of formulas, remove badly-typed formulas in-place.
	 * @param formulas a collection of formulas to type check
	 */
	public void typeCheckAll(Map<String, FormulaTree> formulas){
		Iterator<FormulaTree> iter = formulas.values().iterator();
		FormulaTree f;

		while (iter.hasNext()){
			f = iter.next();
			if(!isWellTypedFormula(f)){
				iter.remove();
			}			
		}
	}



	/**
	 * Formula Type checking, returns true for a correctly typed formula. 
	 * @param f
	 * @return
	 */
	public boolean isWellTypedFormula(FormulaTree f){
		//get typing for all variables
		Map<Character, Type> varTypes = getVarTypes(f);

		//get all predicate nodes in this formula
		ArrayList<FormulaTree> leaves = FormulaGenerator.getLeaves(f);

		//check all 
		for(FormulaTree l : leaves){
			if (!isWellTyped(varTypes, l)){return false;}
		}
		return true;
	}

	/**
	 * Given a FormulaTree, iterate through the quantifiers and assign
	 * the corresponding type to each variable. 
	 * @param f a FormulaTree
	 * @return a mapping of variables to Types
	 */
	public Map<Character, Type> getVarTypes(FormulaTree f){
		Map<Character, Type> varTypes = new LinkedHashMap<Character, Type>();
		TypedQuantifier tq = null;
		while(f.root() instanceof TypedQuantifier){
			tq = (TypedQuantifier) f.root();
			varTypes.put(tq.variable(), tq.type());
			f = f.left();
		}
		return varTypes;
	}


	/**
	 * Type checking for a single tree node enclosing a Predicate.
	 * Returns true if the variables in the Predicate match their required types. 
	 * @param varTypes a mapping of variables to types
	 * @param f a FormulaTree with a single Predicate node
	 * @return true if the variables in the predicate meet the type constraints
	 */
	public boolean isWellTyped(Map<Character, Type> varTypes, FormulaTree f){
		Type varType, constraintType;
		Predicate p = (Predicate) f.root();
		
		//get variable tuple from Predicate
		char[] varTuple = p.varTuple();
		
		//get constraint tuple from the parent Relation
		ArrayList<Type> constraint = p.parentRelation().constraint();
		
		//anything with no type constraint is well-typed
		if (constraint == null){
			return true;
		}
		
		int length = varTuple.length;

		//get each variable type and constraint type, check if they match
		for (int i = 0; i < length; i++){
			varType = varTypes.get(varTuple[i]);
			constraintType = constraint.get(i);

			if (!varType.matchesType(constraintType)){
				return false;
			}
		}
		return true;
	}

	//TODO: handle common axioms, preserve labels
	public Map<String, FormulaTree> translateAllToUntyped(Map<String, FormulaTree> formulas){
		Map<String, FormulaTree> untyped = new LinkedHashMap<String, FormulaTree>();

		for(FormulaTree typed: formulas.values()){
			FormulaTree ut = translateToUntyped(typed);
			untyped.put(ut.outputTextFormula(), ut);
		}
		return untyped;
	}

	/**
	 * Translates a typed formula into an untyped one.
	 * Calls recursive function {@link #translateToUntypedRecurse(FormulaTree, Map)}.
	 * @param typed
	 * @return
	 */
	public FormulaTree translateToUntyped(FormulaTree typed){
		Map<Character, Type> varTypes = new LinkedHashMap<Character, Type>();
		return translateToUntypedRecurse(typed, varTypes);
	}


	/**
	 * Translates a typed expression into an equivalent untyped one.
	 * Types are translated into Relations (specifically into Predicate terms)
	 * Typed quantifiers are translated into equivalent untyped ones. 
	 * Then new expressions are constructed according to the equivalences: 
	 * <ul>
	 * <li>(∀ x : T) P(x) ==> (∀x T(x) -> P(x))</li>
	 * <li>(∃x : T) P(x)  ==> (∃x T(x) & P(x))</li>
	 * <li>(∃!x : T) P(x) ==> (∃!x T(x) & P(x))</li>			TODO: is this notation correct?		
	 * </ul>
	 * @param typed a FormulaTree with Types
	 * @param varTypes a mapping of variable types
	 * @return the FormulaTree for an equivalent untyped expression
	 */
	public FormulaTree translateToUntypedRecurse(FormulaTree typed, Map<Character, Type> varTypes){
		//new tree to construct
		FormulaTree t = new FormulaTree();

		Node node = typed.root();
		Type type;
		char var;

		//quantifier cases
		if (node instanceof TypedQuantifier){
			//get variable for this quantifier
			var = ((TypedQuantifier) node).variable();

			//get type for this quantifier
			type = ((TypedQuantifier) node).type();

			//update var |-> type mapping
			varTypes.put(var, type);

			//new untyped quantifier, to be determined by cases below
			Quantifier q = null;

			//new operator, determined by cases below
			Operator o = null;

			//new predicate term, same for all cases
			FormulaTree pNode = translatedPredicateNode(type, var);

			if (node instanceof TypedUniversalQuantifier){
				//make a matching untyped quantifier
				q = new UniversalQuantifier(var);

				//new implication operator
				o = new Implies();
			}

			if (node instanceof TypedUniquenessQuantifier){
				//make a matching untyped quantifier
				q = new UniquenessQuantifier(var);

				//new conjunction operator
				o = new And();
			}

			if (node instanceof TypedExistentialQuantifier){
				//make a matching untyped quantifier
				q = new ExistentialQuantifier(var);

				//new conjunction operator
				o = new And();
			}

			//wrap operator in FormulaTree object
			FormulaTree oNode = new FormulaTree(o);

			//assemble tree and recurse
			t.setRoot(q);
			t.setRight(null);				
			t.setLeft(oNode);
			oNode.setLeft(pNode);
			oNode.setRight(translateToUntypedRecurse(typed.left(), varTypes));

		} else {

			//else copy unchanged
			t.setRoot(node);

			//recurse on left and right
			if (typed.left() != null) {
				t.setLeft(translateToUntypedRecurse(typed.left(), varTypes));
			}
			if (typed.right() != null) {
				t.setRight(translateToUntypedRecurse(typed.right(), varTypes));
			}
		}
		return t;
	}


	/**
	 * Convert Types in the input into Relations.
	 * This is required to convert typed expressions into untyped ones:
	 * For each type T in the input with elements {a, b, c...}, create a 
	 * Relation R with the same name as T, with facts R(a), R(b), R(c)...
	 * @return a collection of Relations
	 */
	public static ArrayList<Relation> translateTypesToRelations(ArrayList<Type> typeCollection){
		ArrayList<Relation> newRelations = new ArrayList<Relation>();
		for (Type t: typeCollection){
			Relation r = new Relation(t.name()); 

			//all Types have arity 1
			r.setArity(1);

			//convert elements to facts for this relation
			for (String e : t.elements()){
				ArrayList<String> fact = new ArrayList<String>();
				fact.add(e);
				r.addFact(fact);
			}
			newRelations.add(r);
		}
		return newRelations;
	}

	/**
	 * Given a Type object, return the matching Relation.
	 * Used for translating typed formulas into untyped ones.
	 * @param t a Type
	 * @return a Relation
	 */
	public Relation getTranslatedRelation(Type t){
		for (Relation r : translatedTypes){
			if (t.name().equals(r.name())){
				return r;
			}
		}
		return null;
	}


	/**
	 * Given a Type T and a variable v, return a FormulaTree with a single 
	 * predicate node for the term T(v)
	 * @param type
	 * @param var
	 * @return
	 */
	public FormulaTree translatedPredicateNode(Type type, char var){
		//make singleton variable tuple
		char[] varTuple = new char[]{var};

		//get parent relation for predicate
		Relation r = getTranslatedRelation(type);

		//make predicate and package into FormulaTree
		Predicate p = new Predicate(r, varTuple);
		return new FormulaTree(p);		
	}


	/**
	 * do truth-value checking in-place, discard anything false
	 * @param formulas
	 */
	public void truthValueCheckAll(Map<String, FormulaTree> formulas){
		Iterator<FormulaTree> iter = formulas.values().iterator();
		FormulaTree f;

		//iterate and remove anything false
		while (iter.hasNext()){
			f = iter.next();
			if (!(f.value(untypedElements))){
				iter.remove();
			}
		}
	}

	/**
	 * Collect all typed elements into a single untyped collection
	 * @return
	 */
	public static ArrayList<String> untypeElements(ArrayList<Type> typeCollection){
		ArrayList<String> untyped = new ArrayList<String>();
		for (Type t: typeCollection){
			untyped.addAll(t.elements());
		}
		return untyped;
	}



	/**
	 * Separate method to generate higher-size terms from smaller ones. 
	 * @see {FormulaGenerator#higherSizeTerms(Collection, ArrayList)}.
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

			//stop if cancelled by GUI
			if (isCancelled()){
			//	System.err.println("Typed FormulaGenerator cancelled at higher terms");
				return null;
			}

			ArrayList<FormulaTree> leaves = FormulaGenerator.getLeaves(oldTerm);

			for (FormulaTree leaf : leaves){

				Node toReplace = new Predicate((Predicate)leaf.root());

				for (FormulaTree subtree : subtrees){

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
	 * Given an unquantified, typed expression, return all formulas possible by adding quantification.
	 * @param unquantified an unquantified formula
	 * @param numvars the variable search limit
	 * @return a collection of formulas
	 */
	public Map<String, FormulaTree> generateFormulas(FormulaTree unquantified, int numvars){
		int numTypes = input.types().size();

		//get all vectors for variables and types
		Set<int[]> quantifierPrefixSet = HandElimination.makeCombinations(numvars, NUM_QUANTIFIERS);
		Set<int[]> typePrefixSet = HandElimination.makeCombinations(numvars, numTypes);

		//get all possible typed prefixes as FormulaTrees
		ArrayList<FormulaTree> prefixes = getTypedPrefixes(quantifierPrefixSet, typePrefixSet);

		//combine all prefixes with the unquantified term 
		Map<String, FormulaTree>formulas = getAllFormulas(prefixes, unquantified);

		//typecheck in-place, remove anything badly typed
		typeCheckAll(formulas);

		//stop if nothing left after typechecking
		if (formulas.size() == 0){return formulas;}
		
		//translate to untyped
		Map<String, FormulaTree> translated = translateAllToUntyped(formulas);

		//truth-value checking in-place, discard anything false	
		truthValueCheckAll(translated);

		return translated;
	}

	/**
	 * Generate bare existence claims for each type in the input. 
	 * For each type T and its translated relation T(), generate the claims ∃x T(x)
	 * and ∃!x T(x).
	 * @return a FormulaTree collection of existence claims
	 */
	public Map<String, FormulaTree> typeExistenceClaims(){
		Map<String, FormulaTree> formulas = new LinkedHashMap<String, FormulaTree>();
		
		//for each unary relation R describing a type, form the untyped expression ∃x R(x)
		//these are all known to be true, since types must be occupied
		for (Relation r : translatedTypes){
			FormulaTree exists = new FormulaTree(new ExistentialQuantifier('x'));
			FormulaTree predicate = new FormulaTree(new Predicate(r, new char[]{'x'}));
			exists.setRight(null);
			exists.setLeft(predicate);
			formulas.put(exists.outputTextFormula(), exists);
		}
		
		//for each unary relation R describing a type, form the untyped expression ∃!x R(x)
		//these need to have their truth values checked
		for (Relation r : translatedTypes){			
			FormulaTree unique = new FormulaTree(new UniquenessQuantifier('x'));
			FormulaTree predicate = new FormulaTree(new Predicate(r, new char[]{'x'}));
			unique.setRight(null);
			unique.setLeft(predicate);
			
			//add if true
			if (unique.value(untypedElements)){
				formulas.put(unique.outputTextFormula(), unique);
			}
		}
		
		return formulas;
	}

	
	/**
	 * Generate Formulas for common mathematical axioms. 
	 * In some cases typing restrictions are inferred from the axioms to avoid generating
	 * too many useless formulas. 
	 * @see {FormulaGenerator{@link #commonAxioms(ArrayList)}
	 * @param relations
	 * @return a collection of common axioms that are true for the input
	 */
	Map<String, CommonAxiom> commonAxioms(ArrayList<Relation> relations){
		Map<String, CommonAxiom> common = new LinkedHashMap<String, CommonAxiom>();
		
		//arity 3 axioms related to groups
		for (Relation r : relations){
			if (r.arity() != 3){continue;}
			common.putAll(commutativity(r));
			common.putAll(associativity(r));
			common.putAll(closure(r));
			common.putAll(leftIdentity(r));
			common.putAll(rightIdentity(r));
			common.putAll(leftIdentityLeftInverse(r));
			common.putAll(rightIdentityLeftInverse(r));
			common.putAll(leftIdentityRightInverse(r));
			common.putAll(rightIdentityRightInverse(r));
		}

		//arity 2 axioms related to geometry
		for (Relation r : relations){
			if (r.arity() != 2){continue;}
			common.putAll(antisymmetry(r));
			common.putAll(transitivityOfCongruence(r));
		}
		
		//arity 2 equivalence relation properties
		for (Relation r : relations){
			if (r.arity() != 2){continue;}
			common.putAll(reflexivity(r));
			common.putAll(symmetry(r));
			common.putAll(transitivity(r));
		}
				
		return common;
	}

	
	
	
	

	
	//arity 3 ------------------------
	

	//∀x∀y∀z P(x,y,z) <-> P(y,x,z) 
	//x,y same type, z free
	/**
	 * Given a Relation, generate the formula that claims the relation represents a 
	 * commutative operation: ∀x∀y∀z P(x,y,z) <-> P(y,x,z).
	 * x,y are assumed to be the same type, with z free. 
	 * 
	 * @param r a Relation
	 * @return a collection of commutativity claims 
	 */
	public Map<String, CommonAxiom> commutativity(Relation r){
		Map<String, FormulaTree> formulas = new LinkedHashMap<String, FormulaTree>();
		
		//build all prefixes, combine all with unquantified term
		for (Type t1 : input.types()){
			for (Type t2 : input.types()){
				//build quantifier prefix
				FormulaTree allX = new FormulaTree(new TypedUniversalQuantifier(t1, 'x'));
				FormulaTree allY = new FormulaTree(new TypedUniversalQuantifier(t1, 'y'));
				FormulaTree allZ = new FormulaTree(new TypedUniversalQuantifier(t2, 'z'));
				allX.setRight(null);
				allX.setLeft(allY);
				allY.setRight(null);
				allY.setLeft(allZ);
				allZ.setRight(null);
				allZ.setLeft(commutativityBody(r));
				
				formulas.put(allX.outputTextFormula(), allX);
			}			
		}
		
		Map<String, FormulaTree> checked = typeAndTruthValueCheck(formulas);
		return convertToCommonAxiom(checked, "commutativity (" + r.name() + ")");
	}
	
	//unquantified body of formula
	//∀x∀y∀z P(x,y,z) <-> P(y,x,z) 
	//x,t same type, z free
	/**
	 * Generate the unquantified portion of a commutativity claim
	 * @param r a Relation
	 * @return an unquantified formula for commutativity of r
	 */
	public FormulaTree commutativityBody(Relation r){
		FormulaTree iff = new FormulaTree (new Iff());
		FormulaTree left = new FormulaTree(new Predicate(r, new char[]{'x','y','z'}));
		FormulaTree right = new FormulaTree(new Predicate(r, new char[]{'y','x','z'}));
		
		//construct tree
		iff.setLeft(left);
		iff.setRight(right);
		
		//return top node
		return iff;
	}
	
	
	
	//associativity
	//assume all same type
	/**
	 * Given a relation r, generate formulas expressing the claim that r represents an associative
	 * operation. See {@link aa.FormulaGenerator#associativity(Relation)} for discussion.
	 * x,y,z,u,v,w all assumed to be the same type.
	 * @param r a relation
	 * @return a collection of associativity claims (one for each type)
	 */
	public Map<String, CommonAxiom> associativity(Relation r){
		Map<String, FormulaTree> formulas = new LinkedHashMap<String, FormulaTree>();

		//build all prefixes, combine all with unquantified term

		for (Type t : input.types()){
			//build quantifier prefix
			FormulaTree allX = new FormulaTree(new TypedUniversalQuantifier(t, 'x'));
			FormulaTree allY = new FormulaTree(new TypedUniversalQuantifier(t, 'y'));
			FormulaTree allZ = new FormulaTree(new TypedUniversalQuantifier(t, 'z'));
			FormulaTree allU = new FormulaTree(new TypedUniversalQuantifier(t, 'u'));
			FormulaTree allV = new FormulaTree(new TypedUniversalQuantifier(t, 'v'));
			FormulaTree allW = new FormulaTree(new TypedUniversalQuantifier(t, 'w'));
			
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
			allW.setLeft(associativityBody(r));
			
			formulas.put(allX.outputTextFormula(), allX);
		}			

		Map<String, FormulaTree> checked = typeAndTruthValueCheck(formulas);
		return convertToCommonAxiom(checked, "associativity (" + r.name() + ")");
	}
	
	/**
	 * Given a relation r, generate the unquantified portion of a formula claiming r
	 * represents an associative operation. 
	 * @param r a Relation
	 * @return an unquantified formula for the associativity of r
	 */
	public FormulaTree associativityBody(Relation r){
		//build operators
		FormulaTree and = new FormulaTree(new And());
		FormulaTree implies = new FormulaTree(new Implies());
		FormulaTree iff = new FormulaTree(new Iff());
		
		//build predicates
		FormulaTree yzu = new FormulaTree(new Predicate(r, new char[]{'y','z','u'}));
		FormulaTree xyv = new FormulaTree(new Predicate(r, new char[]{'x','y','v'}));
		FormulaTree xuw = new FormulaTree(new Predicate(r, new char[]{'x','u','w'}));
		FormulaTree vzw = new FormulaTree(new Predicate(r, new char[]{'v','z','w'}));
		
		//construct tree
		implies.setLeft(and);
		implies.setRight(iff);
		and.setLeft(yzu);
		and.setRight(xyv);
		iff.setLeft(vzw);
		iff.setRight(xuw);

		//return top node
		return implies;
	}
	
		
	
	//∀x∀y∃z P(x,y,z)
	//the name suggests x,y,z all the same type, although the axiom does not
	/**
	 * Given a relation, generate formulas claiming that r has the closure property.
	 * ∀x∀y∃z P(x,y,z) - although the name of the axiom suggests that x,y,z must be all 
	 * the same type, the variables all appear once only, so x,y,z are all allowed to 
	 * be any type. 
	 * @param r a Relation
	 * @return a collection of claims that r has the closure property. 
	 */
	public Map<String, CommonAxiom> closure(Relation r){
		Map<String, FormulaTree> formulas = new LinkedHashMap<String, FormulaTree>();

		for (Type t1 : input.types()){
			for (Type t2 : input.types()){
				for (Type t3 : input.types()){
					FormulaTree allX = new FormulaTree(new TypedUniversalQuantifier(t1, 'x'));
					FormulaTree allY = new FormulaTree(new TypedUniversalQuantifier(t2, 'y'));
					FormulaTree existsZ = new FormulaTree(new TypedExistentialQuantifier(t3, 'z'));
					allX.setRight(null);
					allX.setLeft(allY);
					allY.setRight(null);
					allY.setLeft(existsZ);
					existsZ.setRight(null);
					existsZ.setLeft(closureBody(r));
					
					formulas.put(allX.outputTextFormula(), allX);
				}
			}
		}
		Map<String, FormulaTree> checked = typeAndTruthValueCheck(formulas);
		return convertToCommonAxiom(checked, "closure (" + r.name() + ")");	
	}

	/**
	 * Given a relation r, generate the unquantified portion of the claim that r is closed. 
	 * @param r a Relation
	 * @return the unquantified portion of a formula claiming closure of r
	 */
	public FormulaTree closureBody(Relation r){
		return new FormulaTree(new Predicate(r, new char[]{'x','y','z'}));
	}
	
	
	
	
	// ∃x ∀y P(x,y,y) 
	/**
	 * Given a relation r, generate formulas expressing the claim that r has the property 
	 * of having a left identity element.
	 * ∃x ∀y P(x,y,y), with x, y being any type. 
	 * @param r a Relation
	 * @return a collection of formulas claiming that r has a left identity element. 
	 */
	public Map<String, CommonAxiom> leftIdentity(Relation r){
		Map<String, FormulaTree> formulas = new LinkedHashMap<String, FormulaTree>();
		for (Type t1 : input.types()){
			for(Type t2 : input.types()){
				
				//build nodes
				FormulaTree existsX = new FormulaTree(new TypedExistentialQuantifier(t1, 'x'));
				FormulaTree allY = new FormulaTree(new TypedUniversalQuantifier(t2, 'y'));
				FormulaTree leftIdentity = new FormulaTree(new Predicate(r, new char[]{'x','y','y'}));
				
				//construct tree;
				existsX.setRight(null);
				existsX.setLeft(allY);
				allY.setRight(null);
				allY.setLeft(leftIdentity);
							
				//return top node
				formulas.put(existsX.outputTextFormula(), existsX);
			}
		}
		Map<String, FormulaTree> checked = typeAndTruthValueCheck(formulas);
		return convertToCommonAxiom(checked, "left identity (" + r.name() + ")");	
	}


	
	
	
	
	
	//∃x ∀y P(y,x,y).
	/**
	 * Given a relation r, generate formulas expressing the claim that r has the property 
	 * of having a right identity element.
	 * ∃x ∀y P(y,x,y), with x, y being any type. 
	 * @param r a Relation
	 * @return a collection of formulas claiming that r has a right identity element. 
	 */
	public Map<String, CommonAxiom> rightIdentity(Relation r){
		Map<String, FormulaTree> formulas = new LinkedHashMap<String, FormulaTree>();
		for (Type t1 : input.types()){
			for(Type t2 : input.types()){
				
				//build nodes
				FormulaTree existsX = new FormulaTree(new TypedExistentialQuantifier(t1, 'x'));
				FormulaTree allY = new FormulaTree(new TypedUniversalQuantifier(t2, 'y'));
				FormulaTree rightIdentity = new FormulaTree(new Predicate(r, new char[]{'y','x','y'}));
				
				//construct tree;
				existsX.setRight(null);
				existsX.setLeft(allY);
				allY.setRight(null);
				allY.setLeft(rightIdentity);
				
				formulas.put(existsX.outputTextFormula(), existsX);
			}
		}
		Map<String, FormulaTree> checked = typeAndTruthValueCheck(formulas);
		return convertToCommonAxiom(checked, "right identity (" + r.name() + ")");	
	}

	//∃x ∀y ∃z P(x,y,y) & P(z,y,x)
	//presumably all the same type----------------
	/**
	 * Given a relation r, generate formulas expressing the claim that r has a 
	 * left identity element and left inverse elements.
	 * ∃x ∀y ∃z P(x,y,y) & P(z,y,x) with x,y,z being any type. 
	 * @param r a Relation
	 * @return a collection of formulas claiming that r left identity, left inverse 
	 */
	public Map<String, CommonAxiom> leftIdentityLeftInverse(Relation r){
		char[] leftIdentity = new char[]{'x','y','y'};
		char[] leftInverse = new char[]{'z','y','x'};

		return convertToCommonAxiom(identityInverseGenerator(r, leftIdentity, leftInverse), 
				"left identity, left inverse (" + r.name() + ")");
	}

	
	
	
	
	
	
	//∃x ∀y ∃z P(y,x,y) & P(z,y,x)
	/**
	 * Given a relation r, generate formulas expressing the claim that r has a 
	 * right identity element and left inverse elements.
	 * ∃x ∀y ∃z P(y,x,y) & P(z,y,x) with x,y,z being any type. 
	 * @param r a Relation
	 * @return a collection of formulas claiming that r right identity, left inverse 
	 */
	public Map<String, CommonAxiom> rightIdentityLeftInverse(Relation r){
		char[] rightIdentity = new char[]{'y','x','y'};
		char[] leftInverse = new char[]{'z','y','x'};

		return convertToCommonAxiom(identityInverseGenerator(r, rightIdentity, leftInverse), 
				"right identity, right inverse (" + r.name() + ")");
	}
	
	//∃x ∀y ∃z P(x,y,y) & P(y,z,x)
	/**
	 * Given a relation r, generate formulas expressing the claim that r has a 
	 * left identity element and right inverse elements.
	 * ∃x ∀y ∃z P(x,y,y) & P(y,z,x) with x,y,z being any type. 
	 * @param r a Relation
	 * @return a collection of formulas claiming that r left identity, right inverse 
	 */
	public Map<String, CommonAxiom> leftIdentityRightInverse(Relation r){
		char[] leftIdentity = new char[]{'x','y','y'};
		char[] RightInverse = new char[]{'y','z','x'};

		return convertToCommonAxiom(identityInverseGenerator(r, leftIdentity, RightInverse), 
				"left identity, right inverse (" + r.name() + ")");
	}
	
	//∃x ∀y ∃z P(y,x,y) & P(y,z,x)
	/**
	 * Given a relation r, generate formulas expressing the claim that r has a 
	 * right identity element and right inverse elements.
	 * ∃x ∀y ∃z P(y,x,y) & P(y,z,x) with x,y,z being any type. 
	 * @param r a Relation
	 * @return a collection of formulas claiming that r right identity, right inverse 
	 */
	public Map<String, CommonAxiom> rightIdentityRightInverse(Relation r){
		char[] rightIdentity = new char[]{'y','x','y'};
		char[] RightInverse = new char[]{'y','z','x'};

		return convertToCommonAxiom(identityInverseGenerator(r, rightIdentity, RightInverse),
				"right identity right inverse (" + r.name() + ")");
	}
	
	
	/** 
	 * Parent function to create all four left/right identity, left/right inverse claims.
	 * @param r a Relation
	 * @param identity predicate for identity
	 * @param inverse predicate for inverse
	 * @return the appropriate identity/inverse formulas
	 */
	public Map<String, FormulaTree> identityInverseGenerator(Relation r, char[] identity, char[] inverse){
		Map<String, FormulaTree> formulas = new LinkedHashMap<String, FormulaTree>();
		for (Type t1 : input.types()){
			for (Type t2 : input.types()){
				for (Type t3 : input.types()){
					//build nodes
					FormulaTree existsX = new FormulaTree(new TypedExistentialQuantifier(t1, 'x'));
					FormulaTree allY = new FormulaTree(new TypedUniversalQuantifier(t2, 'y'));
					FormulaTree existsZ = new FormulaTree(new TypedExistentialQuantifier(t3, 'z'));
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
					
					formulas.put(existsX.outputTextFormula(), existsX);
				}
			}
		}
		return typeAndTruthValueCheck(formulas);
	}
	

	
	
	
	//arity 2 -----------------------
	
	//∀x R(x,x) 
	//same type
	/**
	 * Given a Relation, generate the formulas that claim the relation is reflexive across different types.
	 * For a given relation R, one instance of the claim ∀x R(x,x) is made for each possible type for x.
	 * @param r a Relation
	 * @return a collection of reflexivity claims
	 */
	public Map<String, CommonAxiom> reflexivity(Relation r){
		Map<String, FormulaTree> formulas = new LinkedHashMap<String, FormulaTree>();
		for (Type t : input.types()){
			
			//build nodes
			FormulaTree allX = new FormulaTree(new TypedUniversalQuantifier(t, 'x'));
			FormulaTree predicate = new FormulaTree(new Predicate(r, new char[]{'x','x'}));
			
			//construct tree
			allX.setRight(null);
			allX.setLeft(predicate);
			
			formulas.put(allX.outputTextFormula(), allX);
		}
		return convertToCommonAxiom(typeAndTruthValueCheck(formulas), "reflexivity (" + r.name() + ")");
	}

	//∀x ∀y R(x,y) <-> R(y,x)
	//x,y same type
	/**
	 * Given a Relation R, generate formulas that claim the relation is symmetric for different types:
	 * ∀x ∀y R(x,y) <-> R(y,x) with x,y assumed to be the same type. 
	 * @param r a Relation
	 * @return a collection of symmetry claims (one for each type)
	 */
	public Map<String, CommonAxiom> symmetry(Relation r){
		Map<String, FormulaTree> formulas = new LinkedHashMap<String, FormulaTree>();

		for (Type t : input.types()){

			//build nodes
			FormulaTree allX = new FormulaTree(new TypedUniversalQuantifier(t, 'x'));
			FormulaTree allY = new FormulaTree(new TypedUniversalQuantifier(t, 'y'));
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
			
			formulas.put(allX.outputTextFormula(), allX);
		}
		return convertToCommonAxiom(typeAndTruthValueCheck(formulas), "symmetry (" + r.name() + ")");
	}

	//∀x ∀y ∀z (R(x,y) & R(y,z)) -> R(x,z)
	//all same type since x = z, y = z, and y free
	
	/**
	 * Given a Relation R, generate formulas that claim the relation is transitive for different types:
	 * ∀x ∀y ∀z (R(x,y) & R(y,z)) -> R(x,z) with x,y,z assumed to be the same type. 
	 * @param r a Relation
	 * @return a collection of transitivity claims (one for each type)
	 */
	public Map<String, CommonAxiom> transitivity(Relation r){
		Map<String, FormulaTree> formulas = new LinkedHashMap<String, FormulaTree>();

		for (Type t : input.types()){

			//build nodes
			FormulaTree allX = new FormulaTree(new TypedUniversalQuantifier(t, 'x'));
			FormulaTree allY = new FormulaTree(new TypedUniversalQuantifier(t, 'y'));
			FormulaTree allZ = new FormulaTree(new TypedUniversalQuantifier(t, 'z'));
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
			
			formulas.put(allX.outputTextFormula(), allX);
		}
		return convertToCommonAxiom(typeAndTruthValueCheck(formulas), "transitivity (" + r.name() + ")");
	}

	
	//∀x ∀y  (R(x,y) &  R(y,x)) -> (x = y)
	//same type
	/**
	 * Given a Relation R, generate the formula that claims the relation has the antisymmetry property:
	 * ∀x ∀y ∀z (R(x,y) & R(y,z)) -> R(x,z) with x,y assumed to be the same type. 
	 * @param r a Relation
	 * @return a collection of antisymmetry claims (one for each type)
	 */
	public Map<String, CommonAxiom> antisymmetry(Relation r){
		Map<String, FormulaTree> formulas = new LinkedHashMap<String, FormulaTree>();

		for (Type t : input.types()){
			//build nodes
			FormulaTree allX = new FormulaTree(new TypedUniversalQuantifier(t, 'x'));
			FormulaTree allY = new FormulaTree(new TypedUniversalQuantifier(t, 'y'));
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
			
			formulas.put(allX.outputTextFormula(), allX);
		}
		return convertToCommonAxiom(typeAndTruthValueCheck(formulas), "antisymmetry (" + r.name() + ")");
	}

	// ∀x ∀y *(x,y) <-> *(y,x)
	//same type
	/**
	 * Given a Relation R, generate the formula that claims the relation has the congruence property:
	 * ∀x ∀y *(x,y) <-> *(y,x) with x,y assumed to be the same type. 
	 * @param r a Relation
	 * @return a collection of antisymmetry claims (one for each type)
	 */
	public Map<String, CommonAxiom> congruence(Relation r){
		Map<String, FormulaTree> formulas = new LinkedHashMap<String, FormulaTree>();

		for (Type t : input.types()){
			//build nodes
			FormulaTree allX = new FormulaTree(new TypedUniversalQuantifier(t, 'x'));
			FormulaTree allY = new FormulaTree(new TypedUniversalQuantifier(t, 'y'));
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
			
			formulas.put(allX.outputTextFormula(), allX);
		}
		return convertToCommonAxiom(typeAndTruthValueCheck(formulas), "congruence (" + r.name() + ")");
	}

	//∀x ∀y ∀z ∀u ∀v ∀w (*(x,y) <-> *(z,u) & *(x,y) <-> *(v,w)) -> (*(z,u) <-> *(v,w))
	//x,z,v same type
	//y,u,w same type
	/**
	 * Given a Relation R, generate the formula that claims the relation has the 
	 * transitivity of congruence property:
	 * ∀x ∀y ∀z ∀u ∀v ∀w (*(x,y) <-> *(z,u) & *(x,y) <-> *(v,w)) -> (*(z,u) <-> *(v,w)) 
	 * with x,z,u assumed to be the same type, and y,u,w assumed to be the same type.
	 * Note that this is broader typing than the congruence claim, since variables are
	 * always on one particular side of the tuple.
	 *  
	 * @param r a Relation
	 * @return a collection of transitivity of congruence claims 
	 */
	public Map<String, CommonAxiom> transitivityOfCongruence(Relation r){
		Map<String, FormulaTree> formulas = new LinkedHashMap<String, FormulaTree>();

		for (Type t1 : input.types()){
			for (Type t2 : input.types()){
								
				//build nodes
				FormulaTree allX = new FormulaTree(new TypedUniversalQuantifier(t1, 'x'));
				FormulaTree allY = new FormulaTree(new TypedUniversalQuantifier(t2, 'y'));
				FormulaTree allZ = new FormulaTree(new TypedUniversalQuantifier(t1, 'z'));
				FormulaTree allU = new FormulaTree(new TypedUniversalQuantifier(t2, 'u'));
				FormulaTree allV = new FormulaTree(new TypedUniversalQuantifier(t1, 'v'));
				FormulaTree allW = new FormulaTree(new TypedUniversalQuantifier(t2, 'w'));

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
				
				formulas.put(allX.outputTextFormula(), allX);
			}
		}
		return convertToCommonAxiom(typeAndTruthValueCheck(formulas), "transitivity of congruence (" + r.name() + ")");
	}

	
	/**
	 * In-place type checking and truth-value checking. Anything mis-typed or false is removed.
	 * Formulas are translated from typed expressions to untyped ones. 
	 * @param typed a collection of typed formulas
	 * @return a collection of untyped formulas true for the input
	 */
	public Map<String, FormulaTree> typeAndTruthValueCheck(Map<String, FormulaTree> typed){
		
		//typecheck in-place, remove anything badly typed
		typeCheckAll(typed);
		
		//translate to untyped
		Map<String, FormulaTree> untyped = translateAllToUntyped(typed);

		//truth-value checking in-place, discard anything false	
		truthValueCheckAll(untyped);
		
		return untyped;
	}
	
	/**
	 * Type-convert a formula collection to a "common axioms" collection. 
	 * 
	 * @param formulas a collection of formulas expressing an axiom
	 * @param label the common name of the axiom
	 * @return a LinkedHashMap of CommonAxiom objects
	 */
	public Map<String, CommonAxiom> convertToCommonAxiom(Map<String, FormulaTree> formulas, String label)	{
		Map<String, CommonAxiom> axioms = new LinkedHashMap<String, CommonAxiom>();
		
		for(FormulaTree f : formulas.values()){
			axioms.put(f.outputTextFormula(), new CommonAxiom(f, label));
		}
		return axioms;
	}
	
	/**
	 * Convert a single FormulaTree to a CommonAxiom (add a text label)
	 * @param f a FormulaTree
	 * @param label a text Label
	 * @return a CommonAxiom object
	 */
	public CommonAxiom convertToCommonAxiom(FormulaTree f, String label){
		return new CommonAxiom(f, label);
	}
	
	

}
