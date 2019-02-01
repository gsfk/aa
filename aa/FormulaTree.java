package aa;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.Map;
import java.util.Set;
import java.util.Stack;
import java.util.Queue;

/**
 * Class for binary expression trees for formulas in first-order logic. 
 * 
 * Nodes exists for three quantifiers (∀, ∃, ∃!),
 * five operators (&, v, ⊃, ≡, ¬)
 * and arbitrary predicate expressions from the input domain (eg: P(x,y,z)).
 * Variables are not represented as nodes, but are instead associated with their respective
 * quantifier or predicate nodes. 
 * 
 * This class includes methods for creating, rewriting, and evaluating the truth-value of 
 * expression trees. 
 */
public class FormulaTree {

	private Node node;
	private FormulaTree left, right, parent;
	private byte variableRange;
	private boolean truthValue;
	private boolean includeInMinimalSet;

	//------ constructors ------

	/**
	 * default constructor
	 */
	public FormulaTree(){
		node = null;
		left = null;
		right = null;
		parent = null;
		variableRange = 0;
		includeInMinimalSet = true;
	}

	/**
	 * copy constructor
	 */
	public FormulaTree(FormulaTree t){
		node = t.node;
		left = t.left;
		right = t.right;
		parent = t.parent;
		variableRange = t.variableRange;
		includeInMinimalSet = t.includeInMinimalSet;
	}

	/**
	 * constructor for a predicate only
	 */
	public FormulaTree(Predicate root){ 
		node = root; 
		left = null; 
		right = null;
		parent = null;
		variableRange = root.variableRange();
	}

	/**
	 * constructor for a single node 
	 */
	public FormulaTree(Node root){ 
		node = root; 
		left = null; 
		right = null;
		parent = null;
		variableRange = 0;
		includeInMinimalSet = true;
	}


	/**
	 * constructor for full tree: a top node and two subtrees
	 */
	public FormulaTree(Node root, FormulaTree l, FormulaTree r){
		node = root;
		includeInMinimalSet = true;
		setLeft(l);
		setRight(r);
		parent = null;
		
		if (l == null){
			variableRange = r.variableRange; //right never null? what about quantifiers? 
		} else {
			variableRange = unionRanges(l.variableRange, r.variableRange);	
		}
	}

	
	//UNUSED??
	/**
	 * constructor for a FormulaTree and a single predicate
	 */
	public FormulaTree(FormulaTree qTree, Predicate p){
		this(qTree, new FormulaTree(p));
		variableRange = unionRanges(qTree.variableRange, p.variableRange());
	}
	
	/**
	 * constructor to add a quantifier prefix to a single subtree
	 */
	public FormulaTree(FormulaTree qTree, FormulaTree t){

		FormulaTree newTree = qTree.deepCopy();
		FormulaTree subtree = t.deepCopy();
		FormulaTree temp  = newTree;

		while (temp.left != null){
			temp = temp.left;
		}
		temp.setLeft(subtree);
		node = newTree.node;
		right = null;
		left = newTree.left;
		
		//variable ranges must be equal, checked elsewhere
		variableRange = t.variableRange();
		
		includeInMinimalSet = true;
	}

/**
 * Get the Node at the root of the FormulaTree
 * @return the root Node
 */
	public Node root(){ return node;}

	/**
	 * Get the left subtree of this FormulaTree
	 * @return the FormulaTree representing the left subtree
	 */
	public FormulaTree left(){ return left;}

	/**
	 * Get the right subtree of this FormulaTree
	 * @return the FormulaTree representing the right subtree
	 * @return the right subtree
	 */
	public FormulaTree right(){ return right;}

	/**
	 * Get the parent FormulaTree of the root of this FormulaTree. 
	 * Typically we are only interested in the top node of the tree. 
	 * @return the parent FormulaTree
	 */
	public FormulaTree parent(){ return parent;}

	/**
	 * Set the root Node of this FormulaTree
	 * @param x root Node to set
	 */
	public void setRoot(Node x){ 
		node = x;
		if (x instanceof Predicate){
			this.variableRange = ((Predicate) x).variableRange();
		}
	}

	/**
	 * set the left FormulaTree for this tree.
	 * @param t the FormulaTree to set as the left subtree
	 */
	public void setLeft(FormulaTree t){ 
		left = t;
		if (t != null) {
			t.parent = this;
			variableRange = unionRanges(this.variableRange, t.variableRange);
		}
	}

	/**
	 * set the right FormulaTree for this tree.
	 * @param t the FormulaTree to set as the right subtree
	 */
	public void setRight(FormulaTree t){ 
		right = t;
		if (t != null){
			t.parent = this;
			variableRange = unionRanges(this.variableRange, t.variableRange);
		}
	}

	/**
	 * Set a parent FormulaTree for this FormulaTree
	 * @param t the new parent Node
	 */
	public void setParent(FormulaTree t){ 
		parent = t;
	}

	/**
	 * get the variable range for the expression represented by this FormulaTree
	 * @return a byte representation of the variable range.
	 * @see #numVarsForThisRange(byte)
	 */
	public byte variableRange(){return variableRange;}

	//UNUSED?
	/**
	 * get the truth value of the expression represented by this FormulaTree.
	 * @return a boolean representing the truth value
	 */
	public boolean truthValue(){return truthValue;}

	/**
	 * set the truth value for the expression represented by this FormulaTree.
	 * @param b boolean
	 */
	public void setTruthValue(boolean b){truthValue = b;}
	
	
	/**
	 * Shows whether or not the expression represented by this FormulaTree is included in 
	 * a minimal set of axioms. 
	 * @return true if included in minimal set
	 */
	public boolean includeInMinimalSet(){return includeInMinimalSet;}
	
	/**
	 * Set the boolean marking this expression as a member of a minimal axiom set.  
	 * @param b set true to include in min set.
	 */
	public void setIncludeInMinimalSet(boolean b){
		includeInMinimalSet = b;
	}

	
	//correct
	/**
	 * Return a human-readable String for the expression represented by this FormulaTree.
	 * @return a String representing the expression. Calls {@link #formulaTextRecurse(boolean, boolean) formulaTextRecurse()}.
	 */
	public String outputTextFormula(){
		return this.formulaTextRecurse(true, false);
	}

	/**
	 * Return a prover-readable String for the expression represented by this FormulaTree.
	 * @return a String representing the expression
	 */
	public String outputProverFormula(){
		FormulaTree nonUnique = this;

		//if uniqueness quantifier present, rewrite the tree
		if (this.hasUniquenessQuantifier()){
			nonUnique = nonUnique.eliminateUniquenessQuantification();
		}

		//return prover text
		return nonUnique.formulaTextRecurse(false, true);
	}
	
	/**
	 * Return true is this tree has includes a uniqueness quantifier.  				//TODO
	 * @return true if uniqueness quantifier present 								//works only for prenex form
	 */
//	public boolean hasUniquenessQuantifier(){
//		FormulaTree currentNode = this;
//		while (currentNode.node instanceof Quantifier){
//			if (currentNode.node instanceof UniquenessQuantifier){
//				return true;
//			}
//			currentNode = currentNode.left;
//		}
//		return false;
//	}
	
	
	/**
	 * Return true is this tree has includes a uniqueness quantifier.
	 * Works by BFS search of an expression tree.
	 * @return
	 */
	public boolean hasUniquenessQuantifier(){
		Queue<FormulaTree> queue = new LinkedList<FormulaTree>();
		FormulaTree n;
		queue.add(this);
		
		while (!queue.isEmpty()){
			n = queue.remove();
			
			if (n.root() instanceof UniquenessQuantifier){
				return true;
			} 
			//add left
			if (n.left() != null){queue.add(n.left());}
			
			//add right
			if (n.right() != null){queue.add(n.right());}
		}
		return false;
	}
	
	
	
	
	
	//generates formula text from an expression tree, both for prover and user output
	/**
	 * Recursive method for translating FormulaTrees into a String expression. 
	 * Called by {@link #outputTextFormula()} and {@link #outputProverFormula()}.
	 * @param skipParens true to avoid printing outermost parentheses
	 * @param isProverOutput set true to produce a prover-readable String rather than a human-readable one
	 * @return a String representation of the formula
	 */
	public String formulaTextRecurse(boolean skipParens, boolean isProverOutput) {
		StringBuilder textFormula = new StringBuilder();
		FormulaTree currentNode = this;
		boolean binaryOperator = false;
		String name;
		
		//preorder for quantifiers
		while (currentNode != null && currentNode.root() instanceof Quantifier){
			if (isProverOutput){
				name = currentNode.root().proverName();
			} else {
				name = currentNode.root().outputName();
			}
			
			textFormula.append(name);
			currentNode = currentNode.left;
		}
		//space between quantifiers and rest of formula
		if (skipParens){
			textFormula.append(" "); 
		}

		//handle printing quantifier trees only (for debugging)
		if (currentNode == null){
			return textFormula.toString();
		}
		
		//inorder for rest of formula
		if (currentNode.root() instanceof Operator && !(currentNode.root() instanceof Not) && !(currentNode.root() instanceof Equals)){
			binaryOperator = true;
		}

		if (binaryOperator && !skipParens){
			textFormula.append("(");
		}

		if (currentNode.left != null){
			textFormula.append(currentNode.left.formulaTextRecurse(false, isProverOutput));
		}

		if (binaryOperator){
			textFormula.append(" ");
		}

		if (isProverOutput){
			name = currentNode.root().proverName();
		} else {
			name = currentNode.root().outputName();
		}
		textFormula.append(name);

		if (binaryOperator){
			textFormula.append(" ");
		}

		if (currentNode.right != null){
			textFormula.append(currentNode.right.formulaTextRecurse(false, isProverOutput));
		}

		if (binaryOperator && !skipParens){
			textFormula.append(")");
		}

		return textFormula.toString();
	}

	/**
	 * Eliminate uniqueness quantifier ∃! by tree rewriting.
	 * Calls the recursive method {@link #elimUniquenessRecurse(Map) elimUniquenessRecurse()}.
	 * 
	 * @return a logically equivalent FormulaTree lacking a uniqueness quantifier
	 */
	//eliminate uniqueness quantifier by tree rewriting
	public FormulaTree eliminateUniquenessQuantification(){
		Map<Character, Character> substitution = nullSubstitution();
		return elimUniquenessRecurse(substitution);
	}

	/**
	 * Recursive method for tree rewriting. 
	 * Copies all tree nodes unchanged except for uniqueness quantifiers. 
	 * Translates according to the equivalence ∃!xP(x) <-> ∃x∀t(P(t) <-> x=t)).
	 * In general, where S is any subtree, the expression "∃!xS" becomes ∃x∀t(S[x/t] <-> x=t))
	 * 
	 * @param substitution a Java Map of variable substitutions 
	 * @return A new tree without a uniqueness quantifier as the top node, with the given substitution
	 * applied
	 */
	//recursive method for tree rewriting, called by parent method above
	public FormulaTree elimUniquenessRecurse(Map<Character, Character> substitution){
		FormulaTree t = new FormulaTree();

		//uniqueness case		
		if (this.node instanceof UniquenessQuantifier){
			char oldVar = ((UniquenessQuantifier) this.node).variable();
			char newVar = freshVariable(oldVar);
			
			//apply substitution
			substitution.put(oldVar, newVar);
			
			//build new subtree structure
			//for old expression ∃!x P(x), build new expression ∃x ∀t (P(t) <-> x = t)
			
			//change uniqueness quantifier to regular existential quantifier with the same variable
			ExistentialQuantifier e = new ExistentialQuantifier();
			e.setVariable(oldVar);
			
			//universal quantifier with fresh variable
			UniversalQuantifier a = new UniversalQuantifier();
			a.setVariable(newVar);
			FormulaTree aTree = new FormulaTree(a);
			aTree.right = null;
						
			//operator nodes
			FormulaTree iff = new FormulaTree(new Iff());
			FormulaTree eq = new FormulaTree(new Equals(oldVar, newVar));  //l,r null
			
			//assemble parts and recurse:
			
			//existential quantifier
			t.node = e;
			t.right = null;
			
			//universal quantifier
			t.left = aTree;		
			aTree.left = iff;
			
			//biconditional operator
			iff.right = eq;
			
			//equality operator
			eq.left = eq.right = null;
			
			//recurse
			iff.left = this.left.elimUniquenessRecurse(substitution);

		} else {			//else non-unique

			//if predicate, apply substitution
			if (this.node instanceof Predicate){
				
				//copy old predicate
				Predicate oldPredicate = (Predicate)this.root();
				Predicate newPredicate = new Predicate(oldPredicate); 
				
				//apply substitution 
				char[] newTuple = tupleSubstitution(oldPredicate.varTuple(), substitution);
				newPredicate.setVarTuple(newTuple);

				//set root, do not recurse (predicates are leaves)
				t.node = newPredicate;
				t.left = t.right = null;

				//else operator or other quantifier, copy unchanged
			} else {

				t.node = this.node;

				//recurse on left and right (check for null) 
				if (this.left != null) {
					t.left = this.left.elimUniquenessRecurse(substitution);
				}
				if (this.right != null) {
					t.right = this.right.elimUniquenessRecurse(substitution);
				}
			}
		}//end non-unique case

		return t;
	}

	/**
	 * Create an initial substitution mapping for the 
	 * {@link #eliminateUniquenessQuantification()} method. 
	 * This initial mapping has no effect, it maps x |-> x, y |-> y, etc. The mapping is altered
	 * where appropriate as elimUniquenessRecurse() recurses through the FormulaTree.
	 *
	 * @return an identity substitution where each variable is mapped to itself.
	 */
	//initial substitution for uniqueness quantifier elimination method above
	public static Map<Character, Character> nullSubstitution(){
		Map<Character, Character> substitution = new HashMap<Character, Character>();
		substitution.put('x', 'x');
		substitution.put('y', 'y');
		substitution.put('z', 'z');
		substitution.put('w', 'w');
		return substitution;
	}

	
	/**
	 * Apply a given substitution to the variable tuple of a predicate.
	 * Given the substitution (x |-> t, y |-> u) and predicate term P(x,y,y),
	 * produces the new tuple (t,u,u) expressed as a character array.
	 * Any unsubstituted variables keep their original names.
	 * 
	 * @param oldTuple a char array representing the variable tuple for a predicate term
	 * @param substitution a mapping between variables
	 * @return the new variable tuple
	 */
	//apply substitution to predicate variable tuple
	//unsubstituted variables keep their old names
	public static char[] tupleSubstitution(char[] oldTuple, Map<Character, Character> substitution){
		int length = oldTuple.length;
		char[] newTuple = new char[length];
		for (int i = 0; i < length; i++){
			newTuple[i] = substitution.get(oldTuple[i]);
		}
		return newTuple; 
	}

	/**
	 * maps an old variable to a fresh one.
	 * In particular maps x->t, y->u, z->v, w->s
	 * @param oldVar the old variable (one of x,y,z,w)
	 * @return a character representing a fresh varaible
	 */
	//maps an old variable to a fresh one: x->t, y->u, z->v, w->s
	public static char freshVariable(char oldVar){
		return (char)((int)oldVar - 4);
	}
	

	/**
	 * Recursive deep copy for FormulaTrees
	 * @return a deep copy of the FormulaTree
	 */
	public FormulaTree deepCopy() {
		FormulaTree n = new FormulaTree();
		n.setRoot(this.root());
		n.variableRange = this.variableRange;
		if (this.left != null) {
			n.setLeft(this.left.deepCopy());
		}
		if (this.right != null) {
			n.setRight(this.right.deepCopy());
		}
		return n;
	}

/**
 * Computes the number of variables in a term.
 * Returns zero for invalid ranges.
 * Calls {@link #numVarsForThisRange(byte) numVarsForThisRange()}
 * @return the integer number of variables
 */
	public int numVars(){
		return numVarsForThisRange(variableRange);
	}
		
	
	/**
	 * Static method to compute the number of variables in an expression, where the input is a
	 * variable range value encoded as a Java byte.   
	 * 
	 * Each of the four possible variables is given a binary value:<p>
	 * 
	 *  x = 1000<p>
	 *  y = 0100<p>
	 *  z = 0010<p>
	 *  w = 0001<p>
	 *  
	 *  The variables present in an expression are summed together, eg: x + y = 1000 + 0100 = 1100.
	 *  
	 *  A simple rule is applied to avoid producing redundant expressions: 
	 *  
	 *  Single-variable formulas are over x only<p>
	 *  Two-variable formulas are over x,y only<p>
	 *  Three-variable expressions are over x,y,z only<p>
	 *  Four-variable expressions are over x,y,z,w only<p>
	 * 
	 *  This method returns the integer value of the number of variables in a FormulaTree 
	 *  (and thus whether the formula it represents is over x, or (x,y) or (x,y,z) or (x,y,z,w).
	 *  Invalid range values (those not meeting the rule above) produce a return value of zero.
	 * 
	 * @param range a byte expression for the variable range of a FormulaTree
	 * @return the integer number of variables in the FormulaTree, either 1, 2, 3, or 4, 
	 * with invalid ranges returning zero.
	 */
	public static int numVarsForThisRange(byte range){
		final byte xRange = 0b1000; 
		final byte yRange = 0b0100; 
		final byte zRange = 0b0010; 
		final byte wRange = 0b0001; 
		

		if (range == xRange) {return 1;}
		if (range == (xRange | yRange)) {return 2;}
		if (range == (xRange | yRange | zRange)) {return 3;}
		if (range == (xRange | yRange | zRange | wRange)){return 4;}

		//else invalid
		return 0;
	}

	/**
	 * Union the range of two variable ranges
	 * @param a Java byte representing a variable range
	 * @param b Java byte representing a variable range
	 * @return the range of (a Union b)
	 * @see #numVarsForThisRange(byte)
	 */
	public static byte unionRanges(byte a, byte b){
		int value = a | b;
		return (byte) value;
	}

	/**
	 * Update the variable range of a FormulaTree by Depth-First search.
	 * Updates are necessary when iteratively constructing larger FormulaTrees.
	 */
	public void updateRange(){
		byte range = 0;
		Stack<FormulaTree> s = new Stack<FormulaTree>();

		s.add(this);
		while (!s.isEmpty()){
			FormulaTree currentNode = s.pop();
			if (currentNode.right() != null) {
				s.add(currentNode.right());
			}
			if (currentNode.left() != null) {
				s.add(currentNode.left());	
			}
			if (currentNode.root() instanceof Predicate){
				range = unionRanges(range, currentNode.variableRange());
			}
		}
		this.variableRange = range;
	}

	
	/**
	 * Test if a formula is interesting.
	 * 
	 * Call a formula interesting if:<p>
	 * The outermost quantifier is universal and main connective is implication<p>
	 * The outermost quantifier is existential and main connective is conjunction<p>
	 * The outermost quantifier is uniqueness and main connective is conjunction<p>
	 * @return true if interesting
	 */
	public boolean isInteresting(){
		if (outerQuantifierUniversal() && mainConnectiveImplies()) {return true;}
		if (outerQuantifierExistential() && mainConnectiveAnd()) {return true;}
		if (outerQuantifierUniqueness() && mainConnectiveAnd()){return true;} 
		return false;
	}

	/**
	 * Test if the outermost quantifier of a FormulaTree is the Universal Quantifier
	 * @return true if the outermost quantifier is Universal
	 */
	public boolean outerQuantifierUniversal(){
		if (node instanceof UniversalQuantifier){
			return true;
		}
		return false;
	}
	/**
	 * Test if the outermost quantifier of a FormulaTree is the Existential Quantifier
	 * @return true if the outermost quantifier is Existential
	 */
	public boolean outerQuantifierExistential(){
		if (node instanceof ExistentialQuantifier){
			return true;
		}
		return false;
	}
	/**
	 * Test if the outermost quantifier of a FormulaTree is the Uniqueness Quantifier
	 * @return true if the outermost quantifier is uniqueness
	 */
	public boolean outerQuantifierUniqueness(){
		if (node instanceof UniquenessQuantifier){
			return true;
		}
		return false;
	}
	
	/**
	 * Test if the main connective of a FormulaTree is implication
	 * @return true if main connective is implication
	 */
	public boolean mainConnectiveImplies(){
		FormulaTree currentNode = this;
		
		//skip quantifiers
		while (currentNode.node instanceof Quantifier){
			currentNode = currentNode.left;
		}
		if (currentNode.node instanceof Implies){
			return true;
		}
		return false;
	}
	
	/**
	 * Test if the main connective of a FormulaTree is conjunction
	 * @return true main connective is conjunction
	 */
	public boolean mainConnectiveAnd(){
		FormulaTree currentNode = this;
		
		//skip quantifiers
		while (currentNode.node instanceof Quantifier){
			currentNode = currentNode.left;
		}
		if (currentNode.node instanceof And){
			return true;
		}
		return false;
	}
	

	//TRUTH-VALUE METHODS
	
	/* AND-OR search
	and-or tree is never made explicitly in memory 
	and in practice even the particular nodes of the tree are not constructed
	the tree structure is an abstract description of the search method
	 */

	
	
	
/** 

	
	
	
	//returns truth value for a formula over input domain elements
	/**
	 * Find the truth value of the expression represented by this FormulaTree over the input elements.
	 * Calls the recursive method {@link #valueRecurse(FormulaTree, ArrayList, Map, boolean) valueRecurse()}.
	 * 
	 * @param elements the elements of the input
	 * @return the truth value of the expression
	 */
	public boolean value(ArrayList<String> elements){
		Map<Character, String> substitution = initSubstitution();
		boolean debug = false;
		boolean result;
		
		result  = valueRecurse(this, elements, substitution, debug);

		return result;
	}


	/**
	 * Recursive truth-value evaluation method for FormulaTrees.
	 * 
	 * Tree nodes are either quantifiers, operators or predicates. 
	 * Treat each case accordingly:
	 * 
	 * quantifier cases:
	 * 
	 * 		universal: check all substitutions (all possible substitutions of domain constants for this variable)
	 * 		return true if all true
	 * 
	 * 		existential: check all substitutions, return true after first true case
	 * 
	 * 		uniqueness: check all substitutions, return true if exactly one true
	 * 
	 * operator cases (for subtrees A,B):
	 * 
	 * 		conjunction: value(A & B) = value(A) && value(B)
	 * 		disjunction: value(A v B) = value(A) || value(B)
	 * 	   	implication: A -> B is equivalent to ¬A v B, so value(A -> B) = !(value(A)) || value(B)
	 * 		biconditional: A <-> B true if A and B have matching truth values, so value(A <-> B) = (value(A) == value(B))
	 * 		negation: value(¬A) = !value(A)
	 * 
	 * predicate case (base case):
	 * 
	 * 		reach a predicate term of the form P(x,y,z), 
	 * 		all predicate terms are leaves; by the time you reach a leaf, any variable terms will have been 
	 * 		substituted away in the quantifier cases above. The substitution is a mapping between variables and 
	 * 		domain elements, passed along as a parameter in the search routine, such as: (x |-> a, y |-> b, z |-> c).  
	 * 		So return "true" if the tuple (a,b,c) appears in the fact table for P, return "false" otherwise. 
	 * 
	 * 
	 * @param t a FormulaTree object
	 * @param elements the domain elements
	 * @param substitution a mapping of variable substitutions
	 * @param debug debugging boolean
	 * @return the truth value of the formula
	 */
	//recursive truth value search called by parent function value() above
	//original static code, to test
	public static boolean valueRecurse(FormulaTree t, ArrayList<String> elements, 
			Map<Character, String> substitution, boolean debug){

		boolean result = false;
		Node n = t.root();
		FormulaTree left = t.left();	
		FormulaTree right = t.right();

		//quantifier cases
		if (n instanceof Quantifier){
			char variable = ((Quantifier) n).variable();

			//Universal case
			//for loop over all domain elements
			//if all true, return true
			//return false on first false
			//recurse on left child, right child is null
			if (n instanceof UniversalQuantifier){
				for (String e : elements){
					substitution.put(variable, e);
					result = valueRecurse(left, elements, substitution, debug);
					if (!result){
						return false;
					}
				}
				return true;

			} else 

				//Existential case
				//return true on first true
				//if all false return false
				//recurse on right child, left child is null
				if (n instanceof ExistentialQuantifier){			
					for (String e : elements){
						substitution.put(variable, e);					
						result = valueRecurse(left, elements, substitution, debug);					
						if (result){
							return true;
						}
					}
					return false;

				} else 

					//Uniqueness case
					//return true if exactly one true
					//return false on second true
					//recurse on right child, left child is null					
					if (n instanceof UniquenessQuantifier){
						int trueCount = 0;
						for (String e : elements){
							substitution.put(variable, e);
							result = valueRecurse(left, elements, substitution, debug);			
							if (result){
								trueCount++;
							}
						}
						if (trueCount == 1){
							return true;
						} else {
							return false;
						}
					}
		}

		//operator cases
		if (n instanceof Operator){
			if (n instanceof And){
				return (valueRecurse(left, elements, substitution, debug) && valueRecurse(right, elements, substitution, debug));
			}

			if (n instanceof Or){
				return (valueRecurse(left, elements, substitution, debug) || valueRecurse(right, elements, substitution, debug));				
			}

			if (n instanceof Implies){
				return (!(valueRecurse(left, elements, substitution, debug)) || valueRecurse(right, elements, substitution, debug));
			}

			if (n instanceof Iff){
				return (valueRecurse(left, elements, substitution, debug) == valueRecurse(right, elements, substitution, debug));
			}

			if (n instanceof Not){
				return !valueRecurse(right, elements, substitution, debug);
			}
			
			//equals for assessing common axiom claims only
			if (n instanceof Equals){
				String leftConstant = substitution.get(((Equals) n).leftVar());
				String rightConstant = substitution.get(((Equals) n).rightVar());
				
				//return true if strings equal, no recursion
				return leftConstant.equals(rightConstant);
			}
			
		}

		//predicate case
		//generate tuple of variable substitutions and check fact table for this predicate
		if (n instanceof Predicate){
			ArrayList<String> claim = new ArrayList<String>();
			char[] varTuple = ((Predicate) n).varTuple();
			claim = getSubstitution(varTuple, substitution);

			if (debug){
				System.out.println(n.outputName());
				System.out.println(arrayListString(claim));
				System.out.println(((Predicate) n).parentRelation().factTableLookup(claim) + "\n");
			}
			
			return ((Predicate) n).parentRelation().factTableLookup(claim);
		}

		//never reach here
		//dummy return for the compiler, all returns are conditional
		System.err.println("And-Or search error");
		return false; 
	}

	
	//needed? empty substitution should be sufficient
	//create an empty substitution
	public static Map<Character, String> initSubstitution(){
		Map<Character, String> substitution = new HashMap<Character, String>();
		substitution.put('x', null);
		substitution.put('y', null);
		substitution.put('z', null);
		substitution.put('w', null);
		return substitution;
	}

	//given a tuple of variables and a substitution mapping, return a tuple of domain elements
	public static ArrayList<String> getSubstitution(char[] varTuple, Map<Character, String> subst){
		ArrayList<String> substitution = new ArrayList<String>();
		for (Character c : varTuple){
			substitution.add(subst.get(c));
		}
		return substitution;
	}
	
	

	//------ debug print methods --------
	
	public static String arrayListString(ArrayList<String> array){
		StringBuilder s = new StringBuilder();
		int commasToPrint = array.size()-1;
		s.append("<");
		for (String element: array){
			s.append(element);
			if (commasToPrint > 0){
				s.append(", ");
				commasToPrint--;
			}
		}
		s.append(">");
		return s.toString();
	}
	
	public static String setString(Set<String> collection){
		StringBuilder s = new StringBuilder();
		int commasToPrint = collection.size()-1;
		s.append("<");
		for (String t: collection){
			s.append(t);
			if (commasToPrint > 0){
				s.append(", ");
				commasToPrint--;
			}
		}
		s.append(">");
		return s.toString();
	}
		
	public static String arrayListOfNodesString(ArrayList<? extends Node> array){
		StringBuilder s = new StringBuilder();
		int commasToPrint = array.size()-1;
		s.append("<");
		for (Node n: array){
			s.append(n.outputName());
			if (commasToPrint > 0){
				s.append(", ");
				commasToPrint--;
			}
		}
		s.append(">");
		return s.toString();
	}
	
	public static String treeArrayListToString(ArrayList<FormulaTree> array){
		StringBuilder s = new StringBuilder();
		int commasToPrint = array.size()-1;
		s.append("<");
		for (FormulaTree t: array){
			s.append(t.outputTextFormula());
			if (commasToPrint > 0){
				s.append(", ");
				commasToPrint--;
			}
		}
		s.append(">");
		return s.toString();
	}
	
	
	public static String showInterestingAsString(Map<String, FormulaTree> formulas){
		StringBuilder s = new StringBuilder();
		int count = 0;
		System.err.println("Interesting formulas: ");
		for (FormulaTree f : formulas.values()){
			if (f.isInteresting()){
				s.append(f.outputTextFormula() + "\n");				
				count ++;
			}
		}
		System.err.println(count + " interesting formulas");
		return s.toString();
	}


	public static String substitutionString(Map<Character, String> substitution){
		StringBuilder s = new StringBuilder();
		String value;
		int commasToPrint = substitution.size()-1; 	
		s.append("[");
		for (Character c: substitution.keySet()){
			s.append(c + ":");
			value = substitution.get(c);
			if (value!= null) {
				s.append(value);
			} else {
				s.append("∅");
			}
			if (commasToPrint > 0){
				s.append(", ");
				commasToPrint--;
			}
		}
		s.append("]");
		return s.toString();
	}
	
	
	public static String indentPadding(char var){
		if(var == 'x'){return "";}
		if(var == 'y'){return "   ";}
		if(var == 'z'){return "      ";}
		if(var == 'w'){return "         ";}
		if(var == 'u'){return "            ";}
		if(var == 'v'){return "               ";}	
		
		return null;
	}
	
	
	
	
	
	
	
	
	
	
	
	
	
	
	
	
	
	
	

	
	//---- debug-oriented truth-value methods
	//returns truth value for a formula over input domain elements
	/**
	 * Debugging version of the truth-value method {@link #value(ArrayList) value()}.
	 * Returns the truth value of a formula over the input domain elements
	 * @param elements the input domain elements 
	 * @return truth value of the formula represented by the FormulaTree
	 */
	public boolean debugValue(ArrayList<String> elements){
		Map<Character, String> substitution = initSubstitution();
		boolean debug = false;
		boolean result;
				
		result  = debugValueRecurse(elements, substitution, debug);
		
		return result;
	}

/**
 * A non-static version of {@link #valueRecurse(FormulaTree, ArrayList, Map, boolean) valueRecurse()} 
 * focused on debugging. 
 * @param elements the domain elements
 * @param substitution a mapping of variable substitutions
 * @param debug boolean, to remove!
 * @return the truth value of the formula 
 */
	public boolean debugValueRecurse(ArrayList<String> elements, 
			Map<Character, String> substitution, boolean debug){

		boolean result = false;
		Node n = this.root();

		//quantifier cases
		if (n instanceof Quantifier){
			char variable = ((Quantifier) n).variable();

			//Universal case
			//for loop over all domain elements
			//if all true, return true
			//return false on first false
			//recurse on left child, right child is null

			
			if (n instanceof UniversalQuantifier){
				char var = ((Quantifier) n).variable();
				String padding = indentPadding(var);
				System.out.println("\nUniversal: " + var);
				for (String e : elements){
					substitution.put(variable, e);
					System.out.print("∀" + var + padding + substitutionString(substitution) + " ");
					result = this.left.debugValueRecurse(elements, substitution, debug);
					System.out.println(result);
					
					if (!result){
						return false;
					}
				}
				return true;

			} else 

				//Existential case
				//return true on first true
				//if all false return false
				//recurse on right child, left child is null
				if (n instanceof ExistentialQuantifier){	
					char var = ((Quantifier) n).variable();
					String padding = indentPadding(var);
					System.out.println("\nExistential: " + var);

					for (String e : elements){
						substitution.put(variable, e);	
						System.out.print("∃" + var + padding + substitutionString(substitution) + " ");

						result = this.left.debugValueRecurse(elements, substitution, debug);
						System.out.println(result);

						
						if (result){
							return true;
						}
					}
					return false;

				} else 

					//Uniqueness case
					//return true if exactly one true
					//return false on second true
					//recurse on right child, left child is null					
					if (n instanceof UniquenessQuantifier){
						char var = ((Quantifier) n).variable();
						String padding = indentPadding(var);
						System.out.println("\nUniqueness: " + var);

						int trueCount = 0;
						for (String e : elements){
							substitution.put(variable, e);
							System.out.print("∃!" + var + padding + substitutionString(substitution) + " ");

							result = this.left.debugValueRecurse(elements, substitution, debug);
							
							System.out.println(result);
							
							if (result){
								trueCount++;
							}
						}
						if (trueCount == 1){
							return true;
						} else {
							return false;
						}
					}
		}

		//operator cases
		if (n instanceof Operator){
			if (n instanceof And){
				return (this.left.debugValueRecurse(elements, substitution, debug) && this.right.debugValueRecurse(elements, substitution, debug));
			}

			if (n instanceof Or){
				return (this.left.debugValueRecurse(elements, substitution, debug) || this.right.debugValueRecurse(elements, substitution, debug));				
			}

			if (n instanceof Implies){
				return (!(this.left.debugValueRecurse(elements, substitution, debug)) || this.right.debugValueRecurse(elements, substitution, debug));
			}

			if (n instanceof Iff){
				return (this.left.debugValueRecurse(elements, substitution, debug) == this.right.debugValueRecurse(elements, substitution, debug));
			}

			if (n instanceof Not){
				return !this.right.debugValueRecurse(elements, substitution, debug);
			}
			
			
		}

		//predicate case
		//generate tuple of variable substitutions and check fact table for this predicate
		if (n instanceof Predicate){
			ArrayList<String> claim = new ArrayList<String>();
			char[] varTuple = ((Predicate) n).varTuple();
			claim = getSubstitution(varTuple, substitution);

			if (debug){
				System.out.println(n.outputName());
				System.out.println(arrayListString(claim));
				System.out.println(((Predicate) n).parentRelation().factTableLookup(claim) + "\n");
			}
			
			return ((Predicate) n).parentRelation().factTableLookup(claim);
		}

		//never reach here
		//dummy return for the compiler, all returns are conditional
		System.err.println("And-Or search error");
		return false; 
	}


	
	
	
	
	
}


