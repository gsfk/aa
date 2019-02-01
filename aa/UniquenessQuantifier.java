package aa;

/**
 * FormulaTree node for the Uniqueness Quantifier. 
 * @see aa.Quantifier
 */

public class UniquenessQuantifier extends Quantifier {
	
	/**
	 * Default constructor
	 */
	public UniquenessQuantifier(){
		super();
		outputName = "∃!";
		proverName = ""; // no prover name
	}

	/**
	 * Construct a uniqueness quantifier with an associated variable
	 * @param v a variable
	 */
	public UniquenessQuantifier(char v){
		super();
		outputName = "∃!";
		proverName = ""; // no prover name
		setVariable(v);
	}

	/**
	 * Copy constructor
	 * @param q a uniqueness quantifier to copy
	 */
	public UniquenessQuantifier(Quantifier q){
		outputName = q.outputName;
		proverName = q.proverName;
		variable = q.variable;
	}

	/**
	 * Return a copy of this quantifier with a new variable
	 * @param v a variable name (x,y,z or w)
	 * @return a new UniquenessQuantifier 
	 */
	public UniquenessQuantifier copyQuantifierWithNewVar(char v){
		UniquenessQuantifier q = new UniquenessQuantifier(this);
		q.setVariable(v);
		return q;
	}


}