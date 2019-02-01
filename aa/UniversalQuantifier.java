package aa;

/**
 * FormulaTree node for the Universal Quantifier. 
 * @see aa.Quantifier
 */
public class UniversalQuantifier extends Quantifier {
	
	/**
	 * Default constructor
	 */
	public UniversalQuantifier(){
		super();
		outputName = "∀";
		proverName = "all";
	}
	
	/**
	 * Constructor for a Universal Quantifier with an associated variable 
	 */
	public UniversalQuantifier(char v){
		super();
		outputName = "∀";
		proverName = "all";
		setVariable(v);
	}
	
	/**
	 * Copy constructor 
	 * @param q the quantifier to copy
	 */
	public UniversalQuantifier(Quantifier q){
		outputName = q.outputName;
		proverName = q.proverName;
		variable = q.variable;
	}
	
	/**
	 * Create a copy of this quantifier, but with a substituted variable
	 * @param v - the new variable
	 */
	public UniversalQuantifier copyQuantifierWithNewVar(char v){
		UniversalQuantifier q = new UniversalQuantifier(this);
		q.setVariable(v);
		return q;
	}
	
}

