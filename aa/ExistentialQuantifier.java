package aa;

/**
 * FormulaTree node for the Existential Quantifier. 
 */
public class ExistentialQuantifier extends Quantifier {
	
	/**
	 * Default constructor
	 */
	public ExistentialQuantifier(){
		super();
		outputName = "∃";
		proverName = "exists";
	}
	
	/**
	 * Create an Existential Quantifier with an associated variable 
	 */
	public ExistentialQuantifier(char v){
		super();
		outputName = "∃";
		proverName = "exists";
		setVariable(v);
	}
		
	/**
	 * Copy constructor
	 * @param q the quantifier to copy
	 */
	public ExistentialQuantifier(Quantifier q){
		outputName = q.outputName;
		proverName = q.proverName;
		variable = q.variable;
	}
	
	/**
	 * Create a copy of this quantifier, but with a substituted variable
	 * @param v - the new variable
	 */
	public ExistentialQuantifier copyQuantifierWithNewVar(char v){
		ExistentialQuantifier q = new ExistentialQuantifier(this);
		q.setVariable(v);
		return q;
	}
	
}