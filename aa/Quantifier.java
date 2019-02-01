package aa;

/**
 * Abstract parent class for Quantifier nodes in a FormulaTree
 * @see aa.Node
 * @see aa.FormulaTree
 *
 */
public abstract class Quantifier extends Node {
	protected char variable;

	/**
	 * Default constructor
	 */
	public Quantifier(){}
	
	/**
	 * set the variable for this quantifier 
	 * @param v
	 */
	public void setVariable(char v){variable = v;}
	
	/**
	 * Get the variable bound by this quantifier
	 * @return the variable name (x,y,z, or w)
	 */
	public char variable(){return variable;}
	
	/**
	 * Return a human-readable String for this quantifier, eg "∀x"
	 */
	public String outputName(){return new String(outputName + variable);}
	
	
	/**
	 * Return a prover-readable String for this quantifier
	 */
	public String proverName(){return new String(proverName + " " + variable + " ");}
}
