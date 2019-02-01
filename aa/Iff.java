package aa;
/**
 * Class for a biconditional node in a FormulaTree
 *
 */

public class Iff extends Operator{
	
	public Iff(){
		super();
		outputName = "≡";
		proverName = "<->";
	}

	
	/**
	 * Return a new instance
	 */
	public Iff getOperator(){
		return new Iff();
	}
}