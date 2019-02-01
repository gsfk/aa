package aa;
/**
 * Class for an implication node in a FormulaTree
 *
 */

public class Implies extends Operator{
	public Implies(){
		super();
		outputName = "⊃";
		proverName = "->";
	}
	
	/**
	 * Return a new instance
	 */
	public Implies getOperator(){
		return new Implies(); 
	}
	
}
