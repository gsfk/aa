package aa;

/**
 * Class for a negation node in a FormulaTree
 */
public class Not extends Operator{
	public Not(){
		super();
		outputName = "¬";
		proverName = "-";
	}
	
	/**
	 * Return a new instance
	 */
	public Not getOperator(){ 
		return new Not();
	}

}
