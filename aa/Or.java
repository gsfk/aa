package aa;

/**
 * Class for a disjunction node in a FormulaTree
 */
public class Or extends Operator{
	public Or(){
		super();
		outputName = "v";
		proverName = "|";
	}

	
	/**
	 * Return a new instance
	 */
	public Or getOperator(){
		return new Or();
	}
}
