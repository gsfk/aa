package aa;

/**
 * Class for a conjunction node in a FormulaTree
 *
 */
public class And extends Operator{
	public And(){
		super();
		outputName = "&";
		proverName = "&";
	}

	
	/**
	 * Return a new instance
	 * @return a new And instance
	 */
	public And getOperator(){
		return new And();
	}
	
	
}

