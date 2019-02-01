package aa;
/**
 * Abstract class for logical operators
 * @see aa.Node
 * @see aa.FormulaTree
 *
 */
public abstract class Operator extends Node{
	public Operator(){}
	
	/**
	 * Return a new instance.
	 * Abstract method is instantiated by the subclasses, so
	 * And returns a new And, Or returns a new Or, etc.
	 * @return a new Operator object
	 */
	public abstract Operator getOperator();
	
	

}