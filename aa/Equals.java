package aa;

/**
 * Special operator for prover output only.
 * Used only in output to the prover, for prover-readable translations
 * of  formulas bearing a uniqueness quantifier. The input domain need
 * not have an explicit equality operator; uniqueness assumes some concept 
 * of equality.
 */
public class Equals extends Operator{
	
	char oldVariable, newVariable;
	
	
	public Equals(){
		super();
		outputName = proverName = name();
	}

	/**
	 * Constructor that takes "old" and "new" variables 
	 * @param oldVar the old variable (one of x,y,z,w)
	 * @param newVar a fresh substitution variable (one of t,u,v,s)
	 */
	public Equals(char oldVar, char newVar){
		super();
		oldVariable = oldVar;
		newVariable = newVar;
		outputName = proverName = name();
	}
	
	/**
	 * Return a new instance
	 * @return a new Equals object
	 */
	public Equals getOperator(){
		return new Equals();
	}
	
	/**
	 * Generate the output name. 
	 * @return String of the output name
	 */
	public String name(){
		StringBuilder name = new StringBuilder();
		name.append("(");
		name.append(this.oldVariable);
		name.append(" = ");
		name.append(this.newVariable);
		name.append(")");
		return name.toString();
	}
	
	
	public char leftVar(){return oldVariable;}
	public void setLeftVar(char v){oldVariable = v;}
	
	public char rightVar(){return newVariable;}
	public void setRightVar(char v){newVariable = v;}
	
}



