package aa;

/**
 * Class for a particular instance of a relation with a particular tuple of variables
 *
 */
public class Predicate extends Node{

	private char[] varTuple; 
	private byte variableRange;
	private Relation parentRelation;

	//constants for computing variable ranges
	private final byte xRange = 0b1000; 
	private final byte yRange = 0b0100; 
	private final byte zRange = 0b0010; 
	private final byte wRange = 0b0001; 
	
	/**
	 * Constructor
	 * @param r a Relation object
	 * @param t a variable tuple
	 */
	public Predicate(Relation r, char[] t){
		parentRelation = r;
		varTuple = t;
		String name = name();
		outputName = name;
		proverName = name;
		variableRange = computeRange();
	}


	/**
	 * Copy constructor
	 * @param p the Predicate to copy
	 */
	public Predicate(Predicate p){
		super(p);
		parentRelation = p.parentRelation();
		varTuple = p.varTuple;
		variableRange = p.variableRange;
		String name = name();
		outputName = name;
		proverName = name;
	}

	/**
	 * Compute the variable range of this Predicate.
	 * Uses a byte representation of the range, see 
	 * {@link aa.FormulaTree#numVarsForThisRange(byte) numVarsForThisRange()}
	 * 
	 * @return a byte representation of the variable range
	 */
	public byte computeRange(){
		int range = 0;
		for (char v : varTuple){
			if (v == 'x'){range = (range | xRange);}
			if (v == 'y'){range = (range | yRange);}
			if (v == 'z'){range = (range | zRange);}
			if (v == 'w'){range = (range | wRange);}
		}
		return (byte) range;
	}

	//warning: keep as name() rather than returning the field "outputname"
	/**
	 * Return a human-readable String for this Predicate
	 * @return the String
	 */
	public String outputName(){return name();}
	
	//warning: keep as name(), rather returning the filed "proverName"
	/**
	 * Return a prover-readable String for this Predicate.
	 * Calls the method {@link #name()}
	 * @return the String
	 */
	public String proverName(){return name();}
	
	/**
	 * Get the variable tuple for this Predicate.
	 * In practice this is the same as the human-readable String, but 
	 * this is an overloaded method, and we need both versions. 
	 * Calls the method {@link #name()}
	 * @return a char array of the variable tuple
	 */
	public char[] varTuple() {return varTuple;}
	
	/**
	 * Set the variable tuple for this Predicate 
	 * @param tup the tuple to set
	 */
	public void setVarTuple(char[] tup){varTuple = tup;}
	
	/**
	 * Get the variable range
	 * @return a byte representation of the variables in the Predicate
	 */
	public byte variableRange() {return variableRange;}
	
	/**
	 * Get the parent relation of this Predicate.
	 * This allows access to the fact table for this predicate in truth-value methods. 
	 * @return the parent relation 
	 */
	public Relation parentRelation(){return parentRelation;}
	

	/**
	 * Output a String representation: the Relation name plus the variable tuple 
	 * between brackets, eg: P(x,y).
	 * @return the String for the Predicate
	 */
	public String name(){
		if (this.varTuple == null) {return null;}

		StringBuilder name = new StringBuilder();
		int commasRemaining = parentRelation.arity()-1;
			
		name.append(parentRelation.name());
		name.append("(");
		
		for (char v : this.varTuple){
			name.append(v);
			if (commasRemaining > 0){
				name.append(",");				
				commasRemaining --;
			}
		}
		name.append(")");
		return name.toString();
	}

}

