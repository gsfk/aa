package aa;

/**
 * FormulaTree node for a Universal Quantifier with an associated type
 * @see aa.Quantifier
 */
public class TypedExistentialQuantifier extends TypedQuantifier {
	
	public TypedExistentialQuantifier(){}
	
	public TypedExistentialQuantifier(Type t){
		super(t);
		outputName = "∃ " + t.name() + " ";
		
		//no prover name
		proverName = "";
	}
	
	/**
	 * Constructor for a TypedUniversalQuantifier with an associated variable 
	 */
	public TypedExistentialQuantifier(Type t, char v){
		super(t);
		outputName = "∃ " + t.name() + " ";
		proverName = "";
		setVariable(v);
	}
	
	/**
	 * Copy constructor 
	 * @param q the quantifier to copy
	 */
	public TypedExistentialQuantifier(TypedQuantifier q){
		super(q.type());
		outputName = q.outputName;
		proverName = q.proverName;
		variable = q.variable;
	}
	
	/**
	 * Create a copy of this quantifier, but with a substituted variable
	 * @param v - the new variable
	 */
	public TypedExistentialQuantifier copyQuantifierWithNewVar(char v){
		TypedExistentialQuantifier q = new TypedExistentialQuantifier(this);
		q.setVariable(v);
		return q;
	}
	
}

