package aa;

/**
 * FormulaTree node for a Universal Quantifier with an associated type
 * @see aa.Quantifier
 */
public class TypedUniversalQuantifier extends TypedQuantifier {
	
	
	public TypedUniversalQuantifier(){}
	
	public TypedUniversalQuantifier(Type t){
		super(t);
		outputName = "∀" + type().name() + " ";
		
		//no prover name
		proverName = "";
	}
	
	/**
	 * Constructor for a TypedUniversalQuantifier with an associated variable 
	 */
	public TypedUniversalQuantifier(Type t, char v){
		super(t);
		outputName = "∀" + t.name() + " ";
		proverName = "";
		setVariable(v);
	}
	
	/**
	 * Copy constructor 
	 * @param q the quantifier to copy
	 */
	public TypedUniversalQuantifier(TypedQuantifier q){
		super(q.type());
		outputName = q.outputName;
		proverName = q.proverName;
		variable = q.variable;
	}
	
	/**
	 * Create a copy of this quantifier, but with a substituted variable
	 * @param v - the new variable
	 */
	public TypedUniversalQuantifier copyQuantifierWithNewVar(char v){
		TypedUniversalQuantifier q = new TypedUniversalQuantifier(this);
		q.setVariable(v);
		return q;
	}
	
}

