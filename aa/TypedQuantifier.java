package aa;

/**
 * Abstract class for a Quantifier associated with a particular Relation 
 *
 */
public abstract class TypedQuantifier extends Quantifier {

	private Type type;
	
	public TypedQuantifier(){}
	
	public TypedQuantifier(Type t){
		super();
		type = t;
	}
	
	public Type type(){return type;}
	public void setType(Type t){type = t;}
}



