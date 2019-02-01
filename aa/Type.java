package aa;

import java.util.ArrayList;

/**
 * Class for types in the input, if any.
 * Elements can be a member of a type, types are also used for 
 * placing typing constraints on relations. 
 * 
 * @see {aa.TypedFormulaGenerator}
 */
public class Type {
	private String name;
	private ArrayList<String> elements;
	
	/**
	 * Default constructor
	 */
	public Type(){
		elements = new ArrayList<String>();
	}
	
	/**
	 * Constructor that takes a Type name and a list of its elements
	 * @param n
	 * @param e
	 */
	public Type(String n, ArrayList<String> e){
		name = n;
		elements = e;
	}
	
	public String name(){return name;}
	public void setName(String n){name = n;}
	
	public ArrayList<String> elements(){return elements;}
	public void addElement(String s){elements.add(s);}
	

	/**
	 * Equality checker for Types
	 * @param t
	 * @return
	 */
	public boolean matchesType (Type t){
		if (this instanceof WildType || t instanceof WildType){
			return true;
		}
		if (this.name().equals(t.name())){
			return true;
		}
		return false;
	}
	
	
	
	
	
}
