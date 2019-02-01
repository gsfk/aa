package aa;

import java.util.ArrayList;

//warning: fact tables must be added after construction
//constructor returns an incomplete instance, this is not great


/**
 * Class to represent the relations present in the input.
 * 
 */
public class Relation {

	//predicate name
	private String name;

	//arity determined by parser
	private int arity; 

	//fact table 
	private ArrayList<ArrayList<String>> facts = new ArrayList<ArrayList<String>>();
	
	//NEW
	//typing constraint
	private ArrayList<Type> constraint;

	/**
	 * Default constructor
	 */
	public Relation(){};
	
	/**
	 * Copy constructor
	 * @param r the Relation to copy
	 */
	public Relation(Relation r){
		name = r.name;
		arity = r.arity;
		facts = r.facts;
	}
	
	/**
	 * Constructor for name only
	 * @param n
	 */
	public Relation(String n){
		name = n;
		arity = 0;
	}
	

	/**
	 * Returns the name of this Relation
	 * @return the name
	 */
	public String name(){return name;}
	
	//new
	/**
	 * Set the name of the Relation
	 * @param n the name
	 */
	public void setName(String n){name = n;}
	
	/**
	 * Add a fact to the fact table for this relation
	 * @param f an ArrayList of constants from the elements of the domain
	 */
	public void addFact(ArrayList<String> f){facts.add(f);}
	
	/**
	 * Set the arity of the relation
	 * @param a the integer value of the arity
	 */
	public void setArity(int a){arity = a;}
	
	/**
	 * Get the arity of this Relation
	 * @return the integer value of the arity
	 */
	public int arity(){return arity;}

	/**
	 * Return the fact table for this relation
	 * @return the fact table
	 */
	public ArrayList<ArrayList<String>> facts(){return facts;}

	/**
	 * Get the size of the fact table for this Relation
	 * @return the size
	 */
	public int numFacts(){return facts.size();}
	
	/**
	 * Lookup function for the fact table. 
	 * This is an arity-oblivious method, a significant improvement over the collection of 
	 * different arity-aware methods in earlier parts of the code.
	 * Input is a tuple of constants from the domain, returns true if this tuple is present 
	 * in the fact table
	 * 
	 * @param claim a tuple of constants (the claim to verify)
	 * @return true if this tuple is present in the fact table. 
	 */
	public boolean factTableLookup(ArrayList<String> claim){

		//TODO: throw arity mismatch error
		//current code returns false rather than error

		//iterate through fact table
		// no arity checks, no table size checks
		for (ArrayList<String> currentFact : this.facts){
			if (claim.equals(currentFact)){
				return true;
			}
		} 
		//reached end of table, fact not found
		return false; 	
	}
	
	
	/**
	 * Return the typing constraint for this relation. Returns null if none.
	 * @return an ArrayList representing the type constraint
	 */
	public ArrayList<Type> constraint(){return constraint;}
	
	/**
	 * Set the typing constraint for this relation
	 * @param c an ArrayList of types
	 */
	public void setConstraint(ArrayList<Type> c){constraint = c;}
	
	
}

