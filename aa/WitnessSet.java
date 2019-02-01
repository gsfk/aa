package aa;

import java.util.ArrayList;
import java.util.Map;

/**
 * Class used for debugging output only.
 * Allows printing of variable substitutions and truth values during 
 * truth-value checking. Used only in the method 
 * {@link aa.FormulaTree#debugValueRecurse(ArrayList, Map, boolean)}.
 */
public class WitnessSet {

	private boolean truthValue;
	private ArrayList<Map<Character, String>> witnesses;
	
	public WitnessSet(){
		witnesses = new ArrayList<Map<Character, String>>();
	}
	
	/**
	 * Return the truth value
	 * @return the truth value
	 */
	public boolean truthValue(){return truthValue;}
	
	/**
	 * Set the truth value
	 * @param v the truth value
	 */
	public void setTruthValue(boolean v){truthValue = v;}
	
	/**
	 * Return the the set of substitutions
	 * @return the set
	 */
	public ArrayList<Map<Character, String>> witnessSet(){return witnesses;}
	
	/**
	 * Add a substitution to the witness set
	 * @param s the substitution to add
	 */
	public void addWitness(Map<Character, String> s){witnesses.add(s);}
	
	
}
