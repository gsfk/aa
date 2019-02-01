package aa;

/**
 * Class for quantifier prefixes, used only in Hand Elimination methods.
 * 
 * Uses a simple characteristic vector to represent quantifier prefixes according to the scheme 
 * 0 = ∀, 1 = ∃!, 2 = ∃.
 *
 * @see aa.HandElimination
 */
public class Prefix{

	//is public faster?
	private int[] vector;
	private boolean included;

	public Prefix(int[] a){
		vector = a;
		included = true;
	}

	/**
	 * Remove this prefix from the prefix set
	 */
	public void remove() {included = false;}

	/**
	 * Return whether this prefix is included or not included in the prefix set
	 * @return true if included
	 */
	public boolean included() {return included;}
	
	/**
	 * Return the characteristic integer vector associated with this prefix.
	 * @return the prefix vector
	 */
	public int[] vector() {return vector;}
	


}