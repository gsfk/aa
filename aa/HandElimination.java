package aa;

import java.util.Set;
import java.util.LinkedHashSet;


/** 
 * <h1>Hand Elimination</h1> A collection of static methods for eliminating 
 * some redundant and false formulas "by hand", without external calls to a prover. 
 * 
 * This approach is motivated by this observation: <p>
 * 
 * ∀x P(x) true ⇒ ∃x P(x) true<p>
 * ∃!x P(x) true ⇒ ∃x P(x) true<p>
 * 
 * and in general many quantified formulas have obvious redundancies that can be produced by a
 * altering the quantifier prefix only. Since we are searching for axioms, any formulas clearly 
 * redundant to something else can be discarded without being considered. The main time expense in 
 * axiom search is number of calls to the prover; each redundancy eliminated is one fewer prover call. 
 * 
 * Given an unquantified formula F:
 * 
 * generate the set q1, q2, ... qn of quantifier prefixes for F
 * 
 * while quantifier prefixes remain:
 * <ul>
 * <li>get the next quantifier qi, test the truth value of qiF</li>
 * <li>if qiF true:</li>
 * <ul>
 * <li>add qiF to the list of true formulas</li>
 * <li>remove any prefix qj from the prefix set such that qiF ⇒ qjF </li>
 * </ul></ul>
 * 
 * 
 * Several methods are based on a compact "characteristic vector" representation of a 
 * quantifier prefix, using the following numbering:<p>
 * <ul>
 * <li>0: ∀</li>
 * <li>1: ∃!</li>
 * <li>2: ∃</li>
 * </ul>
 * 
 */
public class HandElimination {
	
	/**
	 * Private constructor, not instantiable, static methods only
	 */
	private HandElimination(){}
	
	/**
	 * Given a characteristic vector, produce the associated quantifier prefix tree
	 * @param prefixVector an integer array
	 * @return a FormulaTree object representing the quantifier prefix
	 */
	public static FormulaTree getQuantifierPrefix(int[] prefixVector){
		switch(prefixVector.length){
		case 1: return getPrefix1(prefixVector);
		case 2: return getPrefix2(prefixVector);
		case 3: return getPrefix3(prefixVector);
		case 4: return getPrefix4(prefixVector);
		default: System.err.println("quantifier prefix error");
		}
		//dummy return
		return null;
	}

	/**
	 * Given an integer vector, returns a FormulaTree quantifier prefix with one quantifier
	 * @param prefixVector the characteristic vector for the prefix
	 * @return a FormulaTree quantifier prefix
	 */
	public static FormulaTree getPrefix1(int[] prefixVector){
		return new FormulaTree(getQuantifierWithVar(prefixVector[0], 'x'));
	}

	/**
	 * Given an integer vector, returns a FormulaTree quantifier prefix with two quantifiers
	 * @param prefixVector the characteristic vector for the prefix
	 * @return a FormulaTree quantifier prefix
	 */
	public static FormulaTree getPrefix2(int[] prefixVector){
		FormulaTree qx = new FormulaTree(getQuantifierWithVar(prefixVector[0], 'x'));
		FormulaTree qy = new FormulaTree(getQuantifierWithVar(prefixVector[1], 'y'));
		
		qx.setLeft(qy);
		return qx;
	}

	/**
	 * Given an integer vector, returns a FormulaTree quantifier prefix with three quantifiers
	 * @param prefixVector the characteristic vector for the prefix
	 * @return a FormulaTree quantifier prefix
	 */
	public static FormulaTree getPrefix3(int[] prefixVector){
		FormulaTree qx = new FormulaTree(getQuantifierWithVar(prefixVector[0], 'x'));
		FormulaTree qy = new FormulaTree(getQuantifierWithVar(prefixVector[1], 'y'));
		FormulaTree qz = new FormulaTree(getQuantifierWithVar(prefixVector[2], 'z'));
	
		qx.setLeft(qy);
		qy.setLeft(qz);
		return qx;
	}

	/**
	 * Given an integer vector, returns a FormulaTree quantifier prefix with four quantifiers
	 * @param prefixVector the characteristic vector for the prefix
	 * @return a FormulaTree quantifier prefix
	 */
	public static FormulaTree getPrefix4(int[] prefixVector){
		FormulaTree qx = new FormulaTree(getQuantifierWithVar(prefixVector[0], 'x'));
		FormulaTree qy = new FormulaTree(getQuantifierWithVar(prefixVector[1], 'y'));
		FormulaTree qz = new FormulaTree(getQuantifierWithVar(prefixVector[2], 'z'));
		FormulaTree qw = new FormulaTree(getQuantifierWithVar(prefixVector[3], 'w'));
	
		qx.setLeft(qy);
		qy.setLeft(qz);
		qz.setLeft(qw);
		return qx;
	}

	/**
	 * Given an integer, returns a new quantifier of the appropriate type. 
	 * 
	 * 0 -> ∀<p>
	 * 1 -> ∃!<p>
	 * 2 -> ∃<p>
	 * @param q an integer value
	 * @return the associated Quantifier object
	 */
	public static Quantifier getQuantifier(int q){
		switch(q){
		case 0: return new UniversalQuantifier();
		case 1: return new UniquenessQuantifier();
		case 2: return new ExistentialQuantifier();
		default: System.err.println("quantifier error");
		}
		return null;	
	}

	/**
	 * Given an integer and a variable name, returns a new quantifier of the appropriate type
	 * associated with the given variable. 
	 * 
	* 0 -> ∀<p>
	* 1 _> ∃!<p>
	* 2 -> ∃<p>
	 * @param q an integer value
	 * @return the associated Quantifier object
	 */
	public static Quantifier getQuantifierWithVar(int q, char v){
		switch(q){
		case 0: return new UniversalQuantifier(v);
		case 1: return new UniquenessQuantifier(v);
		case 2: return new ExistentialQuantifier(v);
		default: System.err.println("quantifier error");
		}
		return null;	
	}

	//----- prefix removal methods ----//

	//given a set of Prefix objects and a set of vectors, set the "include" parameters to false
	//for all matching prefixes
	//--- betterRemove needs a better name ---
	
	/**
	 * Remove a subset of elements from a set of integer arrays.
	 * 
	 * Since we are iterating over the set at the same time as removing multiple members, 
	 * removing anything leads to Java concurrency errors, even when an iterator is used. 
	 * So in practice the elements to be removed are marked as removed and ignored on
	 * further iterations. 
	 * 
	 * This method effectively takes sets A and B as input, and removes elements of B from A,
	 * but only by tagging removed elements. The method is void, A is altered as a side effect.
	 *
	 * betterRemove() was better than the first remove() method, and I never bothered
	 * changing the name. 
	 * 
	 * @param original the array set to be altered
	 * @param toRemove the array to remove 
	 */
	public static void betterRemove(Set<Prefix> original, Set<int[]> toRemove){
		for (int[] v : toRemove){
			removeVector(original, v);
		}
	}

	/**
	 * Marks a characteristic vector as removed from a vector set.  
	 * 
	 * Void method alters the set passed as a parameter. The "include"
	 * parameter for the vector is set to false. Called by {@link HandElimination#betterRemove(Set, Set)
	 * betterRemove()}
	 * @param prefixSet the set to alter
	 * @param v the vector to mark as removed
	 */
	public static void removeVector(Set<Prefix> prefixSet, int[] v){
		for (Prefix p : prefixSet){
			if (samePrefix(p,v)){
				p.remove();
			}
		}
	}

	/**
	 * Check if int vector matches corresponding int array in a Prefix object.
	 * Note that Java .equals() for arrays does not work as expected.
	 * @param p a Prefix object
	 * @param v an int array
	 * @return true if both arguments represent the same quantifier prefix
	 */
	public static boolean samePrefix(Prefix p, int[] v){
		int length = v.length;
		int[] prefixVector = p.vector();
		boolean isMatch = true;
		if (length != prefixVector.length){System.err.println("vector length error");}

		for (int i = 0; i < length; i++){
			if (prefixVector[i] != v[i]){
				isMatch = false; 
				break;
			}
		}
		return isMatch;
	}



	/**
	 * Given a set of integer vectors, return a set of Prefix objects.
	 * @param vectors a set of int arrays representing a set of quantifier prefixes
	 * @return a set of FormulaTree objects for the associated quantifier prefixes
	 */
	public static Set<Prefix> generatePrefixSet(Set<int[]> vectors){
		Set<Prefix> s = new LinkedHashSet<Prefix>();
		for (int[] v : vectors){
			Prefix p = new Prefix(v);
			s.add(p);
		}
		return s;
	}


	
	//given a prefix Q, return some obviously false prefixes		//TODO: incorrect, remove
	//does all combinations of swaps of ∀ and ∃!
//	public static Set<int[]> falsePrefixes(int[] prefix){
//		Set<int[]> falsePrefixes = new LinkedHashSet<int[]>();
//		int numPositions = numSwapPositions(prefix);
//		int prefixLength = prefix.length;
//
//		//get all possible swap/don't swap options for each position
//		Set<int[]> swaps = getSwaps(numPositions);
//
//		//main loop through swap/don't swap vectors
//		for (int[] swap : swaps){
//			//counter for number of swaps
//			int swapIndex = 0;
//
//			//new redundant prefix
//			int[] f = new int[prefixLength];
//
//			for (int i = 0; i < prefixLength; i++){
//				if (prefix[i] == 0 || prefix[i] == 1){
//
//					//swap
//					if (swap[swapIndex] == 1){
//						//0 -> 1, 1-> 0
//						f[i] = (-1* prefix[i]%2) +1;
//						swapIndex++;
//					} else {
//						f[i] = prefix[i];
//						swapIndex++;
//					} 
//				} else {
//					f[i] = prefix[i];
//				}
//			} //end loop through prefix
//			falsePrefixes.add(f);
//		}
//		return falsePrefixes;
//	}

	
	
	//INCORRECT, ∃!∀y *(x,y) does not imply ∃!x∃y *(x,y)
	//only do swaps where uniqueness absent
	//swapping leftmost uniqueness for existence is fine, otherwise skip
	//full story is more complex, other cases are valid, see notes. 
	//for prefix ∀x∃!y∀z∀w, there are 9 redundant cases
	  	//old incorrect version returns 15 redundant
		//new "corrected" version returns zero
		//possible approach is to demote leftmost uniqueness quantifier (even if not leftmost quantifier)
		//and follow implications from there
	
	
	//num unique: 
	//0: swap as before
	//1: if leftmost, swap leftmost only, else ignore
	//to improve, see notes 
	
	
	/**
	 * Given a prefix Q, return prefixes redundant to Q except Q itself
	 * @param prefix the characteristic vector for a quantifier prefix 
	 * @return a set of characteristic vectors of prefixes redundant to Q
	 */
	public static Set<int[]> redundantPrefixes(int[] prefix){
				
		Set<int[]> redundants = new LinkedHashSet<int[]>();

		//skip this step if uniqueness quantifier present
		if (numUniquenessQuantifiers(prefix) > 0){
		
			//if leftmost, swap leftmost and return 
			if (hasUniquenessQuantifierLeftmost(prefix)){
				redundants.add(changeLeftmostToExistential(prefix));
			}
			
			//else:
			return redundants;
		}
		
		int numPositions = numSwapPositions(prefix);
		int prefixLength = prefix.length;

		//get all possible swap/don't swap options for each position
		Set<int[]> swaps = getSwaps(numPositions);

		//main loop through swap/don't swap vectors
		for (int[] swap : swaps){
			//counter for number of swaps
			int swapIndex = 0;

			//new redundant prefix
			int[] r = new int[prefixLength];

			for (int i = 0; i < prefixLength; i++){
				if (prefix[i] == 0 || prefix[i] == 1){

					//swap
					if (swap[swapIndex] == 1){
						r[i] = 2;
						swapIndex++;
					} else {
						r[i] = prefix[i];
						swapIndex++;
					} 
				} else {
					r[i] = prefix[i];
				}
			} //end loop through prefix
			redundants.add(r);
		}
		return redundants;
	}



	/**
	 * Returns true if a characteristic vector has a uniqueness quantifier in the leftmost 
	 * (outermost) position.
	 * 
	 * This corresponds to a quantifier prefix where the outermost quantifier is the 
	 * uniqueness quantifier.
	 * @param p a characteristic vector
	 * @return true if the outermost quantifier in the vector is the uniqueness quantifier
	 */
	public static boolean hasUniquenessQuantifierLeftmost(int[] p){
		final int uniquenessQuantifer = 1;
		if (p[0] == uniquenessQuantifer){
			return true;
		}
		return false;
	}
	
	
	/**
	 * Change the outermost quantifier in a characteristic vector to an existential 
	 * quantifier
	 * @param p the characteristic vector for a quantifier prefix
	 * @return p with the outmost quantifier changed to existential 
	 */
	public static int[] changeLeftmostToExistential(int[] p){
		p[0] = 2;
		return p;
	}
	
	

	//TODO: why existential ?
	/**		
	 * Given a quantifier prefix, returns the number of universal and existential quantifiers
	 * @param p a characteristic vector for a quantifier prefix 
	 * @return the total number of universal and uniqueness quantifiers in the vector
	 */
	public static int numSwapPositions(int[] p){
		int numSwap = 0;
		int length = p.length;
		for (int i = 0; i < length; i++){
			if (p[i] == 0 || p[i] == 1){
				numSwap++;
			}
		}
		return numSwap;
	}


	/**
	 * Given a quantifier prefix, returns the number of uniqueness quantifiers.
	 * @param p a characteristic vector for a quantifier prefix 
	 * @return the total number of uniqueness quantifiers in the vector
	 */
	public static int numUniquenessQuantifiers(int[] p){
		int numUnique = 0;
		int length = p.length;
		for (int i = 0; i < length; i++){
			if (p[i] == 1){
				numUnique++;
			}
		}
		return numUnique;
	}

	/**
	 * Produces all swap vectors except the all-zero no-swap vector.
	 * "Swap vectors" are 0/1 sequences, signifying "don't swap"/"swap",
	 * These are used by {@link #redundantPrefixes(int[]) redundantPrefixes()}
	 * to swap ∀ -> ∃ to produce redundant quantifier prefixes. 
	 * 
	 * getSwaps() returns the set of all 0/1 combinations of fixed length,
	 * except for the one that is only zeros, eg on input 2, returns (01, 10, 11).
	 * 
	 * @param numPositions the length of swap vectors needed
	 * @return the set of swap vectors
	 */
	public static Set<int[]> getSwaps(int numPositions){
		//either swap or don't swap for all positions
		Set<int[]> a = makeCombinations(numPositions, 2);
		a = removeZeroVector(a);
		return a;
	}

	/**
	 * Remove the all-zero array from a set of arrays
	 * @param s an array set
	 * @return an array set with no all-zero array
	 */
	public static Set<int[]> removeZeroVector(Set<int[]> s){
		Set<int[]> noZero = new LinkedHashSet<int[]>();
		for (int[] a : s){
			if (isZeroVector(a)){continue;}
			noZero.add(a);
		}
		return noZero;
	}

	/**
	 * Given an int array, returns true if the array includes only zeros 	
	 * @param arr an int array
	 * @return true if the array is all zeros
	 */
	public static boolean isZeroVector(int[] arr){
		int length = arr.length;
		for (int i = 0; i < length; i++){
			if (arr[i] != 0){
				return false;
			}
		}
		return true;
	}

	/**
	 * Generic combinatorial code that generates all integer combination of a 
	 * given length and number of elements.
	 * Calls the recursive method {@link #generateCombo(Set, int[], int, int, int) generateCombo()}.
	 * 
	 * @param numPositions the length of arrays to return
	 * @param numElements the number of elements to use
	 * @return all combinations as a set of integer arrays
	 */
	public static Set<int[]> makeCombinations(int numPositions, int numElements){
		int[] prefix = new int[numPositions];
		Set<int[]> collection = new LinkedHashSet<int[]>();
		generateCombo(collection, prefix, numElements, numPositions, 0);
		return collection;
	}

	/**
	 * Recursively generate all combinations of a given length and number of elements.
	 * Called by the parent function {@link #makeCombinations(int, int) makeCombinations()}.
	 * 
	 * Recursively adds to the "collection" set passed as an argument. 
	 * @param collection the set to add to
	 * @param prefix an array being recursively constructed
	 * @param numElements the number of elements in the combination
	 * @param numPositions the length of the combination
	 * @param num current position in array being constructed 
	 */
	public static void generateCombo(Set<int[]> collection, int[] prefix, int numElements, int numPositions, int num){
		if (num == numPositions){	    
			int[] prefixCopy = new int[prefix.length];
			System.arraycopy(prefix, 0, prefixCopy, 0, prefix.length);
			collection.add(prefixCopy);
			return;
		} else {
			for (int i = 0; i < numElements; i++){   
				prefix[num] = i;
				generateCombo(collection, prefix, numElements, numPositions, num+1);
			}
		}
	}



	//------ Debugging print methods ------------
	
	/**
	 * Debugging print method.
	 * @param s a set of integer arrays
	 */
	public static void printSet(Set<int[]> s){
		for (int[] arr: s){
			System.out.print("[");
			for (int i =0; i< arr.length; i++){
				System.out.print(arr[i]);
				if (i< arr.length-1){
					System.out.print(",");
				}
			}
			System.out.println("]");
		}
	}
	/**
	 * Debugging print method.
	 * @param s a set of Prefix objects
	 */
	public static void printPrefixSet(Set<Prefix> s){
		for (Prefix p: s){
			if (p.included()){
				printArray(p.vector());
			}
		}
	}
	
	
	/**
	 * Debugging print method.
	 * Return String of quantifier+variable representation of all prefixes in a Set 
	 * @param s a set of Prefix objects
	 * @return a String representation of the Prefix set
	 */
	public static String prefixSetString(Set<Prefix> s){			//working here
		StringBuilder str = new StringBuilder();
		for (Prefix p: s){
			if (p.included()){
				str.append(prefixString(p.vector()) + "\n");
			}
		}
		return str.toString();
	}	
	
	
	
	
	
	
	/**
	 * Debugging print method.
	 * @param vectors a set of integer arrays
	 */
	public static void printVectorSet(Set<int[]> vectors){
		for (int[] v : vectors){
			simpleIntPrefixPrint(v);
			System.out.println();
		}
	}

	/**
	 * Debug print method. 
	 * @param vectors integer vector set
	 * @return a String representation
	 */
	public static String vectorSetString(Set<int[]> vectors){
		StringBuilder s = new StringBuilder();
	for (int[] v : vectors){
		s.append(simpleIntPrefixString(v));
		s.append("\n");
	}
	return s.toString();
}
	
	
	
	
	/**
	 * Debugging print method.
	 * @param a an integer array
	 */
	public static void printArray(int[] a){
		int length = a.length;
		System.out.print("[");
		for (int i =0; i<length; i++){
			System.out.print(a[i]);
			if (i< length-1){
				System.out.print(",");
			}
		}
		System.out.println("]");
	}
	/**
	 * Debugging print method
	 * @param p an integer array
	 */
	public static void simpleIntPrefixPrint(int[] p){
		int length = p.length;
		char startVar = 'x';
		for (int i = 0; i< length; i++){
			System.out.print(printQuantifier(p[i]));
			System.out.print((char)(startVar + i));
		}		
	}

	/**
	 * Debugging print method
	 * @param p integer array
	 * @return a String representing a quantifier prefix
	 */
	public static String simpleIntPrefixString(int[] p){
		StringBuilder s = new StringBuilder();
		int length = p.length;
		char startVar = 'x';
		for (int i = 0; i< length; i++){
			s.append(printQuantifier(p[i]));
			s.append((char)(startVar + i));
		}		
		return s.toString();
	}
	
	/**
	 * Return a String representation of a Prefix
	 * @return the String
	 */
	public static String prefixString(int[] p){
		StringBuilder s = new StringBuilder();
		int length = p.length;
		char startVar = 'x';
		for (int i = 0; i< length; i++){
			s.append(printQuantifier(p[i]));
			s.append((char)(startVar + i) + " ");
		}		
		return s.toString();
	}	
	
	/**
	 * Debugging print method.
	 * 
	 * Returns the String for the quantifier associated with each int:
	 * 
	 * 0 -> ∀<p>
	 * 1 -> ∃!<p>
	 * 2 -> ∃<p>
	 * 
	 * @param n integer value (0,1 or 2)
	 * @return the String for the associated quantifier
	 */
	public static String printQuantifier(int n){
		switch (n){
		case 0: return "∀";
		case 1: return "∃!";
		case 2: return "∃";
		default: return null;
		}
	}



}
