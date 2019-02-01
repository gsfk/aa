package aa;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.util.ArrayList;
import java.util.Scanner;



public class Input {

	private final int DEFAULT_TIMEOUT_SECONDS = 3; 
	private int varLimit = -1;
	private int sizeLimit = -1;
	private int chunkSize = 0;
	private int timeout = DEFAULT_TIMEOUT_SECONDS;
	private String filename;

	private ArrayList<Type> types;
	private ArrayList<Relation> relations;

	//elements now associated with types 
	//only input lacking types has an "elements" collection
	private ArrayList<String> elements;

	private boolean searchCommonAxioms = true;

	public Input(File file) throws Exception {
		filename = file.getName();
		parse(file);
	}



	/**
	 * get all the types in the input 
	 * @return an ArrayList of Type objects
	 */
	public ArrayList<Type> types(){return types;}

	/**
	 * Return elements for an input lacking types
	 * @return a String ArrayList of elements
	 */
	public ArrayList<String> elements(){return elements;}
	
	/**
	 * Get all the relations in the input
	 * @return an ArrayList of Relation objects
	 */
	public ArrayList<Relation> relations(){return relations;}

	//WARNING: UNTYPED ELEMENTS ONLY, TODO
	/**
	 * get the number of untyped elements in the domain.
	 * This value should be zero for inputs with types
	 * @return the integer number of elements
	 */
	public int numElements() {return elements.size();}

	
	/**
	 * Get the name of the input file
	 * @return the name of the input file
	 */
	public String filename() {return filename;}

	/**
	 * Generate a distinct output filename for each input filename. 
	 * This avoid overwrites of unrelated output files. 
	 * For an input file named "myfile.txt", returns the name "myfile_output.txt"
	 * @return a String name for the output file
	 */
	public String generateOutputName(){
		String inputName = filename;
		int inputLength = inputName.length();
		String outputName = "";

		//remove ".txt" suffix if present
		if (inputLength > 4){
			String checkForDotTextSuffix = inputName.substring(inputLength - 4);
			if (checkForDotTextSuffix.equals(".txt")) {
				inputName = inputName.substring(0, (inputName.length() - 4));
			}
		}
		outputName += inputName + "_output.txt";
		return outputName;
	}

	
	
	
	
	
	
	
	
	
//	public String generateOutputName(){
//		String inputName = filename;
//		int inputLength = inputName.length();
//		String outputName = "output(";
//
//		//remove ".txt" suffix if present
//		if (inputLength > 4){
//			String checkForDotTextSuffix = inputName.substring(inputLength - 4);
//			if (checkForDotTextSuffix.equals(".txt")) {
//				inputName = inputName.substring(0, (inputName.length() - 4));
//			}
//		}
//		outputName += inputName + ").txt";
//		return outputName;
//	}

	
	
	
	/**
	 * Get the variable limit for the search space
	 * @return the variable limit
	 */
	public int varLimit() {return varLimit;}

	/**
	 * Get the size (number of operators) limit for the search space
	 * @return the size limit
	 */
	
	/**
	 * Set the variable limit for the search space
	 * @param n the new varible limit
	 */
	public void setVarLimit(int n){varLimit = n;}
	
	/**
	 * Get the size limit for the search space
	 * @return size limit
	 */
	public int sizeLimit() {return sizeLimit;}

	/**
	 * Set the size limit for the search space
	 * @param n new size limit
	 */
	public void setSizeLimit(int n){sizeLimit = n;}
	
	
	
	/**
	 * Get the Prover9/Mace4 timeout in seconds, the amount of time to wait for a result
	 * before giving up.
	 * @return timeout limit in seconds
	 */
	public int timeout() {return timeout;}

	/**
	 * Set Prover9/Mace4 timeout in seconds, the amount of time to wait for a result
	 * before giving up.
	 * @param n the new timeout
	 */
	public void setTimeout(int n){timeout = n;}
	
	
	/**
	 * Get whether this input uses partial search by only checking smaller "chunks" of premises 
	 * for each prover call
	 * @return true if chunking used
	 */
	public boolean useChunking() {return chunkSize > 0;}

//	/**
//	 * Set whether this input should use partial search by only checking smaller "chunks" of premises
//	 * for each prover call.
//	 * @param b set true to use chunking
//	 */
//	public void setUseChunking(boolean b) {useChunking = b;}

	/**
	 * Get the number of premises printed for each Prover9/Mace4 call.
	 * @return the number of premises printed
	 */
	public int chunkSize() {return chunkSize;}

	/**
	 * Set the number of premises to print for each Prover9/Mace4 call.
	 * Default is to print all premises each time, which is slower. 
	 */
	public void setChunkSize(int c){chunkSize = c;}

	/**
	 * Return true if this input has typed elements.
	 * @return true if domain elements are typed
	 */
	public boolean hasTypes(){
		return (types == null || types.size() != 0) && (elements == null || elements.size() == 0);
	}

	public boolean searchCommonAxioms(){return searchCommonAxioms;}
	
	public void setSearchCommonAxioms(boolean search){searchCommonAxioms = search;}
	
	
	
	/**
	 * Parse the input file
	 * @param file a File reference
	 * @throws Exception
	 */
	public void parse(File file) throws Exception{
		ArrayList<ArrayList<String>> tokens = fileTokens(file);
		int numLines = tokens.size();

		//main parser loop
		for (int i = 0; i < numLines; i++){
			ArrayList<String> line = tokens.get(i);
			String head = line.get(0);
			
			if (head.equals("varlimit")){
				varLimit = Integer.parseInt(line.get(1));	
			}
			if (head.equals("sizelimit")){
				sizeLimit = Integer.parseInt(line.get(1));	
			}			
			if (head.equals("chunksize")){
				chunkSize = Integer.parseInt(line.get(1));	
			}				
			if (head.equals("timeout")){
				timeout = Integer.parseInt(line.get(1));	
			}			
			if (head.equals("Types")){
				types = new ArrayList<Type>();
				ArrayList<ArrayList<String>> typeTokens = new ArrayList<ArrayList<String>>();
				int j = i+1;

				//collect all relevant string tokens and parse into Types
				while(!tokens.get(j).get(0).equals("Relations")){
					ArrayList<String> nextLine = tokens.get(j);
					typeTokens.add(nextLine);
					j++;
				}
				parseTypes(typeTokens);
			}	

			if (head.equals("Elements")){
				int length = line.size();
				elements = new ArrayList<String>();
				for (int j=1; j < length; j++){
					elements.add(line.get(j));
				}
			}

			if (head.equals("Relations")){
				relations = new ArrayList<Relation>();
				ArrayList<ArrayList<String>> relationTokens = new ArrayList<ArrayList<String>>();
				int j = i+1;

				while(!tokens.get(j).get(0).equals("Facts")){
					ArrayList<String> nextLine = tokens.get(j);
					relationTokens.add(nextLine);
					j++;
				}
				parseRelations(relationTokens);								
			}	

			if (head.equals("Facts")){
				ArrayList<ArrayList<String>> factTokens = new ArrayList<ArrayList<String>>();
				int j = i+1;

				while(j < numLines && !tokens.get(j).get(0).equals("end")){
					ArrayList<String> nextLine = tokens.get(j);
					factTokens.add(nextLine);
					j++;
				}
				parseFacts(factTokens);
			}		
		}

		try {
			verifyInput();
		} catch (Exception e) {
			throw e;
		}
	}



	public void parseTypes(ArrayList<ArrayList<String>> typeTokens){

		//for each line of input, create a type
		for (ArrayList<String> line: typeTokens){
			int length = line.size();
			Type t = new Type();
			t.setName(line.get(0));

			//add elements 
			for (int i = 1; i < length; i++){
				t.addElement(line.get(i));
			}

			//add this Type to the collection
			types.add(t);			
		}
	}

	//return the Type with this name

	/**
	 * Return the type matching a given name.
	 * Returns a new wildcard type if typeName is the underscore character.
	 * @param typeName the type name to match
	 * @return the matching Type
	 * @throws Exception 
	 */
	public Type getType(String typeName) throws Exception{
		if (types == null){
			throw new Exception("Error: type constraint with no types found, closing.");
		}
		
		if (typeName.equals("_")){
			return new WildType();
		}
		for (Type t: types){
			if (typeName.equals(t.name())){
				return t;
			} 
		}
		return null;
	}

	/**
	 * Given a relation name, return the matching relation.
	 * Returns null if no match.
	 * @param relationName a name of a relation
	 * @return the matching relation, if any
	 */
	public Relation getRelation(String relationName){
		for (Relation r: relations){
			if (relationName.equals(r.name())){
				return r;
			}
		}
		return null;
	}


	/**
	 * Given a collection of Strings describing a set of relations, create a corresponding
	 * collection of releation objects.
	 * 
	 * @param relationTokens a 2D ArrayList of Strings
	 * @throws Exception 
	 */
	public void parseRelations(ArrayList<ArrayList<String>> relationTokens) throws Exception{

		//for each line of input, create a Relation
		for (ArrayList<String> line: relationTokens){
			String typeName;
			int length = line.size();
			Relation r = new Relation();
			r.setName(line.get(0));
			ArrayList<Type> constraint = new ArrayList<Type>();
			if (length <= 1){
				constraint = null;
			} 

			//build constraint tuple 
			for (int i = 1; i < length; i++){
				typeName = line.get(i);
				Type t = getType(typeName);
				if (t == null){
					throw new Exception("Error: bad constraint for relation " + r.name());
				}
				constraint.add(t);
			} 
			if (constraint != null){
				r.setConstraint(constraint);
			}
			relations.add(r);
		}
	}

	
	/**
	 * Given a collection of Strings describing a set of facts, add each 
	 * fact to the corresponding relation.
	 * 
	 * @param factTokens a 2D ArrayList of Strings
	 * @throws Exception 
	 */
	public void parseFacts(ArrayList<ArrayList<String>> factTokens) throws Exception{
		//for each line of input, create a fact 
		for (ArrayList<String> line: factTokens){
			Relation r = getRelation(line.get(0));
			if (r == null){
				throw new Exception("Error: no relation " + line.get(0) + "found, closing.");
			}

			//build a fact from this line
			ArrayList<String> fact = new ArrayList<String>();
			int length = line.size();
			for (int i=1; i < length; i++){
				fact.add(line.get(i));
			}
			r.addFact(fact);
		}		
	}

	/**
	 * Break a text file into readable tokens.
	 * Removes whitespace and comments beginning with '%' from the input. 
	 * returns String ArrayList for each remaining line of the input file. 
	 * @param file the file to read
	 * @return a 2D ArrayList of String tokens
	 */
	public static ArrayList<ArrayList<String>> fileTokens(File file){
		ArrayList<ArrayList<String>> tokens = new ArrayList<ArrayList<String>>();

		Scanner infile = null;
		try{
			infile = new Scanner(new FileReader(file));
		} catch (FileNotFoundException igore){
			//ignore, checked elsewhere						
		}
		while (infile.hasNextLine()){
			ArrayList<String> lineData = lineParser(infile);	
			if (lineData.size() != 0){
				tokens.add(lineData);
			}
		}
		infile.close();
		return tokens;
	}

	/**
	 * Converts a single line of a text file into a collection of String tokens. 
	 * ignores whitespace and comments (comments begin with '%')
	 * @param infile a Scanner object
	 * @return a String ArrayList
	 */
	public static ArrayList<String> lineParser(Scanner infile){
		ArrayList<String> lineInfo = new ArrayList<String>();
		String line = infile.nextLine();
		String[] parts = line.split("[:\\(, \\)]");

		//dump comments
		if (parts.length > 0 && parts[0].length() > 0 && parts[0].charAt(0) == '%'){
			return lineInfo;
		}

		for (String s: parts){
			if (s.length() != 0){
				lineInfo.add(s);
			}
		}
		return lineInfo;
	}

	/**
	 * Error checking for input file
	 * @throws Exception 
	 */
	public void verifyInput() throws Exception{
		if (varLimit < 1 || varLimit > 4){
			throw new Exception("Bad varlimit, should be between one and four. Closing.");
		}

		if (chunkSize < 0){
			throw new Exception("Bad chunksize, closing.");
		}

		if (sizeLimit < 0){
			throw new Exception("Bad sizelimit, please include a sizelimit parameter of at least zero. Closing.");
		}

		if (timeout <= 0){
			throw new Exception("Bad timeout value, closing.");
		}


		for (Relation r : relations){
			if (r.facts() == null || r.facts().size() == 0){
				throw new Exception("Error: relation " + r.name() + " has no facts, closing.");
			}
			ArrayList<ArrayList<String>> f = r.facts();
			int arity = f.get(0).size();
			r.setArity(arity);

			//loop through facts for this relation, checking that arity is the same for all facts
			for (ArrayList<String> ff : f){
				if (arity != ff.size()){
					throw new Exception("Error, arity mismatch in facts for relation " + r.name() + ". Closing.");
				}
			}

			//check constraint for this relation, checking that arity is the same for all constraints
			if (r.constraint() != null && arity != r.constraint().size()){
				throw new Exception("Error, arity mismatch in constraints for relation " + r.name() + ". Closing.");
			}

			if (types != null && elements != null){
				throw new Exception("Error: elements should be either all typed or all untyped. Closing.");
			}

			
			//check for empty domains
			if ((types == null || types.size() ==0) && (elements == null || elements.size() == 0)){
				throw new Exception("Error: no elements found, closing.");
			}
			
			if (types != null){
				for (Type tt : types){
					if (tt.elements() == null || tt.elements().size() == 0){
						throw new Exception("Error: type " + tt.name() + " has no elements, closing.");
					}
				}
			} else  //else checked untyped domain
			{
				if (elements == null || elements.size()==0){
					throw new Exception("Error: no elements found, closing");
				}
			}
		}
	}

	
	/**
	 * Convert typed input to an equivalent untyped input.
	 * Calls methods {@link TypedFormulaGenerator#translateTypesToRelations(ArrayList)} 
	 * and {@link TypedFormulaGenerator#untypeElements(ArrayList)}.
	 */
	public void translatedToUntyped(){
		
		//convert types to relations   
		ArrayList<Relation> translatedTypes = TypedFormulaGenerator.translateTypesToRelations(types);

		// add all
		relations.addAll(translatedTypes);
		
		//convert elements    
		elements = TypedFormulaGenerator.untypeElements(types);
		
		//remove types
		types.clear();
	}
	
	
	
	
	
}
