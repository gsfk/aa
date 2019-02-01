package aa;

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Map;
import java.util.LinkedHashMap;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.CancellationException;

import javax.swing.SwingWorker;

/**
 * Class to handle parallel calls to both the theorem prover (Prover9) and a model builder (Mace4).
 * 
 * Extends Java's SwingWorker class used to do time-consuming background work without freezing a GUI.
 * @see javax.swing.SwingWorker
 *
 */
public class ParallelProver extends SwingWorker<Map<String, FormulaTree>, Void> {
	Input input;

	//all prover call fields
	private Process prover9Process = null;
	private Process mace4Process = null;	

	private String proverPath;

	private int numProver9Timeouts = 0;
	private int numProofsFound = 0;
	private int numNoProofsFound = 0;
	private int numProver9OtherResult = 0;
	private int numMace4Timeouts = 0;
	private int numCounterexamplesFound = 0;
	private int numMace4NoModelsFound = 0;
	private int numMace4OtherResult = 0;
	
	private volatile ProverSearchResults prover9Result, mace4Result;
	
	private final boolean DEBUG = false; 

	//input formula set
	private Map<String, FormulaTree> generatedFormulas;
	private int numFormulas;  
	
	//output formula set
	private Map<String, FormulaTree> minimalSet;


	public ParallelProver(Input i, Map<String, FormulaTree> formulas, String path){
		super();
		input = i;
		generatedFormulas = formulas;
		numFormulas = formulas.size();
		proverPath = path;
	}


	public String proverPath(){return proverPath;}

	public Process prover9Process(){return prover9Process;} 
	public Process mace4Process(){return mace4Process;}

	public void setProver9Process(Process p){prover9Process = p;} 
	public void setMace4Process(Process p){mace4Process = p;}

	public void setProver9Result(ProverSearchResults result){prover9Result = result;}
	public void setMace4Result(ProverSearchResults result){mace4Result = result;}

	public int numProver9Timeouts() {return numProver9Timeouts;}
	public int numProofsFound() {return numProofsFound;}
	public int numNoProofsFound() {return numNoProofsFound;}
	public int numProver9OtherResult() {return numProver9OtherResult;}
	public int numMace4Timeouts() {return numMace4Timeouts;}
	public int numCounterexamplesFound() {return numCounterexamplesFound;}
	public int numMace4NoModelsFound(){return numMace4NoModelsFound;}
	public int numMace4OtherResult() {return numMace4OtherResult;}
	public int minSetSize(){return minimalSet.size();}

	public Map<String, FormulaTree> minimalSet(){return minimalSet;}
	
	
	/**
	 * Background task for calls to Prover9 and Mace4
	 */
	@Override
	public Map<String, FormulaTree> doInBackground() {		

		ProverSearchResults outcome; 
		int premisesChunkSize = input.chunkSize();
		int numDone = 0;		

		//formula set to return
		minimalSet = new LinkedHashMap<String, FormulaTree>();

		//error checking
		if (premisesChunkSize >= numFormulas){
			//input.setUseChunking(false);
			//System.err.println("chunk size is larger than number of formulas, ignoring");
			//fireupdate																	TODO
		}

		
		//key set for iterating through formulas by index value
		Object[] formulaKeys = generatedFormulas.keySet().toArray();

		FormulaTree formulaToProve = null;

		//System.out.println("sending " + numFormulas + " formulas to prover");

		//can reverse order here with no increase in time complexity
		//for (int i = numFormulas -1; i <= 0; i--){
		
		
		//main loop: for each formula in the set, try to prove it from the others
//		for (int i = 0; i < numFormulas; i++){

		for (int i = numFormulas -1; i >= 0; i--){	
			
			
			if (isCancelled()){
				//System.err.println("ParallelProver cancelled");
				return null;
			}

			firePropertyChange("proverProgress", numDone, numDone+1);
			
			formulaToProve = generatedFormulas.get(formulaKeys[i]);
			
			try {
			
			//create a new prover input file, or overwrite an old one
			File outfile = new File("analogy_prover_file.in");
			outfile.createNewFile();

			// --- build input file ---- //
			FileWriter fileOutput = new FileWriter(outfile); 

			//Prover9 parameters
			fileOutput.write("if(Prover9).\n");

			//stop after finding one proof (starts counting from zero)
			fileOutput.write("assign(max_proofs, 0).\n");

			//suppress console output
			fileOutput.write("set(quiet).\n");
			fileOutput.write("clear(echo_input).\n");
			fileOutput.write("clear(print_initial_clauses).\n");
			fileOutput.write("clear(print_given).\n");
			fileOutput.write("clear(print_proofs).\n");

			//end Prover9 parameters
			fileOutput.write("end_if.\n");

			//Time limit for both Prover9 and Mace4
			fileOutput.write("assign(max_seconds, " + input.timeout() +").\n\n");

			//start list of premises
			fileOutput.write("formulas(sos).\n\n");

			//print premises
			if (input.useChunking()){
				outputPremiseChunks(fileOutput, generatedFormulas, formulaKeys, minimalSet, i, premisesChunkSize);
			} else {
				outputPremises(fileOutput, generatedFormulas, formulaKeys, i);
			}

			//done printing premises
			fileOutput.write("\nend_of_list.\n\n");

			//try to prove formula i
			fileOutput.write("formulas(goals).\n\n" + formulaToProve.outputProverFormula() + ".\n\n" + "end_of_list.\n");

			fileOutput.close();

			} catch (IOException e){
				if (DEBUG){
					System.err.println(e.getMessage());
				}
				//todo: send message
			}

			//invoke prover, try to prove f
			outcome = parallelProofSearch();
						
			if (outcome == null){
				//should be impossible to get here, assume no proof found
				outcome = ProverSearchResults.NO_PROOF_FOUND;		
				//TODO: send message, throw exception, something
				break;
			}

			if (DEBUG){
				System.out.println(outcome.name());
			}
			
			//set result 
			switch (outcome){

			//proof found, remove from minimal set
			case PROOF_FOUND:{
				numProofsFound++;
				
				//remove from premises printed in next round 
				formulaToProve.setIncludeInMinimalSet(false);
				
				//update inclusion status of this formula in the collection
				generatedFormulas.put(formulaToProve.outputTextFormula(), formulaToProve);
				break;
			}

			//mace4 completed search with no model found 
			//(unlikely case, proof will typically be returned first)
			case MACE4_NO_MODELS_FOUND:{
				numMace4NoModelsFound++;

				////remove from premises printed in next round 
				formulaToProve.setIncludeInMinimalSet(false);						//TODO: correct action?
				
				//update inclusion status of this formula in the collection
				generatedFormulas.put(formulaToProve.outputTextFormula(), formulaToProve);
				break;
			}

			//no models found, we only get here if prover9 timed out as well, so no proof found either
			case MACE4_TIMEOUT:{
				numMace4Timeouts++;
				minimalSet.put(formulaToProve.outputTextFormula(), formulaToProve);
				break;
			}

			//prover9 exhaustive search with no proof found, add to minimal set	
			//(usually expect mace4 counterexample to be found first)
			case NO_PROOF_FOUND: {
				numNoProofsFound++;
				minimalSet.put(formulaToProve.outputTextFormula(), formulaToProve);
				break;
			}

			//counterexample found, no proof exists, add to minimal set
			case MACE4_COUNTEREXAMPLE_FOUND:{
				numCounterexamplesFound++;
				minimalSet.put(formulaToProve.outputTextFormula(), formulaToProve);
				break;
			}

			//prover9 timeout with no proof found,  add to minimal set
			//(expect mace4 to return counterexample first)
			case PROVER_TIMEOUT:{
				numProver9Timeouts++;
				minimalSet.put(formulaToProve.outputTextFormula(), formulaToProve);
				break;
			}
			
			//other result, unused
			case PROVER_OTHER_RESULT: {
				numProver9OtherResult++;
				//System.err.println("PROVER OTHER RESULT: " + ProverValues.Prover9Result);
				break;
			}

			//errors and unused values
			case MACE4_OTHER_RESULT:{
				numMace4OtherResult++;
				//System.err.println("MACE4 OTHER RESULT: " + ProverValues.Mace4Result);
				break;
			}

			//something wrong with the input file
			case PROVER_INPUT_ERROR: {
				System.err.println("Prover error, bad input");
				//throw new IOException();
				break;
			}

			//prover crashed
			case PROVER_OTHER_ERROR: {
				System.err.println("Prover crashed");
			}

			}//end switch

			numDone++;
	
			if (DEBUG){
				System.out.println(numDone + "/" + numFormulas);
			}
			
		} //end main loop 
		
		return minimalSet;
	}

	/**
	 * Run when task finished, allows GUI to retrieve the minimal formula set found
	 */
	@Override
	public void done() {
		try {
			minimalSet = get();
		} catch (InterruptedException ignore) {
			//do nothing
		} catch (ExecutionException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} catch (CancellationException e){
			minimalSet = null;
		}
		
	}




	/**
	 * Run Prover9 and Mace4 in parallel on the same input
	 * @return the result as a ProverSearchResults enum value
	 */
	public ProverSearchResults parallelProofSearch(){

		ProverSearchResults result = null;
		Thread prover9Thread = new Thread(new ParallelProver9Call(this));
		Thread mace4Thread = new Thread(new ParallelMace4Call(this));

		prover9Thread.start();
		mace4Thread.start();

		boolean prover9Alive = prover9Thread.isAlive();
		boolean mace4Alive = mace4Thread.isAlive();
		boolean done = false;

		try{
			while(!done){
				prover9Alive = prover9Thread.isAlive();
				mace4Alive = mace4Thread.isAlive();

				if (!(prover9Alive && mace4Alive)){
					done = true;
				}
			}

			if (prover9Alive) {
				//if result is a timeout, wait for a better answer
				if (mace4Result == ProverSearchResults.MACE4_TIMEOUT){
					prover9Process.waitFor();
					result = prover9Result;
				} else {
					prover9Thread.interrupt();
					prover9Process.destroy(); 
					result = mace4Result;
				}
			}

			if (mace4Alive){
				if (prover9Result == ProverSearchResults.PROVER_TIMEOUT){
					mace4Process.waitFor();
					result = mace4Result;
				} else {
					mace4Thread.interrupt();
					if (mace4Process != null){mace4Process.destroy();}
					result = prover9Result;
				}
			} 

			//else both threads terminated	
			if (!prover9Alive && !mace4Alive){
				prover9Thread.interrupt();
				prover9Process.destroy();   
				mace4Thread.interrupt();
				mace4Process.destroy();
				result = prover9Result;
			}

		} catch (NullPointerException e){
			System.err.println("ParallelProver() null pointer");
			e.printStackTrace();
		} catch(Exception e){
			System.err.println("error running Parallel Prover");
			e.printStackTrace();
		} 

		if (result == null){
			prover9Process.destroy(); 
			mace4Process.destroy();
			result = prover9Result;
		}

		return result;
	}








	//STATIC HELPER METHODS

	/**
	 * print all premises to file
	 * @param fileOutput the output file to write to
	 * @param formulas a Java Map of the set of formulas
	 * @param formulaKeys the set of strings of all the formulas 
	 * @param currentFormula the current formula that we want to prove from the other formulas
	 */
	public static void outputPremises(FileWriter fileOutput, Map<String, FormulaTree> formulas, Object[] formulaKeys, int currentFormula){
		int numFormulas = formulas.size();
		FormulaTree currentPremise;

		try{
			for (int j = 0; j < numFormulas; j++ ){

				//skip formula we're trying to prove
				if (j == currentFormula){continue;}

				//output any other true formula not yet eliminated
				currentPremise = formulas.get(formulaKeys[j]);
				if (currentPremise.includeInMinimalSet()){
					fileOutput.write(currentPremise.outputProverFormula() + ".\n");
				}				
			}
		} catch (IOException e){
			e.printStackTrace();
		}
	}

	/**
	 * Print only smaller chunks of premises to file.
	 * Used for partial search. 
	 * @param fileOutput the output file to write to
	 * @param formulas a Java Map of the set of formulas
	 * @param formulaKeys the set of strings of all the formulas 
	 * @param minimalSet the current minimal set of formulas
	 * @param currentFormulaIndex index of the formula being checked for redundancy
	 * @param chunkSize the number of formulas to check against
	 */
	public static void outputPremiseChunks(FileWriter fileOutput, 
			Map<String, FormulaTree> formulas, 
			Object[] formulaKeys, 
			Map<String, FormulaTree> minimalSet, 
			int currentFormulaIndex, 
			int chunkSize){

		FormulaTree currentPremise;
		int numFormulas = formulas.size();
		int firstPremise = 0;
		int lastPremise = numFormulas-1;
		int halfChunk = chunkSize/2;
		boolean canFitUpperHalfChunk = currentFormulaIndex >= halfChunk;
		boolean canFitLowerHalfChunk = currentFormulaIndex <= numFormulas - halfChunk -1;
		if (chunkSize >= numFormulas){
			outputPremises(fileOutput, formulas, formulaKeys, currentFormulaIndex);
			return;
		}

		//-- begin cases--
		if (canFitUpperHalfChunk && canFitLowerHalfChunk){
			firstPremise = currentFormulaIndex - halfChunk;
			lastPremise = currentFormulaIndex + halfChunk;
		}

		if (!canFitUpperHalfChunk && canFitLowerHalfChunk){
			firstPremise = 0;
			lastPremise = chunkSize;
		}

		if (canFitUpperHalfChunk && !canFitLowerHalfChunk){
			firstPremise = numFormulas - chunkSize - 1;
			lastPremise = numFormulas-1;
		}

		//can't happen, handled elsewhere
		if (!canFitUpperHalfChunk && !canFitLowerHalfChunk){
			//System.out.println("chunking error");
		}


		try{
			for (int premiseIndex = firstPremise; premiseIndex <= lastPremise; premiseIndex++){

				//skip formula we're trying to prove
				if (premiseIndex == currentFormulaIndex){continue;}

				//output any other true formula not yet eliminated
				//updated July 2108 to remove deprecated truth value check before printing
				currentPremise = formulas.get(formulaKeys[premiseIndex]);
				if (currentPremise.includeInMinimalSet()){
					fileOutput.write(currentPremise.outputProverFormula() + ".\n");
				}				
			}

		} catch (IOException e){
			e.printStackTrace();
		}
	}


	
	
	/**
	 * Print only smaller chunks of premises to file, improved version
	 * Guaranteed to print the number of premises requested if they exists. Previous method
	 * counted formulas already proved away, so often printed many fewer premises.
	 * 	 * 
	 * Used for partial search. 
	 * @param fileOutput the output file to write to
	 * @param formulas a Java Map of the set of formulas
	 * @param formulaKeys the set of strings of all the formulas 
	 * @param minimalSet the current minimal set of formulas
	 * @param currentFormulaIndex index of the formula being checked for redundancy
	 * @param chunkSize the number of formulas to check against
	 */
	public static void outputPremiseChunksBetter(FileWriter fileOutput, 
			Map<String, FormulaTree> formulas, 
			Object[] formulaKeys, 
			Map<String, FormulaTree> minimalSet, 
			int currentFormulaIndex, 
			int chunkSize){

		ArrayList<Integer> minSetInidices = minSetIndexes(formulaKeys, formulas);
		
		
		FormulaTree currentPremise;
		int currentIndex;
		int numFormulas = minSetInidices.size();
		int firstPremise = 0;
		int lastPremise = numFormulas-1;
		int halfChunk = chunkSize/2;
		boolean canFitUpperHalfChunk = currentFormulaIndex >= halfChunk;
		boolean canFitLowerHalfChunk = currentFormulaIndex <= numFormulas - halfChunk -1;
		if (chunkSize >= numFormulas){
			outputPremises(fileOutput, formulas, formulaKeys, currentFormulaIndex);
			return;
		}

		//-- begin cases--
		if (canFitUpperHalfChunk && canFitLowerHalfChunk){
			firstPremise = currentFormulaIndex - halfChunk;
			lastPremise = currentFormulaIndex + halfChunk;
		}

		if (!canFitUpperHalfChunk && canFitLowerHalfChunk){
			firstPremise = 0;
			lastPremise = chunkSize;
		}

		if (canFitUpperHalfChunk && !canFitLowerHalfChunk){
			firstPremise = numFormulas - chunkSize - 1;
			lastPremise = numFormulas-1;
		}

		//can't happen, handled elsewhere
		if (!canFitUpperHalfChunk && !canFitLowerHalfChunk){
			//System.out.println("chunking error");
		}


		try{
			for (int premiseIndex = firstPremise; premiseIndex <= lastPremise; premiseIndex++){

				//get next valid index 
				currentIndex = minSetInidices.get(premiseIndex);
				
				//don't print the premise you're trying to prove
				if (currentIndex == currentFormulaIndex){continue;}

				//output any other true formula not yet eliminated
				currentPremise = formulas.get(formulaKeys[currentIndex]);
							
				if (currentPremise.includeInMinimalSet()){
					fileOutput.write(currentPremise.outputProverFormula() + ".\n");
				} else {
					System.err.println("Error: tried to print redundant premise.");
				}
			}

		} catch (IOException e){
			e.printStackTrace();
		}
	}

	
	private static ArrayList<Integer> minSetIndexes(Object[] formulaKeys, Map<String, FormulaTree> formulas){
		ArrayList<Integer> minSetIndices = new ArrayList<Integer>();
		int index;
		int size = formulas.size();
		FormulaTree current;
		for (index = 0; index < size; index++){
			current = formulas.get(formulaKeys[index]);
			if (current.includeInMinimalSet())
				minSetIndices.add(index);
			}
		return minSetIndices;
		
	}
	
	
	
	
}

