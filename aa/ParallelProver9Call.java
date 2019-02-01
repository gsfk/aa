package aa;

import java.io.IOException;
import java.io.BufferedReader;
import java.io.InputStreamReader;


/**
 * Java Runnable implementation to handle calls to the theorem prover Prover9, 
 * which runs as a separate application in a separate process.
 *
 * Prover9 return values:<p>
 * 
 *    0:      proof found<p>
 *    1:      fatal error<p>
 *    2:      no proof found, premises exhausted<p>
 *    3:      max memory hit<p>
 *    4:      max time hit<p>
 *    5:      max given hit<p>
 *    6:      max kept hit<p>
 *    7:      Prover9 terminated<p>
 *  101:      Prover9 crashed<p>
 * 
 */
public class ParallelProver9Call implements Runnable {

	ParallelProver proverCall;

	public ParallelProver9Call(ParallelProver p){
		proverCall = p;
	}


	/**
	 * Call the OS to launch Prover9 in its own process
	 */
	@Override
	public void run() {
		try{
			int prover9ExitValue;

			String callString = proverCall.proverPath();
			callString += "prover9 -f analogy_prover_file.in";

			//external call to Prover9
			Runtime r = Runtime.getRuntime();

			//call prover with its own error handling
			//IO errors elsewhere are handled separately 
			try{
				proverCall.setProver9Process(r.exec(callString));
			} catch (Exception e){
				//System.err.println("error calling Prover9");
				e.printStackTrace();
			}

			BufferedReader in = new BufferedReader(new InputStreamReader(proverCall.prover9Process().getInputStream()));

			//gobble stdout to prevent IO blocking
			while ((!Thread.currentThread().isInterrupted() && ((in.readLine()) != null))) {;}

			proverCall.prover9Process().waitFor();  
			prover9ExitValue = proverCall.prover9Process().exitValue();

			//write result accordingly
			switch (prover9ExitValue){

			//proof found
			case 0: proverCall.setProver9Result(ProverSearchResults.PROOF_FOUND);
			break;

			//completed search, no proof found	
			case 2: proverCall.setProver9Result(ProverSearchResults.NO_PROOF_FOUND); 
			break;

			//timeout	
			case 4: proverCall.setProver9Result(ProverSearchResults.PROVER_TIMEOUT); 
			break;

			//errors
			case 1: proverCall.setProver9Result(ProverSearchResults.PROVER_INPUT_ERROR);
			break;

			case 7:
			case 101:
				proverCall.setProver9Result(ProverSearchResults.PROVER_OTHER_ERROR);	
				break;

				//other values	
			default: proverCall.setProver9Result(ProverSearchResults.PROVER_OTHER_RESULT);
				//System.err.println("Other result: " + prover9ExitValue);

			}
		} catch (IOException ignore){
			//do nothing
			//exceptions here are the result of race conditions about results we no longer care about:
			//(1)mace4 terminates before prover9 ->(2)assign results -> (3)close prover9 thread ->(4)destroy prover9 process
			//but IO error is thrown if prover9 manages to terminate between steps 1 and 4
		} catch (InterruptedException e) {
			//System.out.println("Prover9 interrupted, closing");
			//System.err.println(e);
		} catch (Exception e){
			//System.err.println("Prover9 other ERROR");
			e.printStackTrace();		}
	}

}
