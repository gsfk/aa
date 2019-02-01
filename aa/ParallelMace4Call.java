package aa;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;

/**
 * Java Runnable implementation to handle calls to Mace4, which runs as a separate application in a separate process.
 * 
 * Mace4 checks for counterexample model at the same time that Prover9 looks for proofs. 
 *
 * 
 * 
 * 
 *  Mace4 return values: (from http://www.mcs.anl.gov/research/projects/AR/mace4/July-2005/doc/mace4.pdf)
 *  
 *  0:  The specified number of models (max models, default 1) was found.<p>
 *  1:  fatal error <p>
 *  2:  The search completed without finding any models. <p>
 *  3:  Some models were found, but the search completed before maxmodels models were found.<p>
 *  4:  Some models were found, but the time limit (maxseconds, default ∞) terminated the search before maxmodels models were found.<p>
 *  5:  The time limit (max seconds) terminated the search before any models were found.
 */
public class ParallelMace4Call implements Runnable {

	private ParallelProver proverCall;
	
	public ParallelMace4Call(ParallelProver p){
		proverCall = p;
	}
	
	/**
	 * Call the OS to run Mace4 in its own process
	 */
	@Override
	public void run() {
		try{
			int mace4ExitValue;
			String callString = proverCall.proverPath();
			callString += "mace4 -f analogy_prover_file.in";

			//external call to Mace4
			Runtime r = Runtime.getRuntime();
			
			//call Mace4 with separate error handling
			//allows us to distinguish between classes of IO errors
			try{
				proverCall.setMace4Process(r.exec(callString));
			} catch (Exception e){
				System.err.println("error calling Mace4");
				e.printStackTrace();
			}

			BufferedReader in = new BufferedReader(new InputStreamReader(proverCall.mace4Process().getInputStream()));

			//gobble stdout to prevent IO blocking
			while ((!Thread.currentThread().isInterrupted() && ((in.readLine()) != null))) {;}

			proverCall.mace4Process().waitFor();  
			mace4ExitValue = proverCall.mace4Process().exitValue();

			//write result accordingly
			switch (mace4ExitValue){

			//counterexample found
			case 0: proverCall.setMace4Result(ProverSearchResults.MACE4_COUNTEREXAMPLE_FOUND);
			break;
			//search completed with no models found	
			case 2: proverCall.setMace4Result(ProverSearchResults.MACE4_NO_MODELS_FOUND);
			break;
			//timeout with no models found
			case 5:proverCall.setMace4Result(ProverSearchResults.MACE4_TIMEOUT);
			break;
			//any other result 	
			default: proverCall.setMace4Result(ProverSearchResults.MACE4_OTHER_RESULT);
			}

		} catch (IOException ignore){
			//do nothing, a process we no longer care about was closed too soon
		} catch (InterruptedException ignore) {
			//System.out.println("Mace4 interrupted, closing");
			//System.err.println(e);
		} catch (Exception e){
			System.err.println("Mace4 IO ERROR");
			e.printStackTrace();
		}
	}

}




