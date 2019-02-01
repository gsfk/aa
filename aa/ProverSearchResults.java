package aa;

/**
 * Enum for return values from the theorem prover (Prover9) and 
 * the model builder (Mace4).
 * 
 */

public enum ProverSearchResults {
	PROOF_FOUND,
	NO_PROOF_FOUND,
	PROVER_TIMEOUT,
	PROVER_OTHER_RESULT,
	PROVER_INPUT_ERROR,
	PROVER_OTHER_ERROR,
	MACE4_COUNTEREXAMPLE_FOUND,
	MACE4_NO_MODELS_FOUND,
	MACE4_TIMEOUT,
	MACE4_OTHER_RESULT,
}	