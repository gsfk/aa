package aa;

/**
 * Decorator class for FormulaTrees.
 * Allows us to add a text label to common axioms (eg: "commutativity")
 * 
 */
public class CommonAxiom extends FormulaTree {

	private String label;
	
	public CommonAxiom(FormulaTree f, String l){
		super(f);
		label = l;
	}

	public String label(){return label;}
	
	
}
