package aa;

/**
 * Abstract class for a node in an expression tree. 
 * @see aa.FormulaTree
 *
 */

public abstract class Node {
    protected String outputName;
    protected String proverName;

    /**
     * Default constructor
     */
    public Node(){}
    
    /**
     * Copy constructor
     * @param n Node to copy
     */
    public Node(Node n){
    	outputName = n.outputName;
    	proverName = n.proverName;
    }
    
    /**
     * Return a human-readable String representation of this node
     * @return String for this Node
     */
    public String outputName(){return outputName;}
    
    /**
     * Return a prover-readable String representation of this node
     * @return String for this Node
     */
    public String proverName(){return proverName;}
}
