package aa;

import java.awt.Color;
import java.awt.EventQueue;
import java.awt.event.ActionListener;
import java.awt.event.ActionEvent;

import javax.swing.JFrame;
import javax.swing.JPanel;
import javax.swing.border.EmptyBorder;
import javax.swing.GroupLayout;
import javax.swing.GroupLayout.Alignment;
import javax.swing.JButton;
import javax.swing.JFileChooser;
import javax.swing.JScrollPane;
import javax.swing.LayoutStyle.ComponentPlacement;
import javax.swing.JLabel;
import javax.swing.SpinnerModel;
import javax.swing.SpinnerNumberModel;
import javax.swing.SwingUtilities;
import javax.swing.UIManager;
import javax.swing.JSpinner;
import javax.swing.JCheckBox;
import javax.swing.ProgressMonitor;
import javax.swing.border.EtchedBorder;
import javax.swing.event.ChangeListener;
import javax.swing.event.ChangeEvent;
import javax.swing.text.BadLocationException;
import javax.swing.text.MutableAttributeSet;
import javax.swing.text.SimpleAttributeSet;
import javax.swing.text.StyleConstants;
import javax.swing.text.StyledDocument;
import javax.swing.text.Style;
import javax.swing.text.TabSet;
import javax.swing.text.TabStop;
import javax.swing.JTextPane;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.PrintWriter;
import java.text.DecimalFormat;
import java.util.Map;
import java.util.concurrent.ExecutionException;
import java.beans.PropertyChangeEvent;
import java.beans.PropertyChangeListener;


/**
 * aa: brute force search for axioms.
 * full documentation available in javadoc format
 *
 * Class for GUI, main method, control flow
 * 
 *
 */
@SuppressWarnings("serial")
public class AaGui extends JFrame {

	//GUI fields
	private JPanel contentPane;
	private JTextPane textConsoleArea;
	private JButton linkProverButton;
	private ProgressMonitor progressMonitor;
	private JTextPane axiomOutputArea;
	private Boolean proverIsConnected = false;
	private JButton openFileButton;
	private JButton startSearchButton;
	private StyledDocument consoleDoc;
	private StyledDocument axiomDoc;
	private Style redText;
	private Style blackText;
	private Style axiomText;
	private JPanel panel;
	private JSpinner spinnerChunkSize;
	private JSpinner varLimitSpinner;
	private JSpinner sizeLimitSpinner;
	private JSpinner timeoutSpinner;
	private JPanel panel_2;
	private JLabel lblFormulaGeneration;
	private JLabel lblTheoremProverCalls;
	private JCheckBox commonAxiomsCheckBox;

	//axiom search fields
	private final int DEFAULT_NUM_PREMISES = 50;
	private Input input;					
	private FormulaGenerator formGen;
	private TypedFormulaGenerator typedFormGen;
	private ParallelProver proverCalls;
	private Map<String, FormulaTree> firstMinSet;
	private Map<String, FormulaTree> minSetFromProver;
	private boolean doneGeneration = false;
	private boolean doneTypedGeneration = false; 
	private boolean doneProverCalls = false;
	private boolean isRepeatSearch = false;
	private boolean GUIoutputWritten = false; 
	private boolean cancelNotified = false;
	private String proverPath;
	private File file1, file2;
	private final boolean DEBUG = false;
	private int numProverCalls;
	private int proverProgress;
	private File currentDirectory = null;
	private long startTime, formGenEndTime, proverTime, runTime; 
	private String outputFileName;
	private DecimalFormat decimal = new DecimalFormat("#.#");
	
	/**
	 * handles communication with background threads.
	 * 
	 * Directs most of the control flow in the program in response to state changes
	 * signalled by background threads. 
	 */
	private PropertyChangeListener propertyChangeListener = new PropertyChangeListener() {
		public void propertyChange(PropertyChangeEvent evt) {
			String propertyName = evt.getPropertyName();
			int value = -1;

			if (propertyName.equals("state")){
				//	do nothing
			}
			
			if (propertyName.equals("common")){
				//progressMonitor.setProgress(0);  
				progressMonitor.setNote("common axioms...");
				appendConsole("common axioms...\n");
				
			}
			
			
			if (propertyName.equals("generation") || propertyName.equals("typed generation")){
				progressMonitor.setProgress(0);  			///makes progressMonitor visible
				value = (Integer) evt.getNewValue();
				String message;
				if (!propertyName.equals("common")){
					message = "Generating size " + (value-1) + "... \n";
				} else {
					message = "common axioms... ";
				}
				progressMonitor.setNote(message);	
			}

			//if Formula Generation complete without being cancelled, start prover calls
			//move this to its own method, all values are globals			
			if (formGen != null &&formGen.isDone() 
					&& !doneGeneration && !formGen.isCancelled() && !isRepeatSearch){
				appendConsole("Formula generation complete\n");
				doneGeneration = true;
				formGenEndTime = System.currentTimeMillis();
				proverTime = formGenEndTime;
				
				try {
					firstMinSet = formGen.get();					
				} catch (InterruptedException e) {
					appendErrorConsole("Formula Generation interrupted: " + e.getMessage());
					resetForNewSearch();
					return;
				} catch (ExecutionException e) {
					appendErrorConsole("Formula Generation error: " + e.getMessage());
					progressMonitor.close();
					e.printStackTrace();
					resetForNewSearch();
					return;
				}
				appendConsole("forwarding " + firstMinSet.size() + " formulas to prover.\n");

				launchProver();
			}

			//if Typed Formula Generation complete without being cancelled, start prover calls
			//move this to its own method, all values are globals			
			if (typedFormGen != null && typedFormGen.isDone() 
					&& !doneTypedGeneration && !typedFormGen.isCancelled() && !isRepeatSearch){
				appendConsole("Typed formula generation complete\n");
				doneTypedGeneration = true;
				formGenEndTime = System.currentTimeMillis();
				proverTime = formGenEndTime;
				
				try {
					firstMinSet = typedFormGen.get();					
				} catch (InterruptedException e) {
					appendErrorConsole("Typed Formula Generation interrupted: " + e.getMessage());
					resetForNewSearch();
					return;
				} catch (ExecutionException e) {
					appendErrorConsole("Typed Formula Generation error: " + e.getMessage());
					e.printStackTrace();
					progressMonitor.close();
					resetForNewSearch();
					return;
				} catch (Exception e){
					appendErrorConsole(e.getMessage());
				}
				appendConsole("forwarding " + firstMinSet.size() + " formulas to prover.\n");

				launchProver();
			}			

			//update progress of prover calls
			if (propertyName.equals("proverProgress")) {
				proverProgress = (Integer) evt.getNewValue();

				//compute percentage progress
				int percentProgress = (int)Math.floor(100*proverProgress/(double)numProverCalls);
				progressMonitor.setProgress(percentProgress);
				String message = ("Prover calls: " + proverProgress + "/" + numProverCalls);
				progressMonitor.setNote(message);
				
				axiomOutputArea.setText("");
				appendAxiomArea(proverStats());
				//printProverStats();
			}

			//if prover calls complete without being cancelled, finished
			if (!doneProverCalls && proverCalls != null && proverCalls.isDone() && !proverCalls.isCancelled()){
				doneProverCalls = true;
				minSetFromProver = proverCalls.minimalSet();
				appendConsole("Prover calls complete, full details written to file " + input.generateOutputName() + "\n");
				appendConsole("Click \"Search again\" to continue searching for redundancy in the minimum set\n");
				proverTime = System.currentTimeMillis() - proverTime;
				runTime = System.currentTimeMillis() - startTime;
		
				//print to GUI when available
				Runnable pushResults = new Runnable() {
					public void run() {
						axiomOutputArea.setText("");
						appendAxiomArea(proverStats() + "\n");
						appendAxiomArea(results());
					}
				};
				SwingUtilities.invokeLater(pushResults);
				if (isRepeatSearch){
					writeRepeatResultsToFile();
				} else {
					writeResultsToFile();
				}
				resetForRepeatSearch();				
			}

			if (progressMonitor.isCanceled()) {
				if (!cancelNotified){
					appendErrorConsole("Cancelled.\n"); 
					cancelNotified = true;
				}
				if (formGen != null) {formGen.cancel(true);}
				if (typedFormGen != null) {typedFormGen.cancel(true);}
				if (proverCalls != null) {proverCalls.cancel(true);}
				resetForNewSearch();
			}
		}
	};





	/**
	 * Main method, launch the application.
	 */
	public static void main(String[] args) {
		EventQueue.invokeLater(new Runnable() {
			public void run() {
				AaGui frame = null;
				try {
					frame = new AaGui();
					frame.setVisible(true);
					frame.setTitle("aa");
				} catch (Exception e) {
					e.printStackTrace();
					frame.appendErrorConsole(e.getMessage());
				}
			}
		});
	}

	/**
	 * GUI constructor.
	 * 
	 * Includes some ugly layout code autogenerated by the GUI tools.
	 */
	public AaGui() {
		file1 = null;
		file2 = null;
		setDefaultCloseOperation(JFrame.EXIT_ON_CLOSE);
		setBounds(0, 20, 950, 780);
		contentPane = new JPanel();
		contentPane.setBorder(new EmptyBorder(5, 5, 5, 5));
		setContentPane(contentPane);

		openFileButton = new JButton("Open file");
		openFileButton.addActionListener(new ActionListener() {
			public void actionPerformed(ActionEvent e) {

				resetForNewSearch();

				//get file 
				file1 = openFile();
				startSearchButton.setEnabled(true);

				//parse input										//*** PARSER
				try {
					input = new Input(file1);
				} catch (Exception exc){
					//error message to user console
					appendErrorConsole("Error: " + exc.getMessage());
				}

				//set to default number of premises if none specified
				if (!input.useChunking()){
					input.setChunkSize(DEFAULT_NUM_PREMISES);
				}

				//set visible input controls to match file
				setSearchControls();

				printInputSummary();								
			}
		});

		JScrollPane scrollPane = new JScrollPane();

		linkProverButton = new JButton("Link prover");
		linkProverButton.addActionListener(new ActionListener() {
			public void actionPerformed(ActionEvent e) {
				linkProver();
			}
		});

		JScrollPane scrollPane_1 = new JScrollPane();

		SpinnerModel sm = new SpinnerNumberModel(100, 0, 500, 1);

		startSearchButton = new JButton("Start");
		startSearchButton.setEnabled(false);

		axiomOutputArea = new JTextPane();
		scrollPane_1.setViewportView(axiomOutputArea);

		textConsoleArea = new JTextPane();
		scrollPane.setViewportView(textConsoleArea);

		initTextConsoleDocument();
		initAxiomOutputDocument();



		//START - SINGLE FILE MODE												//START SEARCH HERE
		startSearchButton.addActionListener(new ActionListener() {
			public void actionPerformed(ActionEvent e) {

				//launch progressMonitor
				UIManager.put("ProgressMonitor.progressText", "Generating minimal set");
				progressMonitor = new ProgressMonitor(textConsoleArea,
						"Generating minimal set", "", -2, 100);
				progressMonitor.setProgress(-3);
				progressMonitor.setMillisToDecideToPopup(100);
				startSearchButton.setEnabled(false);

				//prevent multiple prints
				GUIoutputWritten = false;

				//allow another round of prover calls
				doneProverCalls = false;  	

				//reset flag, prevents multiple cancel notifications
				cancelNotified = false; 	

				startTime = System.currentTimeMillis();
				//generate all formulas, unless this is a repeat search
				if (!isRepeatSearch){

					//typed formula generation
					if (input.hasTypes()){
						appendConsole("Launching typed formula generation...\n");
						typedFormGen = new TypedFormulaGenerator(input);
						typedFormGen.addPropertyChangeListener(propertyChangeListener);
						typedFormGen.execute();


					} else { //else untyped

						//launch Formula Generation as a background task
						formGen = new FormulaGenerator(input);
						formGen.addPropertyChangeListener(propertyChangeListener);
						formGen.execute();
					}
				} else {

					//else run prover on old axioms, skip formula generation
					appendConsole("repeat search through minimal set for " + input.filename() + "... \n");

					proverCalls = new ParallelProver(input, firstMinSet, proverPath);				
					proverCalls.addPropertyChangeListener(propertyChangeListener);
					proverTime = System.currentTimeMillis();
					
					//launch prover calls in background										//PROVER CALLED HERE
					proverCalls.execute();			
				}
			}
		});

		panel = new JPanel();
		panel.setToolTipText("Perform a faster search by checking each putative axiom against a subset of true formulas. This leads to larger axioms sets, which can be further reduced by additional searches. ");
		panel.setBorder(new EtchedBorder(EtchedBorder.LOWERED, null, null));
		spinnerChunkSize = new JSpinner(sm);
		spinnerChunkSize.setEnabled(false);
		spinnerChunkSize.addChangeListener(new ChangeListener() {
			public void stateChanged(ChangeEvent e) {
				int value = (int) spinnerChunkSize.getValue();
				if (input != null){				
					input.setChunkSize(value);
				}
			}
		});
		panel_2 = new JPanel();
		panel_2.setBorder(new EtchedBorder(EtchedBorder.LOWERED, null, null));

		GroupLayout gl_contentPane = new GroupLayout(contentPane);
		gl_contentPane.setHorizontalGroup(
				gl_contentPane.createParallelGroup(Alignment.LEADING)
				.addComponent(scrollPane, Alignment.TRAILING, GroupLayout.DEFAULT_SIZE, 940, Short.MAX_VALUE)
				.addComponent(scrollPane_1, Alignment.TRAILING, GroupLayout.DEFAULT_SIZE, 940, Short.MAX_VALUE)
				.addGroup(gl_contentPane.createSequentialGroup()
						.addGroup(gl_contentPane.createParallelGroup(Alignment.TRAILING)
								.addGroup(gl_contentPane.createSequentialGroup()
										.addComponent(openFileButton, GroupLayout.PREFERRED_SIZE, 115, GroupLayout.PREFERRED_SIZE)
										.addPreferredGap(ComponentPlacement.RELATED)
										.addComponent(startSearchButton, GroupLayout.PREFERRED_SIZE, 121, GroupLayout.PREFERRED_SIZE)
										.addPreferredGap(ComponentPlacement.RELATED, 577, Short.MAX_VALUE)
										.addComponent(linkProverButton))
										.addGroup(gl_contentPane.createSequentialGroup()
												.addComponent(panel_2, GroupLayout.DEFAULT_SIZE, 424, Short.MAX_VALUE)
												.addPreferredGap(ComponentPlacement.RELATED)
												.addComponent(panel, GroupLayout.PREFERRED_SIZE, 504, GroupLayout.PREFERRED_SIZE)))
												.addContainerGap())
				);
		gl_contentPane.setVerticalGroup(
				gl_contentPane.createParallelGroup(Alignment.LEADING)
				.addGroup(gl_contentPane.createSequentialGroup()
						.addGap(6)
						.addGroup(gl_contentPane.createParallelGroup(Alignment.BASELINE)
								.addComponent(openFileButton)
								.addComponent(startSearchButton)
								.addComponent(linkProverButton))
								.addPreferredGap(ComponentPlacement.RELATED)
								.addGroup(gl_contentPane.createParallelGroup(Alignment.LEADING)
										.addComponent(panel_2, GroupLayout.DEFAULT_SIZE, 79, Short.MAX_VALUE)
										.addComponent(panel, 0, 0, Short.MAX_VALUE))
										.addPreferredGap(ComponentPlacement.RELATED)
										.addComponent(scrollPane, GroupLayout.PREFERRED_SIZE, 146, GroupLayout.PREFERRED_SIZE)
										.addPreferredGap(ComponentPlacement.RELATED)
										.addComponent(scrollPane_1, GroupLayout.PREFERRED_SIZE, 464, GroupLayout.PREFERRED_SIZE)
										.addContainerGap())
				);

		JLabel label = new JLabel("variable limit");
		SpinnerModel varSpinModel = new SpinnerNumberModel(1, 1, 4, 1);
		varLimitSpinner = new JSpinner(varSpinModel);
		varLimitSpinner.addChangeListener(new ChangeListener() {
			public void stateChanged(ChangeEvent e) {
				if (input != null){
					input.setVarLimit((int) varLimitSpinner.getValue());
				}
			}
		});
		JLabel label_1 = new JLabel("size limit");
		sizeLimitSpinner = new JSpinner(new SpinnerNumberModel(0, 0, 10, 1));
		sizeLimitSpinner.addChangeListener(new ChangeListener() {
			public void stateChanged(ChangeEvent e) {
				if (input != null){
					input.setSizeLimit((int) sizeLimitSpinner.getValue() ); 
				}
			}
		});
		lblFormulaGeneration = new JLabel("Formula Generation");
		commonAxiomsCheckBox = new JCheckBox("generate common axioms");
		commonAxiomsCheckBox.setSelected(true);
		commonAxiomsCheckBox.addChangeListener(new ChangeListener() {
			public void stateChanged(ChangeEvent e) {
				if (input != null){
					input.setSearchCommonAxioms(commonAxiomsCheckBox.isSelected());
				}
			}
		});
		GroupLayout gl_panel_2 = new GroupLayout(panel_2);
		gl_panel_2.setHorizontalGroup(
				gl_panel_2.createParallelGroup(Alignment.LEADING)
				.addGroup(gl_panel_2.createSequentialGroup()
						.addGroup(gl_panel_2.createParallelGroup(Alignment.LEADING)
								.addGroup(gl_panel_2.createSequentialGroup()
										.addContainerGap()
										.addComponent(lblFormulaGeneration)
										.addPreferredGap(ComponentPlacement.RELATED, 132, Short.MAX_VALUE))
										.addGroup(Alignment.TRAILING, gl_panel_2.createSequentialGroup()
												.addContainerGap()
												.addComponent(commonAxiomsCheckBox)
												.addGap(19)))
												.addGroup(gl_panel_2.createParallelGroup(Alignment.TRAILING)
														.addGroup(gl_panel_2.createSequentialGroup()
																.addComponent(label_1)
																.addPreferredGap(ComponentPlacement.RELATED)
																.addComponent(sizeLimitSpinner, GroupLayout.PREFERRED_SIZE, 47, GroupLayout.PREFERRED_SIZE))
																.addGroup(gl_panel_2.createSequentialGroup()
																		.addComponent(label)
																		.addPreferredGap(ComponentPlacement.RELATED)
																		.addComponent(varLimitSpinner, GroupLayout.PREFERRED_SIZE, GroupLayout.DEFAULT_SIZE, GroupLayout.PREFERRED_SIZE)))
																		.addGap(30))
				);
		gl_panel_2.setVerticalGroup(
				gl_panel_2.createParallelGroup(Alignment.LEADING)
				.addGroup(gl_panel_2.createSequentialGroup()
						.addComponent(lblFormulaGeneration)
						.addContainerGap(59, Short.MAX_VALUE))
						.addGroup(gl_panel_2.createSequentialGroup()
								.addContainerGap(13, Short.MAX_VALUE)
								.addGroup(gl_panel_2.createParallelGroup(Alignment.BASELINE)
										.addComponent(varLimitSpinner, GroupLayout.PREFERRED_SIZE, GroupLayout.DEFAULT_SIZE, GroupLayout.PREFERRED_SIZE)
										.addComponent(label))
										.addPreferredGap(ComponentPlacement.RELATED)
										.addGroup(gl_panel_2.createParallelGroup(Alignment.BASELINE)
												.addComponent(sizeLimitSpinner, GroupLayout.PREFERRED_SIZE, GroupLayout.DEFAULT_SIZE, GroupLayout.PREFERRED_SIZE)
												.addComponent(label_1)
												.addComponent(commonAxiomsCheckBox)))
				);
		panel_2.setLayout(gl_panel_2);

		JLabel lblProverTimeoutIn = new JLabel("prover timeout limit (s)");
		timeoutSpinner = new JSpinner(new SpinnerNumberModel(5, 1, 99, 1));
		timeoutSpinner.addChangeListener(new ChangeListener() {
			public void stateChanged(ChangeEvent e) {
				if (input != null){
					input.setTimeout((int) timeoutSpinner.getValue());
				}
			}
		});

		lblTheoremProverCalls = new JLabel("Redundancy Proof Search");

		JLabel lblMax = new JLabel("max premises per proof");
		GroupLayout gl_panel = new GroupLayout(panel);
		gl_panel.setHorizontalGroup(
				gl_panel.createParallelGroup(Alignment.LEADING)
				.addGroup(gl_panel.createSequentialGroup()
						.addGroup(gl_panel.createParallelGroup(Alignment.LEADING)
								.addGroup(gl_panel.createSequentialGroup()
										.addGap(6)
										.addComponent(lblTheoremProverCalls))
										.addGroup(gl_panel.createSequentialGroup()
												.addContainerGap()
												.addComponent(lblMax, GroupLayout.PREFERRED_SIZE, 161, GroupLayout.PREFERRED_SIZE)
												.addPreferredGap(ComponentPlacement.RELATED)
												.addComponent(spinnerChunkSize, GroupLayout.PREFERRED_SIZE, GroupLayout.DEFAULT_SIZE, GroupLayout.PREFERRED_SIZE)
												.addGap(28)
												.addComponent(lblProverTimeoutIn)
												.addGap(12)
												.addComponent(timeoutSpinner, GroupLayout.PREFERRED_SIZE, GroupLayout.DEFAULT_SIZE, GroupLayout.PREFERRED_SIZE)))
												.addGap(125))
				);
		gl_panel.setVerticalGroup(
				gl_panel.createParallelGroup(Alignment.TRAILING)
				.addGroup(gl_panel.createSequentialGroup()
						.addGap(3)
						.addComponent(lblTheoremProverCalls)
						.addGap(18)
						.addGroup(gl_panel.createParallelGroup(Alignment.BASELINE)
								.addComponent(lblMax, GroupLayout.DEFAULT_SIZE, 32, Short.MAX_VALUE)
								.addComponent(spinnerChunkSize, GroupLayout.PREFERRED_SIZE, GroupLayout.DEFAULT_SIZE, GroupLayout.PREFERRED_SIZE)
								.addComponent(lblProverTimeoutIn)
								.addComponent(timeoutSpinner, GroupLayout.PREFERRED_SIZE, GroupLayout.DEFAULT_SIZE, GroupLayout.PREFERRED_SIZE))
								.addGap(10))
				);
		panel.setLayout(gl_panel);

		contentPane.setLayout(gl_contentPane);

		proverPath = getProverPathFromFile();

		if (proverPath == null){
			//throw error
			appendErrorConsole("\nProver path is null");
		}
	}


	/**
	 * Returns the path to the prover application
	 * if file exists and prover is reachable, top-right button reads "Prover connected" 
	 * in green. Else button reads "Link prover" in red.
	 * @return String for the prover path
	 */
	public String getProverPathFromFile(){

		String path = "";

		File f = new File("proverPath.txt");
		if(f.exists() && !f.isDirectory()) { 

			path = getProverPath();
			proverIsConnected = testProverConnection(path);
			if (proverIsConnected){
				linkProverButton.setText("Prover linked");
				Color darkGreen = new Color(0,50,0);
				linkProverButton.setForeground(darkGreen);
				openFileButton.setEnabled(true);
				linkProverButton.setEnabled(false);

			} else {  //else file exists but not connected
				appendErrorConsole("cannot connect to prover, please click \"Link prover\" to link to the executable for your Prover9 file\n");
				appendErrorConsole("It should be somewhere like \" /Users/Me/Documents/stuff/LADR-2009-11A/bin/prover9 \" \n");
				appendErrorConsole("The file I found has the path " + path + "\n");
				linkProverButton.setForeground(Color.RED);
				openFileButton.setEnabled(false);

			}

		} else { //else no file and no connection
			appendErrorConsole("cannot find file proverPath.txt, please click \"Link prover\" to connect");
			linkProverButton.setForeground(Color.RED);
			openFileButton.setEnabled(false);

		}

		if (!path.isEmpty()){
			return path;
		}
		return null;
	}


	/**
	 * Get prover information from user
	 */
	public void linkProver(){

		String tempFilePath;

		JFileChooser openProverDialog = new JFileChooser();
		int returnVal = openProverDialog.showOpenDialog(textConsoleArea);

		//open file 
		//get path name
		//save into file "proverPath.txt" (overwrite)

		if (returnVal == JFileChooser.APPROVE_OPTION) {
			File proverFile = openProverDialog.getSelectedFile();
			tempFilePath = proverFile.getAbsolutePath();

			//remove app name from path, want path to directory only
			if (tempFilePath.endsWith("prover9")){
				//remove "prover9"
				proverPath = tempFilePath.substring(0, tempFilePath.length() - 7);
			} 

			if (tempFilePath.endsWith("mace4")){
				if (tempFilePath.endsWith("prover9-mace4")){
					//remove "prover9-mace4"
					proverPath = tempFilePath.substring(0, tempFilePath.length() - 13);
				} else {
					//else just remove "mace4"
					proverPath = tempFilePath.substring(0, tempFilePath.length() - 4);
				}
			}

			try{
				//save path to file
				FileWriter f = new FileWriter("proverPath.txt"); 
				f.write(proverPath);
				f.close();

				//test prover connection
				boolean proverConnected = testProverConnection(proverPath);
				if (proverConnected){
					Color darkGreen = new Color(0,50,0);
					linkProverButton.setForeground(darkGreen);
					linkProverButton.setText("Prover linked");
					textConsoleArea.setText("Prover found, ready.");
					openFileButton.setEnabled(true);

				} else {
					textConsoleArea.setText("prover Connection failed");
				}

			} catch (IOException ioe){
				appendErrorConsole("Unexpected I/O Error");
			}
		} else {
			//else user cancelled open file, do nothing for now
		}

	}

	//TODO: test Mace4 connection also
	/**
	 * Opens a connection to prover software, checks for appropriate response
	 * @param path a String representing the path to the prover9/mace4 "bin" folder
	 * @return true if prover is present and responding
	 */
	public boolean testProverConnection(String path){
		boolean isConnected  = false;
		int exitValue;
		Process proverProcess = null;

		Runtime r = Runtime.getRuntime();
		String callString = path + "prover9 -f";
		try{
			proverProcess = r.exec(callString);
		} catch (Exception e){
			appendErrorConsole("Error calling Prover9\n");
			return false;
		}

		BufferedReader in = new BufferedReader(new InputStreamReader(proverProcess.getInputStream()));

		try{
			//gobble stdout to prevent IO blocking
			while ((!Thread.currentThread().isInterrupted() && ((in.readLine()) != null))) {;}
			proverProcess.waitFor();  
		} catch (Exception e){
			appendErrorConsole("Error: " + e.getMessage());

		}

		exitValue  = proverProcess.exitValue();

		//exit values between zero and 102 are prover9 exit values
		if (exitValue <= 102) {isConnected = true;}

		return isConnected;
	}

	
	/**
	 * reads absolute path for prover from file
	 * @return a String representing the path
	 */
	public String getProverPath(){
		BufferedReader buffReader = null;
		String path = "";

		try{

			buffReader = new BufferedReader(new FileReader("proverPath.txt"));
			if ((path = buffReader.readLine()) != null){
				//path is now whatever was on the line
			} else {
				path = "";
			}
			buffReader.close();
		} catch (Exception e){
			appendErrorConsole("Prover path error.\n");
		}
		return path;
	}

	
	/**
	 * Opens an "open file" dialog box and returns a reference to the file chosen
	 * @return a Java File reference for the chosen file
	 */ 
	public File openFile(){
		//open in last directory used, or default directory if none
		JFileChooser chosenFile = new JFileChooser(currentDirectory);

		int returnVal = chosenFile.showOpenDialog(textConsoleArea);

		//if opened a file, return file
		if (returnVal == JFileChooser.APPROVE_OPTION) {
			currentDirectory = chosenFile.getSelectedFile();
			return chosenFile.getSelectedFile();
		} 
		return null;
	}

	
	/**
	 * Summarize contents of input file. Print to top console window. 
	 */
	public void printInputSummary(){
		textConsoleArea.setText("");								
		appendConsole("File "+ input.filename() + "\n");
		appendConsole("found " + input.relations().size());
		appendConsole(input.relations().size() > 1? " relations:" + "\n" : " relation:" + "\n");

		for (Relation r : input.relations()){
			appendConsole(r.name() + " (arity " + r.arity() + ", " + r.numFacts() + " facts)" + "\n");
		}

		appendConsole("\nvarlimit: " + input.varLimit() + ", ");
		appendConsole("sizelimit: " + input.sizeLimit() + "\n");
		appendConsole("Click \"Search\" to begin.\n");
	}


	/**
	 * Print results of search to bottom console window. 				TODO: full results
	 */
	public void writeResultstoGUI(){

		//appendConsole(showControlBooleans());
		//	axiomOutputArea.setText(someString());

		axiomOutputArea.setText("");
		appendAxiomArea(proverStats());
//		printProverStats();


		if (GUIoutputWritten){
			System.err.println("cancelling second write");
			return;
		}
	//	System.out.println("WRITING RESULTS");
		GUIoutputWritten = true;

		if (isRepeatSearch){
			appendAxiomArea("repeated search\n");
		}

		appendAxiomArea("\nResults for file: " + file1.getName() + "\n");
		appendAxiomArea("Generated " + firstMinSet.size() + " true formulas\n");

		//axiomOutputArea.append("See file " + input.generateOutputName() + " for full results\n");
		appendAxiomArea("Found minimal set of " + minSetFromProver.size() + " formulas\n");

		appendAxiomArea("Interesting formulas\n");
		appendAxiomArea(Interesting());

		appendAxiomArea("\nOther formulas\n");
		appendAxiomArea(Uninteresting());
	}


	/**
	 * make the String output of search results
	 * @return the String
	 */
	public String results(){
		StringBuilder s = new StringBuilder();

		if (GUIoutputWritten){
			return "";
		}

	//	System.out.println("WRITING RESULTS");
		GUIoutputWritten = true;

		if (isRepeatSearch){
			s.append("repeated search for file "+ file1.getName() + ":\n");
		} else {
			s.append("\nResults for file: " + file1.getName() + "\n");
			s.append("Generated " + firstMinSet.size() + " true formulas\n");
		}

		//axiomOutputArea.append("See file " + input.generateOutputName() + " for full results\n");
		s.append("Found minimal set of " + minSetFromProver.size() + " formulas\n");

		s.append("Common axioms / interesting formulas\n");

		s.append(Interesting());

		s.append("\nOther formulas\n");

		s.append(Uninteresting());

		return s.toString();
	}







	/**
	 * output any "interesting" formulas
	 */
	public String Interesting(){
		StringBuilder s = new StringBuilder();

		int count = 0;
		for (Map.Entry<String, FormulaTree> f : minSetFromProver.entrySet()){
			if (f.getValue().isInteresting() || f.getValue() instanceof CommonAxiom){
				s.append(f.getKey());
				if (f.getValue() instanceof CommonAxiom){
					s.append("  (" + ((CommonAxiom) f.getValue()).label() + ")");
				}			
				s.append("\n");

				count++;
			}			
		}		
		if (count==0){
			s.append("None\n");
		}
		return s.toString();
	}

	/**
	 * output any "uninteresting" formulas
	 */
	public String Uninteresting(){
		StringBuilder s = new StringBuilder();

		int count=0;
		for (Map.Entry<String, FormulaTree> f : minSetFromProver.entrySet()){
			if (!f.getValue().isInteresting() && !(f.getValue() instanceof CommonAxiom)){
				s.append(f.getKey());
				if (f.getValue() instanceof CommonAxiom){
					s.append("  (" + ((CommonAxiom) f.getValue()).label() + ")");
				}			
				s.append("\n");
				count++;
			}			
		}		
		if (count==0){
			s.append("None\n");
		}
		return s.toString();
	}



	/**
	 * launch the prover
	 */
	public void launchProver(){

		numProverCalls = firstMinSet.size();
		proverCalls = new ParallelProver(input, firstMinSet, proverPath);				
		proverCalls.addPropertyChangeListener(propertyChangeListener);

		//launch prover calls in background										//PROVER CALLED HERE
		proverCalls.execute();					
	}


	/**
	 * Reset control flow and other values for a repeat search through the axiom set.
	 * In particular it takes the output axiom set from the first round and makes
	 * it the input set for the next round. 
	 */
	public void resetForRepeatSearch(){
		isRepeatSearch = true;
		//doneProverCalls = false;
		GUIoutputWritten = false;

		//reset input set
		firstMinSet = minSetFromProver;
		numProverCalls = firstMinSet.size();

		//grey out search options
		varLimitSpinner.setEnabled(false);
		sizeLimitSpinner.setEnabled(false);

		//change search button to read "search again"
		startSearchButton.setText("Search again");
		startSearchButton.setEnabled(true);
	}


	/**
	 * Set search controls on the GUI to match the input file. 
	 */
	public void setSearchControls(){

		//appendConsole("CHUNK SIZE IS " + input.chunkSize());

		varLimitSpinner.setValue(input.varLimit());
		sizeLimitSpinner.setValue(input.sizeLimit());
		timeoutSpinner.setValue(input.timeout());

		if (input.useChunking()){
			spinnerChunkSize.setValue(input.chunkSize());	
			spinnerChunkSize.setEnabled(true);
		}		
		//set input to agree with current state of "common axioms" checkbox
		input.setSearchCommonAxioms(commonAxiomsCheckBox.isSelected());
	}

	/**
	 * Reset control flow for a new search with a new input file
	 */
	public void resetForNewSearch(){
		varLimitSpinner.setEnabled(true);
		sizeLimitSpinner.setEnabled(true);
		timeoutSpinner.setEnabled(true);
		startSearchButton.setText("Search");
		//doneProverCalls = false;
		isRepeatSearch = false;
		doneGeneration = false;
		doneTypedGeneration = false;
		GUIoutputWritten = true;
		outputFileName = null;
		
		proverCalls = null;
		formGen = null;
	}


	/**
	 * Debug method
	 */
	public String showControlBooleans(){
		StringBuilder s = new StringBuilder();
		s.append("\n   CONTROL BOOLEANS\n");
		s.append("   doneGeneration: "+ doneGeneration + "\n");
		s.append("   doneProverCalls: "+ doneProverCalls + "\n");
		s.append("   isRepeatSearch: "+ isRepeatSearch + "\n");
		s.append("   GUIoutputWritten: "+ GUIoutputWritten + "\n");
		s.append("   is EDT: " + SwingUtilities.isEventDispatchThread() + "\n\n");
		return s.toString();
	}





	/**
	 * Initialize background document for axiom output area
	 */
	public void initAxiomOutputDocument(){
		axiomDoc = axiomOutputArea.getStyledDocument();
		axiomText = axiomOutputArea.addStyle("Axiom text", null);
		StyleConstants.setForeground(axiomText, Color.BLACK);
		int w = axiomOutputArea.getFontMetrics(axiomOutputArea.getFont()).charWidth(' ');
		TabStop[] stops={new TabStop(w*15), new TabStop(w*38), 
				new TabStop(w*57), new TabStop(w*73)};

		MutableAttributeSet attrs = new SimpleAttributeSet();
		StyleConstants.setTabSet(attrs, new TabSet(stops) );
		axiomOutputArea.setParagraphAttributes(attrs, false);
	}

	/**
	 * Initialize background document for upper console area
	 */
	public void initTextConsoleDocument(){
		consoleDoc = textConsoleArea.getStyledDocument();
		redText = textConsoleArea.addStyle("Red text", null); 
		StyleConstants.setForeground(redText, Color.RED);
		blackText = textConsoleArea.addStyle("Black text", null); 
		StyleConstants.setForeground(blackText, Color.BLACK);
	}



	/**
	 * Print black text to the upper text pane
	 * @param text the text to print
	 */
	public void appendConsole(String text){
		textOutput(text, blackText, consoleDoc);
	}

	/**
	 * Print red text to the upper text pane.
	 * Used for error messages or other warnings. 
	 * @param text the text to print
	 */
	public void appendErrorConsole(String text){
		textOutput(text, redText, consoleDoc);
	}	

	/**
	 * Print black text to lower text pane.
	 * @param text the text to print
	 */
	public void appendAxiomArea(String text){
		textOutput(text, axiomText, axiomDoc);
	}


	/**
	 * General printing method to print to either text area in a given text style.
	 * @param text the text to print
	 * @param style a text style (red or black text)
	 * @param doc the background document for a text pane
	 */
	public void textOutput(String text, Style style, StyledDocument doc){
		try {
			doc.insertString(doc.getLength(), text, style);
		} catch (BadLocationException badloc) {
			appendErrorConsole("Error: " + badloc.getMessage());
		}
	}




	/**
	 * Print prover call statistics to lower output pane
	 */
	public void printProverStats(){
		axiomOutputArea.setText("");
		//textConsoleArea.setText("");


		appendAxiomArea("\nProver Calls\n----------\n");
		appendAxiomArea("Prover9:\tproof found\tno proof\ttimeout\tother\n");
		appendAxiomArea("\t" + proverCalls.numProofsFound());
		appendAxiomArea("\t" + proverCalls.numNoProofsFound());
		appendAxiomArea("\t" + proverCalls.numProver9Timeouts());	
		appendAxiomArea("\t" + proverCalls.numProver9OtherResult() + "\n\n");

		appendAxiomArea("Mace4:\tmodel found\tno model\ttimeout\tother\n");
		appendAxiomArea("\t" + proverCalls.numCounterexamplesFound());
		appendAxiomArea("\t" + proverCalls.numMace4NoModelsFound());
		appendAxiomArea("\t" + proverCalls.numMace4Timeouts());				
		appendAxiomArea("\t" + proverCalls.numMace4OtherResult() + "\n\n");

		appendAxiomArea("Minimal set size: "+ proverCalls.minSetSize());
		int numDiscarded = proverCalls.numProofsFound() + proverCalls.numMace4NoModelsFound();
		appendAxiomArea("    Discarded: "+ numDiscarded + "\n");
	}


	/**
	 * String output of prover call statistics.
	 * Used for file output.
	 * @return the String
	 */
	public String proverStats(){
		if (proverCalls.isCancelled()){return "";}
		
		StringBuilder s = new StringBuilder();
		s.append("\nProver Calls\n----------\n");
		s.append("Prover9:\tproof found\tno proof\ttimeout\tother\n");
		s.append("\t" + proverCalls.numProofsFound());
		s.append("\t" + proverCalls.numNoProofsFound());
		s.append("\t" + proverCalls.numProver9Timeouts());	
		s.append("\t" + proverCalls.numProver9OtherResult() + "\n\n");

		s.append("Mace4:\tmodel found\tno model\ttimeout\tother\n");
		s.append("\t" + proverCalls.numCounterexamplesFound());
		s.append("\t" + proverCalls.numMace4NoModelsFound());
		s.append("\t" + proverCalls.numMace4Timeouts());				
		s.append("\t" + proverCalls.numMace4OtherResult() + "\n\n");

		s.append("Minimal set size: "+ proverCalls.minSetSize());
		int numDiscarded = proverCalls.numProofsFound() + proverCalls.numMace4NoModelsFound();
		s.append("    Discarded: "+ numDiscarded + "\n");

		return s.toString();
	}


	
	public String fileProverStats(){
		StringBuilder s = new StringBuilder();
		s.append("\nProver Calls\n----------\n");
		s.append("Prover9:\tproof found\tno proof\ttimeout\tother\n");
		s.append("\t\t" + proverCalls.numProofsFound());
		s.append("\t\t" + proverCalls.numNoProofsFound());
		s.append("\t\t" + proverCalls.numProver9Timeouts());	
		s.append("\t" + proverCalls.numProver9OtherResult() + "\n\n");

		s.append("Mace4:\t\tmodel found\tno model\ttimeout\tother\n");
		s.append("\t\t" + proverCalls.numCounterexamplesFound());
		s.append("\t\t" + proverCalls.numMace4NoModelsFound());
		s.append("\t\t" + proverCalls.numMace4Timeouts());				
		s.append("\t" + proverCalls.numMace4OtherResult() + "\n\n");

		s.append("Minimal set size: "+ proverCalls.minSetSize());
		int numDiscarded = proverCalls.numProofsFound() + proverCalls.numMace4NoModelsFound();
		s.append("    Discarded: "+ numDiscarded + "\n");

		return s.toString();
	}
	
	
	
	
	
	
	
	
	//TODO: running results to file
	//if repeat search, just append to end
	/**
	 * Write to file
	 */
	public void writeResultsToFile() {
		outputFileName = input.generateOutputName();
		File outfile = new File(outputFileName);
		PrintWriter fileOutput = null;
		try {
			outfile.createNewFile();
			fileOutput = new PrintWriter(outfile);
		} catch (IOException e) {
			appendErrorConsole("I/O Error: " + e.getMessage());
		}
		
		//search complete, write report to file
		fileOutput.println("Results for filename " + input.filename());

		fileOutput.println("Found minimal set of " +  minSetFromProver.size() +" in " + runTime/1000.0 + " seconds" );
		fileOutput.println(firstMinSet.size() + " true formulas generated\n");
		
		fileOutput.println("Input");
		fileOutput.println("¯¯¯¯¯");
		fileOutput.print(input.relations().size() > 1 ? "Relations: " : "Relation: ");
		int commasToPrint = input.relations().size() -1;
		for (int index = 0; index < input.relations().size(); index++){
			fileOutput.print(input.relations().get(index).name());
			if (commasToPrint > 0){
				fileOutput.print(", ");
				commasToPrint --;
			}
		}
		fileOutput.print("\n");

		if (input.hasTypes()){
			fileOutput.print(input.types().size() > 1 ? "Types: " : "Type: ");
			commasToPrint = input.types().size() -1;
			for (int index = 0; index < input.types().size(); index++){
				fileOutput.print(input.types().get(index).name());
				if (commasToPrint > 0){
					fileOutput.print(", ");
					commasToPrint --;
				}
			}
		} else {
			fileOutput.println("Untyped input");
		}
		
		fileOutput.println("\nGenerated " + firstMinSet.size() + " formulas in " + (formGenEndTime - startTime)/1000.0 + " seconds");
		fileOutput.println("max premises per proof: " + input.chunkSize() + ", timeout: " + input.timeout());
		fileOutput.println("Prover & model checker calls: " + proverTime/1000.0 + " seconds");
		fileOutput.println("Total runtime: " + runTime/1000 + " seconds");
		
	
		fileOutput.println();
		fileOutput.println(fileProverStats()+ "\n\n");

		fileOutput.println("Minimal set");
		fileOutput.println("-----------");
		fileOutput.println(minSet());
		
		
		fileOutput.println("\n\nAll true formulas generated");
		fileOutput.println("---------------------------");
		fileOutput.println(allGeneratedFormulas());

		fileOutput.close();		
	}




	public void writeRepeatResultsToFile(){
		PrintWriter pw = null;
		try {
			pw = new PrintWriter(new FileWriter(outputFileName, true));
		} catch (IOException e) {
			appendErrorConsole("Error writing output file: " + e.getMessage());
		}
		pw.print(repeatSearchResults());
		pw.close();
	}


	
	
	
	public String repeatSearchResults(){
		StringBuilder s = new StringBuilder();
		s.append("\n\nResults for repeat search\n");
		s.append("-------------------------\n");
		s.append("Performed " + firstMinSet.size() + " prover calls in " 
				+ decimal.format(proverTime/1000.0) + " seconds\n");
		s.append("max premises: " + input.chunkSize() + ", timeout: " + input.timeout() + "\n");
		s.append(fileProverStats() + "\n");
		s.append("Minimum set\n");
		s.append("-----------\n");
		s.append(minSet());
		s.append("\n");
		return s.toString();
	}
	
	
	
	
	
	
	/**
	 * String output of all formulas generated
	 * @return  the String
	 */
	public String allGeneratedFormulas(){
		StringBuilder s = new StringBuilder();
		for (FormulaTree f : firstMinSet.values()){

			//revert
			s.append(f.outputTextFormula() + "\n");	
			if (f instanceof CommonAxiom){
				s.append("(" + ((CommonAxiom) f).label() + ")\n\n");
			}
		}
		return s.toString();
	}
	
	/**
	 * String output of minSet for user
	 * @return the String
	 */
	public String minSet(){
		StringBuilder s = new StringBuilder();		
		for (FormulaTree f : minSetFromProver.values()){
			s.append(f.outputTextFormula() + "\n");	
			if (f instanceof CommonAxiom){
				s.append("(" + ((CommonAxiom) f).label() + ")\n\n");
			}
			
		}
		return s.toString();
	}

	
	


}





/*control flow:

	open file/change settings -> new search -> repeat search 
					|   ^						  |  ^
					v   |						  v  | 	
			   cancel/alter settings			  -->|


 * 
 */


