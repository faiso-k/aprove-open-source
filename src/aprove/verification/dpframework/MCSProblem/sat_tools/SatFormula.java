package aprove.verification.dpframework.MCSProblem.sat_tools;

import java.io.*;
import java.util.*;

/*
 * This class represents CNF formula
 * Each variable has two forms: 1) variable name as string wikth meaning 2) dimax as Integer
 */
public class SatFormula {

    // mutual mapping between two v aiable representations
    private Hashtable<String, Integer> varsToDimacsVarsHT = new Hashtable<String, Integer>();
    private Hashtable<Integer, String> dimacsVarsToVarsHT = new Hashtable<Integer, String>();
    // The formula saved in memory (not used if Config.USE_CNF_FILE=true)
    private List<List<String>> _cnfFormula;
    private List<List<Integer>> _dimacsCnfFormula;

    // file containing dimacs formula (used if Config.USE_CNF_FILE=true)
    private String _dimacsFormulaFile = null;
    private FileWriter _dimacsFileFileWriter;
    private BufferedWriter _dimacsFileOutput;

    private int _numOfClauses = 0;

    //formula solutions in dymacs format and string format (as variable names)
    private int[] _dimacsSolution = null;
    private String[] _solution = null;
    private Hashtable<Integer, Boolean> _dimacsVarsValuesHT;

    // The input is CNF formuyla of the form like: {{x,-y},{z,t}}
    public SatFormula(final List<List<String>> cnfFormula) {
        this._cnfFormula = cnfFormula;
        this._dimacsCnfFormula = new ArrayList<List<Integer>>();

        Integer nextVarNumber = 1;
        List<Integer> dimacsClosure = null;
        List<String> closure = null;
        String literal = null;
        String var = null;
        boolean isNegative = false;
        Integer dimacsVar = null;

        for (final Iterator<List<String>> formulaIt = this._cnfFormula.iterator(); formulaIt.hasNext();) {
            dimacsClosure = new ArrayList<Integer>();
            this._dimacsCnfFormula.add(dimacsClosure);
            closure = formulaIt.next();
            for (final Iterator<String> closureIt = closure.iterator(); closureIt.hasNext();) {
                literal = closureIt.next();
                var = CommonOperations.literalToVar(literal);
                isNegative = CommonOperations.isLiteralNegative(literal);
                if (!this.varsToDimacsVarsHT.containsKey(var)) { //create new dimacs var
                    this.varsToDimacsVarsHT.put(var, nextVarNumber);
                    this.dimacsVarsToVarsHT.put(nextVarNumber, var);
                    nextVarNumber++;
                }
                dimacsVar = this.varsToDimacsVarsHT.get(var);
                if (isNegative) {
                    dimacsClosure.add(-dimacsVar);
                } else {
                    dimacsClosure.add(dimacsVar);
                }
            }
        }
    }

    public SatFormula(final List<List<Integer>> dimacsCnfFormula, final Hashtable<Integer, String> dimacsVarsToVarsHT,
            final Hashtable<String, Integer> varsToDimacsVarsHT) {
        this._dimacsCnfFormula = dimacsCnfFormula;
        this.dimacsVarsToVarsHT = dimacsVarsToVarsHT;
        this.varsToDimacsVarsHT = varsToDimacsVarsHT;
    }

    public SatFormula(final Hashtable<Integer, String> dimacsVarsToVarsHT,
            final Hashtable<String, Integer> varsToDimacsVarsHT) {

        this.dimacsVarsToVarsHT = dimacsVarsToVarsHT;
        this.varsToDimacsVarsHT = varsToDimacsVarsHT;

        /*
                File dir=new File("TMP");
                    if (!dir.exists())
                        dir.mkdir();
                    _dimacsFormulaFile = "TMP\\mcnp_dimacs_"+Math.random()*1000000;
                    */

        try {
            final File tempfile = File.createTempFile("mcnp_dimacs", "dimacs");
            tempfile.deleteOnExit();
            this._dimacsFormulaFile = tempfile.getCanonicalPath();
            this._dimacsFileFileWriter = new FileWriter(tempfile);
        } catch (final IOException e) {
            e.printStackTrace();
        }
        this._dimacsFileOutput = new BufferedWriter(this._dimacsFileFileWriter);
    }

    //
    public void addClause(final List<Integer> closure) {
        if (closure.isEmpty()) {
            closure.add(1);
            closure.add(-1);
        }
        this._numOfClauses++;
        if (this._dimacsFormulaFile == null) {
            throw new RuntimeException("The method works only if when dimacs formula is ran using file. ");
        }

        String closureString = "";
        for (final Integer integer : closure) {
            closureString = closureString + integer + " ";
        }
        closureString = closureString + "0";

        try {
            this._dimacsFileFileWriter.write(closureString + "\n");
            this._dimacsFileFileWriter.flush();
        } catch (final IOException e) {
            e.printStackTrace();
        }
    }

    // return the variable according to dimacs variable var. If no such - return null.
    public String dimacsVarToVar(final int var) {
        if (this.dimacsVarsToVarsHT.containsKey(var)) {
            return this.dimacsVarsToVarsHT.get(var);
        } else {
            return null;
        }

    }

    // Returns if the formula is satisfiable.
    // Also gets the solution.
    public boolean isSolvable() {
        if (this._dimacsSolution == null) {
            try {
                this.getDimacsSolution();
            } catch (final Exception e) {
                // e.printStackTrace(); //D
                return false;
            }
        }
        return true;
    }

    private void deleteFile(final String file) {
        final File f = new File(file);
        final boolean b = f.delete();
        if (f.exists()) {
            try {
                Thread.sleep(3000);
            } catch (final InterruptedException e) {
                // TODO Auto-generated catch block
                e.printStackTrace();
            }
            f.delete();
            if (f.exists()) {
                System.err.println("CNF formula file '" + f.getAbsolutePath() + "' was not deleted.");
            }
        }
    }

    // add number of closures and variables in the first lines
    // it is done by rewriting the existrsin file contents
    private void adjustDimacsFile() {
        final String tmpFile = this._dimacsFormulaFile + "_tmp";
        try {
            final FileWriter writer = new FileWriter(tmpFile);
            final BufferedWriter out = new BufferedWriter(writer);
            out.write("p cnf " + this.varsToDimacsVarsHT.size() + " " + this._numOfClauses + "\n");
            final FileInputStream fis = new FileInputStream(this._dimacsFormulaFile);
            final InputStreamReader isr = new InputStreamReader(fis);
            final BufferedReader reader = new BufferedReader(isr);
            String line = null;
            while ((line = reader.readLine()) != null) {
                out.write(line + "\n");
            }

            reader.close();
            isr.close();
            fis.close();
            out.close();
            writer.close();

        } catch (final IOException e) {
            e.printStackTrace();
        }
        this.deleteFile(this._dimacsFormulaFile);
        final File newFile = new File(tmpFile);
        newFile.renameTo(new File(this._dimacsFormulaFile));
    }

    // Get dimacs format solution. Solve first if not solved yet.
    public int[] getDimacsSolution() {
        if (this._dimacsSolution == null) {
            final Solver s = new Solver();
            if (this._dimacsFormulaFile == null) {
                this._dimacsSolution = s.solve(this._dimacsCnfFormula);
            } else {
                try {
                    this._dimacsFileFileWriter.close();
                    this._dimacsFileOutput.close();
                    this.adjustDimacsFile();
                    this._dimacsSolution = s.solve(this._dimacsFormulaFile);
                } catch (final IOException e) {
                    e.printStackTrace();
                }
                this.deleteFile(this._dimacsFormulaFile);
            }
            // save results to table
            this._dimacsVarsValuesHT = new Hashtable<Integer, Boolean>();
            for (final int element : this._dimacsSolution) {
                if (element > 0) {
                    this._dimacsVarsValuesHT.put(element, true);
                } else {
                    this._dimacsVarsValuesHT.put((-1) * element, false);
                }
            }

        }
        return this._dimacsSolution;
    }

    // Transform dimacs solution to understandable with variaable names.
    // Solve first if not solved yet.
    public String[] getSolution() {
        if (this._solution == null) {
            final int[] dimacsSolution = this.getDimacsSolution();
            this._solution = new String[dimacsSolution.length];
            for (int i = 0; i < dimacsSolution.length; i++) {
                final int dimacsVar = Math.abs(dimacsSolution[i]);
                final String var = this.dimacsVarsToVarsHT.get(dimacsVar);
                if (dimacsSolution[i] > 0) {
                    this._solution[i] = var;
                } else {
                    this._solution[i] = CommonOperations.negateLiteral(var);
                }
            }

        }
        return this._solution;
    }

    // Return positive variables
    public String[] getPositiveSolution() {
        if (this._solution == null) {
            this._solution = this.getSolution();
        }
        int numOfPositives = 0;
        for (int i = 0; i < this._solution.length; i++) {
            if (!CommonOperations.isLiteralNegative(this._solution[i])) {
                numOfPositives++;
            }
        }

        final String[] res = new String[numOfPositives];
        int j = 0;
        for (int i = 0; i < this._solution.length; i++) {
            if (!CommonOperations.isLiteralNegative(this._solution[i])) {
                res[j] = this._solution[i];
                j++;
            }
        }

        return res;
    }

    public int getVarValue(final String var) {
        if (!this.varsToDimacsVarsHT.containsKey(var)) {
            throw new RuntimeException("Varibale " + var + " does not exist.");
        }
        final int dimacsVar = this.varsToDimacsVarsHT.get(var);
        if (!this._dimacsVarsValuesHT.containsKey(dimacsVar)) {
            throw new RuntimeException("Varibale " + var + " does not exist. Dimax var: " + dimacsVar + ".");
        }
        final Boolean varValue = this._dimacsVarsValuesHT.get(dimacsVar);
        if (varValue.booleanValue()) {
            return 1;
        } else {
            return 0;
        }
    }

    // Write to dimacs format file
    public void toDimacsFile(final String file) {
        try {
            // Create file
            final FileWriter fstream = new FileWriter(file);
            final BufferedWriter out = new BufferedWriter(fstream);
            out.write("p cnf " + this.varsToDimacsVarsHT.size() + " " + this._cnfFormula.size() + "\n");

            String closureString = "";
            //Close the output stream

            for (final List<Integer> closure : this._dimacsCnfFormula) {
                closureString = "";
                for (final Integer integer : closure) {
                    closureString = closureString + integer + " ";
                }
                closureString = closureString + "0";
                out.write(closureString + "\n");
            }

            out.close();
        } catch (final Exception e) {
            e.printStackTrace();
        }

    }

    @Override
    public String toString() {
        String closures = "";
        String dimacs = "";
        for (final List<String> closure : this._cnfFormula) {
            for (final String string : closure) {
                closures = closures + string + " ";
            }
            closures = closures + "\n";
        }

        for (final List<Integer> closure : this._dimacsCnfFormula) {
            for (final Integer integer : closure) {
                dimacs = dimacs + integer + " ";
            }
            dimacs = dimacs + "0 ";
        }
        return closures + "\n" + dimacs;
    }
}
