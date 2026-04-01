package aprove.verification.oldframework.PropositionalLogic.SATCheckers;

import java.io.*;
import java.util.*;
import java.util.logging.*;

import aprove.solver.*;
import aprove.strategies.Abortions.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.TheoryPropositions.*;

public class SATDumper implements SATChecker {


    SATChecker engine;
    String outputDir;

    public static Logger log = java.util.logging.Logger.getLogger("SATDumper");

    public SATDumper(SatEngine engine, String outputDir) {
        this.engine = engine.getSATChecker();
        this.outputDir = outputDir;
    }


    @Override
    public void setAssumps(Set<Formula<None>> assumps) {
        // TODO SATView does not currently support assumptions.
        this.engine.setAssumps(assumps);
    }

    @Override
    public int[] solve(Formula<None> formula, Abortion aborter)
            throws AbortionException, SolverException {

        this.serialize(formula);

        return this.engine.solve(formula, aborter);
    }

    @Override
    public int[] solve(String dimacs, Abortion aborter)
            throws AbortionException, SolverException {
        // Well this is a bit late to dump...
        SATDumper.log.log(Level.WARNING, "Could not dump propositional formula: Formula has been provided as dimacs or iscas");
        return this.engine.solve(dimacs, aborter);

    }

    @Override
    public int[] solveCNF(Formula<None> formula, Abortion aborter) {

        this.serialize(formula);

        return this.engine.solveCNF(formula, aborter);
    }



    private void serialize(Formula<None> formula) {
        File file;
        File dir;
        OutputStream out;
        ObjectOutputStream stream;
        try {
            dir = new File(this.outputDir);
            file = File.createTempFile("satdump", ".satview", dir);
            out = new FileOutputStream(file);
            stream = new ObjectOutputStream(out);
            stream.writeObject(formula);
            stream.close();
        } catch (IOException ex) { // F.i. if the marker interface SATViewSerialize is not activated
            SATDumper.log.log(Level.WARNING, ex.toString());
        }
    }

}
