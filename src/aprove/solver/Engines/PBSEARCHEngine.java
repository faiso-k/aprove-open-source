package aprove.solver.Engines;

import java.math.*;

import aprove.solver.*;
import aprove.verification.oldframework.Algebra.Orders.Utility.POLO.*;
import aprove.verification.oldframework.Algebra.Polynomials.PBSearch.*;
import aprove.verification.oldframework.Algebra.Polynomials.PBSearch.PBCheckers.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

public class PBSEARCHEngine extends Engine {

    public enum PBSolver {
        // TODO SAT4J
        PUEBLO,
        MINISATPLUS,
        EXTERNAL; // use command supplied by user
    }

    // PB07 style: No * between weight and PB variable
    // PB05 style:  A * between weight and PB variable
    private boolean asterisk = false;

    private String command = "true"; // does nothing much
    private PBSolver solver = PBSolver.PUEBLO; // resonably good default

    // true:  use Fortet's linearization
    // false: use Glover's linearization
    private boolean fortet = true;

    // use Pseudo Boolean optimization for autostrict?
    private boolean optimize = false;

    public PBChecker getPBChecker() {
        switch (this.solver) {
        case PUEBLO:
            return new PBFileChecker("Pueblo", false);
        case MINISATPLUS:
            return new PBFileChecker("minisat+", true);
        case EXTERNAL:
            return new PBFileChecker(this.command, this.asterisk);
        default:
            throw new RuntimeException("Unknown type " + this.solver + "!");
        }
    }

    @Override
    public SearchAlgorithm getSearchAlgorithm(DefaultValueMap<String, BigInteger> ranges) {
        PBChecker checker = this.getPBChecker();
        boolean fortet = this.getFortet();
        return PBSearch.create(ranges, checker, fortet, this.optimize);
    }

    /**
     * @param asterisk the asterisk to set
     */
    public void setAsterisk(boolean asterisk) {
        this.asterisk = asterisk;
    }


    /**
     * @param command the command to set
     */
    public void setCommand(String command) {
        this.command = command;
    }


    /**
     * @param solver the solver to set
     */
    public void setSolver(PBSolver solver) {
        this.solver = solver;
    }


    /**
     * @param fortet the fortet to set
     */
    public void setFortet(boolean fortet) {
        this.fortet = fortet;
    }

    /**
     * @param optimize the optimize to set
     */
    public void setOptimize(boolean optimize) {
        this.optimize = optimize;
    }

    /**
     * @return the fortet
     */
    public boolean getFortet() {
        return this.fortet;
    }

}
