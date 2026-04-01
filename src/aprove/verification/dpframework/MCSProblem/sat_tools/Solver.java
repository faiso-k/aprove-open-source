package aprove.verification.dpframework.MCSProblem.sat_tools;
import java.util.*;

import org.sat4j.core.*;
import org.sat4j.minisat.*;
import org.sat4j.reader.*;
import org.sat4j.specs.*;

import aprove.verification.dpframework.MCSProblem.satsolver.*;

/*
 * The class runs the corresponding sat solver to solve CNF formula represented by SatFormula object
 * The sat solver iks choosen in Config file
 */

public class Solver {
    private IProblem _problem = null;
    private Boolean _isSatisfiable = null;

    // initializes the formula and init IProblem interface variable _problem
    private void solveHelper(List<List<Integer>> cnf)
    {
        ISolver solver = SolverFactory.newDefault();
        //     prepare the solver to accept MAXVAR variables. MANDATORY
        solver.newVar(1000000);
        //     not mandatory for SAT solving. MANDATORY for MAXSAT solving
        ////////solver.setExpectedNumberOfClauses(1000000);
        for (Iterator<List<Integer>> it=cnf.iterator(); it.hasNext(); ) {
            Object[] clauseObj = it.next().toArray();
            int [] clause = new int[clauseObj.length]; // get the clause from somewhere
            for (int i=0; i<clauseObj.length; i++) {
                clause[i]=((Integer)clauseObj[i]).intValue();
            }
            try {
                solver.addClause(new VecInt(clause));
            } catch (ContradictionException e) {
                // If entered empty clause - set solver to dummy false CNF
                // e.printStackTrace();
                try {
                    solver = SolverFactory.newDefault();
                    int[] falseClause1={1,2};
                    int[] falseClause2={-1,-2};
                    int[] falseClause3={1,-2};
                    int[] falseClause4={-1,2};
                    solver.addClause(new VecInt(falseClause1));
                    solver.addClause(new VecInt(falseClause2));
                    solver.addClause(new VecInt(falseClause3));
                    solver.addClause(new VecInt(falseClause4));
                    return;
                } catch (ContradictionException e1) {
                    e1.printStackTrace();
                }
                return;
            }
        }

        // Working now on the IProblem interface
        this._problem = solver;
    }

    public boolean isSatisfiable(List<List<Integer>> cnf)
    {
        if (this._isSatisfiable!=null) {
            return this._isSatisfiable;
        }

        this.solveHelper(cnf);
        try {
            this._isSatisfiable = this._problem.isSatisfiable();
            return this._isSatisfiable;
        } catch (TimeoutException e) {
            throw new RuntimeException("Timeout accured.",e);
        }
    }

    public int[] solve(List<List<Integer>> cnf)
    {
        boolean satisfiable = this.isSatisfiable(cnf);
        if (satisfiable) {
            return this._problem.model();
        } else {
            throw new RuntimeException("The formula is unsatisfiable.");
        }
    }

    public int[] solve(String file) {
        if (Config.SAT_SOLVER==Config.SAT4J) {
            ISolver solver = SolverFactory.newDefault();
            solver.setTimeout(3600); // 1 hour timeout
            org.sat4j.reader.Reader reader = new DimacsReader(solver);
            try {
                IProblem problem = reader.parseInstance(file);
                if (problem.isSatisfiable()) {
                    return problem.model();
                } else {
                    return null;
                }
            } catch (ContradictionException e) {
                //e.printStackTrace();  //empty clause or contradiction [[-1 1]], [1,2],[-1,-2]]
            } catch (TimeoutException e) {
                e.printStackTrace();
            } catch (Exception e) {
                e.printStackTrace();
            }
            return null;
        } else if (Config.SAT_SOLVER==Config.CryptoMiniSATSolver) {
            SATSolver satSolver = new SATRaceSolver(Config.CryptoMiniSATSolverExecutable);
            try {
                int[] solution = satSolver.solveFile(file);
                return solution;
            } catch (SATSolverException e) {
                e.printStackTrace();
            }
            return null;
        } else if (Config.SAT_SOLVER==Config.MiniSATSolver) {
            SATSolver satSolver = new MiniSATFileOutputSolver(Config.MiniSATSolverExecutable);
            try {
                int[] solution = satSolver.solveFile(file);
                return solution;
            } catch (SATSolverException e) {
                e.printStackTrace();
            }
            return null;
        }
        return null;
    }

}
