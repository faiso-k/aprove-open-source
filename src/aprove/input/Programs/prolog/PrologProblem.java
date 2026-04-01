package aprove.input.Programs.prolog;

import java.util.*;

import aprove.*;
import aprove.input.Programs.prolog.processors.*;
import aprove.input.Programs.prolog.structure.*;
import aprove.prooftree.Export.ProofPurposeDescriptors.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.IntegerReasoning.smt.*;
import aprove.verification.oldframework.SMT.*;
import aprove.verification.oldframework.SMT.Solver.*;
import aprove.verification.oldframework.SMT.Solver.Factories.*;

/**
 * A PrologProblem contains a PrologProgram and can create an AFS for
 * this program out of meta information in the program's layout text.
 * <br><br>
 *
 * Created: Jul 27, 2006<br>
 * Last modified: Oct 7, 2006
 *
 * @author cryingshadow
 * @version $Id$
 */
public class PrologProblem extends DefaultBasicObligation {

    /**
     * The default SMT solver factory.
     */
    public static final SMTSolverFactory DEFAULT_SMT_FACTORY = new Z3ExtSolverFactory();

    /**
     * The default SMT logic.
     */
    public static final SMTLIBLogic DEFAULT_SMT_LOGIC = SMTLIBLogic.QF_NIA;

    /**
     * The PrologProgram containing all information for this PrologProblem.
     */
    private final PrologProgram program;

    /**
     * The query.
     */
    private final PrologQuery query;

    /**
     * The factory to build SMT solvers.
     */
    private final SMTSolverFactory smtFactory;

    /**
     * The logic for SMT solvers.
     */
    private final SMTLIBLogic smtLogic;

    /**
     * Constructs a new PrologProblem with the specified PrologProgram and query.
     * @param p The program.
     * @param q The query.
     * @param factory The factory to build SMT solvers.
     * @param logic The logic for SMT solvers.
     */
    public PrologProblem(PrologProgram p, PrologQuery q, SMTSolverFactory factory, SMTLIBLogic logic) {
        super("Prolog", "Prolog " + q.getPurpose().toString() + " Problem");
        if (Globals.useAssertions) {
            assert (p != null) : "Program is null!";
        }
        this.program = p;
        this.query = q;
        this.smtFactory = factory;
        this.smtLogic = logic;
    }

    /**
     * Creates an Afs out of the query and the directives in the program.
     * @return The program's Afs.
     */
    public List<Afs> createListOfAfs() {
        return this.createListOfAfs(PrologFNG.IN);
    }

    /**
     * Creates a list of Afss from the queries and directives in the program. Moreover, it appends the specified suffix
     * to the query and directive symbols.
     * @param suffix The suffix to append to the symbol names.
     * @return A list of Afss from the queries and directives in the program.
     */
    public List<Afs> createListOfAfs(final String suffix) {
        final List<Afs> afs = new ArrayList<Afs>();
        final Afs firstItem = new Afs();
        firstItem.setFiltering(
            FunctionSymbol.create(this.getQuery().getName() + suffix, this.getQuery().getArity()),
            this.getQuery().getModingAsAfs());
        afs.add(firstItem);
        for (final PrologDirective d : this.program.getDirectives()) {
            for (final PrologQuery q : d.toQueries()) {
                final Afs item = new Afs();
                item.setFiltering(FunctionSymbol.create(q.getName() + suffix, q.getArity()), q.getModingAsAfs());
                afs.add(item);
            }
        }
        if (afs.isEmpty()) {
            afs.add(new Afs());
        }
        return afs;
    }

    @Override
    public String export(final Export_Util o) {
        final String res = this.program.export(o) + o.newline();
        return this.query == null ? res + "Empty query." : res + "Query: " + this.query.export(o);
    }

    /**
     * Returns the program.
     * @return The program.
     */
    public PrologProgram getProgram() {
        return this.program;
    }

    @Override
    public ProofPurposeDescriptor getProofPurposeDescriptor() {
        return new PrologProofPurposeDescriptor(this);
    }

    /**
     * @return The query.
     */
    public PrologQuery getQuery() {
        return this.query;
    }

    /**
     * @return Factory for SMT solvers.
     */
    public SMTSolverFactory getSMTFactory() {
        return this.smtFactory;
    }

    /**
     * @return The logic for SMT solvers.
     */
    public SMTLIBLogic getSMTLogic() {
        return this.smtLogic;
    }

    @Override
    public String getStrategyName() {
        switch (this.query.getPurpose()) {
        case TERMINATION:
            return "plterm";
        case COMPLEXITY:
            return "plcomp";
        case DETERMINACY:
            return "pldet";
        default:
            throw new IllegalStateException("Someone found a new goal for analyzing Prolog programs...");
        }
    }

    /**
     * @param smt The SMT setting to use.
     * @return This Prolog problem with the specified SMT setting.
     */
    public PrologProblem setSMT(FrontendSMT smt) {
        return new PrologProblem(this.getProgram(), this.getQuery(), smt.smtSolverFactory, smt.smtLogic);
    }

}
