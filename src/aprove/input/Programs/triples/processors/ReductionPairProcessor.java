package aprove.input.Programs.triples.processors;

import java.util.*;

import aprove.input.Programs.prolog.structure.*;
import aprove.input.Programs.triples.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Proofs.*;
import aprove.solver.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.dpframework.Orders.*;
import aprove.verification.oldframework.Utility.*;

public class ReductionPairProcessor extends TriplesProblemProcessor {

    private final SolverFactory factory;

    @ParamsViaArgumentObject
    public ReductionPairProcessor(Arguments arguments) {
        this.factory = arguments.order;
    }


    @Override
    public boolean isTriplesApplicable(TriplesProblem pp) {
        return true;
    }

    @Override
    public Result processTriplesProblem(TriplesProblem tp, Abortion aborter)
            throws AbortionException {
        PrologProgram triples = tp.getTriples();
        Set<Rule> constraints = new LinkedHashSet<Rule>();
        Afs afs = tp.getAfs();
        // iterate over all triples

        for (PrologClause triple : triples.getClauses()) {
            // for each triple, get H and B
            PrologTerm lastAtom = triple.getBody();
            while (lastAtom.isConjunction()) {
                lastAtom = lastAtom.getArgument(1);
            }
            PrologTerm firstAtom = triple.getHead();
            TRSTerm H = firstAtom.toTerm();
            TRSTerm B = lastAtom.toTerm();
            H = afs.filterTerm(H);
            B = afs.filterTerm(B);
            constraints.add(Rule.create((TRSFunctionApplication) H,B));
        }

        QActiveSolver solver = this.factory.getQActiveSolver();
        QActiveOrder order = solver.solveQActive(constraints, new LinkedHashMap<Rule, QActiveCondition>(), false, true, aborter);
        if (order == null) {
            return ResultFactory.unsuccessful();
        }
        order = new AfsOrder(afs, order);

        return ResultFactory.proved(new ReductionPairProof(order));
    }

    public static class ReductionPairProof extends Proof.DefaultProof {

        private QActiveOrder order;

        public ReductionPairProof(QActiveOrder order) {
            this.order = order;
        }

        @Override
        public String export(Export_Util o, VerbosityLevel level) {
            return o.export(this.order);
        }

    }

    public static class Arguments {
        public SolverFactory order;
    }

}
