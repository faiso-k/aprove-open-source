package aprove.verification.dpframework.HaskellProblem.Processors;

import java.util.*;
import java.util.logging.*;

import aprove.runtime.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.HaskellProblem.*;
import aprove.verification.oldframework.Haskell.*;
import aprove.verification.oldframework.Haskell.Expressions.*;
import aprove.verification.oldframework.Haskell.Modules.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 *
 * Splits the Haskell program into sub-programs which have only one startterm each.
 * Furthermore, the type expressions are converted, since the type annotation has been incorporated into the types.
 *
 * @author Stephan Swiderski
 */
@NoParams
public class SplitProcessor extends HaskellProcessor {
    protected static Logger logger = Logger.getLogger("aprove.verification.theoremprover.Haskell");

    @Override
    protected Set<Class<? extends HaskellProcessor>> getPreconditionTransformations(HaskellProgram hp) {
        Set<Class<? extends HaskellProcessor>> procs = new LinkedHashSet<Class<? extends HaskellProcessor>>(this.getAllRequiredTransformationProcessors());
        return procs;
    }


    @Override
    public Result process(HaskellProgram obj, Abortion aborter) {
        HaskellProgram hp = obj;
        int len = hp.getModules().getStartTerms().size();


        // remove type expressions (such as e.g. x :: [a])
        hp.getModules().visit(new TypeExpRemoveVisitor());

        if (len == 1) {
            // there already is only one startterm
            return null;
        }

        List<HaskellProgram> em = new Vector<HaskellProgram>();
        for (int i = 0; i < len;i++){
             HaskellProgram cur = obj.deepcopy();
             List<Pair<HaskellObject,HaskellExp>> sts = new Vector<Pair<HaskellObject,HaskellExp>>();
             sts.add(cur.getModules().getStartTerms().get(i));
             cur.getModules().setStartTerms(sts);
             em.add(cur);
        }
        if (hp.getModules().getStartTerms().size() < 1) {
            if (Options.isWebInterfaceMode) {
                System.out.println("<p>No startterms found!</p>");
            }
            return ResultFactory.notApplicable("No startterms were provided");
        }
        return ResultFactory.provedAnd(em,YNMImplication.EQUIVALENT,new SplitProof(hp));
    }


    private static class TypeExpRemoveVisitor extends HaskellVisitor {

        @Override
        public boolean guardStartTerms(Modules ho) { return true; }

        @Override
        public HaskellObject caseTypeExp(TypeExp ho) {
            // this removes the type attached to this expression
            return ho.getExpression();
        }

    }
}
