package aprove.verification.relative.RelADPProblem.Processors;

import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.Set;

import aprove.prooftree.Export.Utility.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.dpframework.TRSProblem.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.relative.RelADPProblem.*;
import immutables.*;

/**
 * Derelatifying Processor as described in Vartanyan's bachelor thesis
 * 
 * @author Grigory Vartanyan, Jan-Christoph Kassing
 * @version $Id$
 */
public class RelADPDerelatifyInADPsProcessor extends RelADPProblemProcessor {

    // ================================================================================
    // isApplicable
    // ================================================================================

    @Override
    public boolean isRelADPPApplicable(RelADPProblem reladpp) {
        return true;
    }

    // ================================================================================
    // Processing
    // ================================================================================

    @Override
    protected Result processRelADPProblem(RelADPProblem origreladpp, final Abortion aborter) throws AbortionException {
        Set<RelADPProblem> new_problems = new LinkedHashSet<RelADPProblem>(origreladpp.getPRel().size());

        for (Rule adp: origreladpp.getPRel()) {
            if(adp.getRight().countAnnos(origreladpp.getDeannotator().keySet()) > 0) {
                Set<Rule> abs = new HashSet<Rule>(origreladpp.getPAbs());
                Set<Rule> rel = new HashSet<Rule>(origreladpp.getPRel());

                TRSTerm rhs = adp.getRight();
                for (final Pair<Position, TRSTerm> posAndSubterm : rhs.getPositionsWithSubTerms()) {
                    if (posAndSubterm.y.isVariable()) {continue;}  // Skip if subterm is a variable

                    final TRSFunctionApplication subterm = (TRSFunctionApplication) posAndSubterm.y;
                    final FunctionSymbol root = subterm.getRootSymbol();

                    if (!origreladpp.getAnnotatedSignature().contains(root)) {continue;}  // Skip if subterm isn't annotated symbol
                    
                    //At this point, we reached an annotated symbol in the right-hand side
                    Set<Position> poses = rhs.getPositions();
                    poses.remove(posAndSubterm.x);
                    final TRSTerm anno_rhs = ((TRSFunctionApplication) rhs).renameAtAllMap(poses, origreladpp.getDeannotator());
                    final Rule newAdp = Rule.create(adp.getLeft(), anno_rhs);
                    abs.add(newAdp);
                }
                
                rel.remove(adp);
                
                new_problems.add(RelADPProblem.create(abs, rel, origreladpp.getQ(), origreladpp.getBiAnnoMap()));
            }
        }

        RelADPDerelatifying2Proof proof = new RelADPDerelatifying2Proof(origreladpp, new_problems);

        final Result result = ResultFactory.provedOr(new_problems, YNMImplication.SOUND, proof);
        return result;
    }

    // ================================================================================
    // Proof
    // ================================================================================

    private static class RelADPDerelatifying2Proof extends RelADPProof {

        private final RelADPProblem reladpp;
        private final Set<RelADPProblem> relADPs;

        private RelADPDerelatifying2Proof(final RelADPProblem reladpp, final Set<RelADPProblem> relADPs) {
            this.reladpp = reladpp;
            this.relADPs = relADPs;
        }

        @Override
        public String export(final Export_Util o, final VerbosityLevel level) {
            String res = "";
            res += o.paragraph();
            res += "We use the second derelatifying processor (moving relative rules)" + o.cite(Citation.IJCAR24) + ".";
            res += o.linebreak();
            res += "We move one relative ADP with annotations to the non-relative part ";
            res += "and create an own Problem for each movable rule.";

            res += o.paragraph();
            res += "Resulting in " + (relADPs.size()) + " subproblem" + ((relADPs.size() == 1) ? "" : "s") + ".";
            res += o.cond_linebreak();
            res += "If one of them is SN, then our original relative ADP problem is SN";

            return o.export(res);
        }
    }
}
