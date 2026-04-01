
package aprove.verification.dpframework.TRSProblem.Processors;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.TRSProblem.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.theoremprover.TerminationProofs.*;
import immutables.*;

/**
 * Rename rules to standard representation.
 * Primarily meant for exporting purposes, efficiency might be
 * improved by not disregarding cached components of the QTRS.
 *
 * @author fuhs
 */
public class QTRSStandardRepresentationProcessor extends QTRSProcessor {

    private static final Proof theProof = new QTRSStandardRepresentationProof();

    @Override
    public boolean isQTRSApplicable(QTRSProblem qtrs) {
        return true;
    }

    @Override
    protected Result processQTRS(QTRSProblem qtrs, Abortion aborter, RuntimeInformation rti) throws AbortionException {
        QTRSProblem newQtrs = this.computeStandardRepresentation(qtrs, aborter);
        if (newQtrs == null) {
            return ResultFactory.unsuccessful("This QTRS already is in standard representation.");
        }

        Result result = ResultFactory.proved(newQtrs,
                YNMImplication.EQUIVALENT, QTRSStandardRepresentationProcessor.theProof);
        return result;
    }

    public QTRSProblem computeStandardRepresentation(QTRSProblem qtrs, Abortion aborter) throws AbortionException {
        Set<Rule> oldR = qtrs.getR();
        ImmutableSet<Rule> newImmutableR = this.computeStandardRepresentation(oldR, aborter);
        if (newImmutableR == null) {
            return null; // the old QTRS problem already is what you wanted
        }
        QTRSProblem newQtrs = QTRSProblem.create(newImmutableR, qtrs.getQ());
        return newQtrs;
    }

    public ImmutableSet<Rule> computeStandardRepresentation(Set<Rule> rules, Abortion aborter) throws AbortionException {
        Set<Rule> newRules = new LinkedHashSet<Rule>(rules.size());
        boolean someNonStdRepresentation = false;
        for (Rule rule : rules) {
            aborter.checkAbortion();
            if (rule.isInStandardRepresentation()) {
                newRules.add(rule);
            }
            else {
                someNonStdRepresentation = true;
                Rule newRule = rule.getStandardRepresentation();
                newRules.add(newRule);
            }
        }

        if (! someNonStdRepresentation) {
            return null; // the old rule set already is what you wanted
        }
        aborter.checkAbortion();
        ImmutableSet<Rule> newImmutableR = ImmutableCreator.create(newRules);
        return newImmutableR;
    }


    private static class QTRSStandardRepresentationProof extends Proof {

        private QTRSStandardRepresentationProof() {}

        @Override
        public String export(Export_Util o) {
            return "Renamed variables in QTRS rules to standard representation.";
        }
    }
}
