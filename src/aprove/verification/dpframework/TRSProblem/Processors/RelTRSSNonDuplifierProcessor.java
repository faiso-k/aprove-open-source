package aprove.verification.dpframework.TRSProblem.Processors;

import java.util.*;

import org.w3c.dom.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Proofs.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.TRSProblem.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import aprove.xml.*;
import immutables.*;

/**
 * Input:  (R, S)
 * Output: (R u {l -> r | l -> r \in S, l -> r is duplicating}, 
 *             S \ {l -> r | l -> r \in S, l -> r is duplicating})
 *
 * Duplicating Rules in S are the kryptonite for
 * the relative ADP Framework! Hence, try to move
 * all of them to the main TRS.
 *
 * @author Jan-Christoph Kassing
 */
@NoParams
public class RelTRSSNonDuplifierProcessor extends RelTRSProcessor {

    @Override
    public boolean isRelTRSApplicable(final RelTRSProblem problem) {
        //Checks if {l -> r | l -> r \in S, l -> r is duplicating} is non-emptry
        for (final Rule r : problem.getS()) {
            if (r.isDuplicating()) {
                return true;
            }
        }
        return false;
    }

    
    @Override
    public Result processRelTRS(final RelTRSProblem problem, final Abortion aborter, final RuntimeInformation rti)
            throws AbortionException {
        final Set<Rule> newS = new LinkedHashSet<Rule>();
        final Set<Rule> deletedS = new LinkedHashSet<Rule>();
        final Set<Rule> newR = new LinkedHashSet<Rule>(problem.getR());

        for (final Rule r : problem.getS()) {
            if (r.isDuplicating()) {
                deletedS.add(r);
                newR.add(r);
            } else {
                newS.add(r);
            }
        }
        if (Globals.useAssertions) {
            assert ! deletedS.isEmpty()
                : "Found no duplicating l -> r in S although processor was applicable!";
        }


        final RelTRSProblem newProblem = RelTRSProblem.create(ImmutableCreator.create(newR),
                ImmutableCreator.create(newS));
        final Proof proof = new RelTRSSCleanerProof(deletedS, newProblem);
        final Result result = ResultFactory.proved(newProblem, YNMImplication.SOUND, proof);
        return result;
    }

    private static class RelTRSSCleanerProof extends RelTRSProof {

        private final Set<Rule> deletedSRules;
        private final RelTRSProblem newProblem;

        private RelTRSSCleanerProof(final Set<Rule> deletedSRules, final RelTRSProblem newProblem) {
            this.deletedSRules = deletedSRules;
            this.newProblem = newProblem;
        }

        @Override
        public String export(final Export_Util o, final VerbosityLevel level) {
            final StringBuilder res = new StringBuilder(64);
            res.append("We have moved all duplicating rules from S to R ");
            res.append(o.rightarrow());
            res.append(" Duplicating rules:");
            res.append(o.linebreak());
            res.append(o.set(this.deletedSRules, Export_Util.RULES));
            res.append(o.linebreak());
            return res.toString();
        }

        @Override
        public Element toDOM(final Document doc, final XMLMetaData xmlMetaData) {
            final Element e = XMLTag.RELTRS_CLEAN_PROOF.createElement(doc);

            final Element rTag = XMLTag.TRS.createElement(doc);
            for (final Rule rule : this.newProblem.getR()) {
                rTag.appendChild(rule.toDOM(doc, xmlMetaData));
            }
            e.appendChild(rTag);

            final Element sTag = XMLTag.TRS.createElement(doc);
            for (final Rule rule : this.newProblem.getS()) {
                sTag.appendChild(rule.toDOM(doc, xmlMetaData));
            }
            e.appendChild(sTag);
            return e;
        }

        @Override
        public Element toCPF(final Document doc, final Element[] childrenProofs, final XMLMetaData xmlMetaData, final CPFModus modus) {
            if (modus.isPositive()) {
                return CPFTag.RELATIVE_TERMINATION_PROOF.create(doc,
                        CPFTag.EQUALITY_REMOVAL.create(doc,
                        childrenProofs[0]));
            } else {
                return super.ruleRemovalNontermProof(doc, childrenProofs[0], xmlMetaData, this.newProblem);
            }
        }


        @Override
        public boolean isCPFCheckableProof(final CPFModus modus) {
            return true;
        }


    }
}
