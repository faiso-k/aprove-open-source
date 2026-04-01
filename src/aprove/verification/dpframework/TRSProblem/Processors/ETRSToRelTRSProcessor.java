package aprove.verification.dpframework.TRSProblem.Processors;

import java.util.*;

import org.w3c.dom.*;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.prooftree.Proofs.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.TRSProblem.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import aprove.xml.*;
import immutables.*;

/**
 * Transforms an equational TRS problem into a relative TRS problem.
 * For every equation t1 = t2 in E, the relative rules t1 -> t2 and
 * t2 -> t1 are added to S.
 * @author Ulrich Schmidt-Goertz
 * @version $Id$
 */
@NoParams
public class ETRSToRelTRSProcessor extends ETRSProcessor {

    @Override
    public boolean isETRSApplicable(ETRSProblem etrs) {
        return true;
    }

    @Override
    protected Result processETRS(ETRSProblem etrs, Abortion aborter) throws AbortionException {

        Set<Equation> E = etrs.getE();
        Set<Rule> newS = new LinkedHashSet<Rule>(2 * E.size());
        for (Equation eq : E) {
            TRSTerm t1 = eq.getLeft();
            TRSTerm t2 = eq.getRight();
            if (t1.isVariable() || t2.isVariable()) {
                return ResultFactory.notApplicable("All sides of E must contain at least one function symbol");
            }
            newS.add(Rule.create((TRSFunctionApplication)t1, t2));
            newS.add(Rule.create((TRSFunctionApplication)t2, t1));
        }
        RelTRSProblem newProblem = RelTRSProblem.create(etrs.getR(), ImmutableCreator.create(newS));
        return ResultFactory.proved(newProblem, YNMImplication.EQUIVALENT, new ETRSToRelTRSProof(newS, etrs, newProblem));
    }

    public static class ETRSToRelTRSProof extends Proof.DefaultProof {

        private final Set<Rule> newS;
        private final BasicObligation origObl;
        private final BasicObligation resultObl;

        public ETRSToRelTRSProof(final Set<Rule> newS, BasicObligation origObl, BasicObligation resultObl) {
            this.newS = newS;
            this.origObl = origObl;
            this.resultObl = resultObl;
        }

        @Override
        public String export(Export_Util o, VerbosityLevel level) {
            StringBuilder result = new StringBuilder();
            result.append("We transform the equational TRS problem into a relative TRS problem by creating the following relative rules:");
            result.append(o.newline());
            result.append(o.set(this.newS, Export_Util.RULES));
            result.append(o.newline());
            result.append(o.linebreak());
            return result.toString();
        }

        @Override
        public Element toDOM(Document doc, XMLMetaData xmlMetaData) {

            Element proofTag = XMLTag.ETRS_TO_RELTRS_PROOF.createElement(doc);
            Element trsTag = XMLTag.TRS.createElement(doc);
            CollectionUtils.addChildren(this.newS, trsTag, doc, xmlMetaData);
            proofTag.appendChild(trsTag);
            return proofTag;
        }
    }
}
