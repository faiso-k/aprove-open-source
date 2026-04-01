package aprove.verification.dpframework.TRSProblem.Processors;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.TRSProblem.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.theoremprover.TerminationProofs.*;
import immutables.*;

/**
 * Adds the C_E rules {c(x,y) -> x, c(x,y) -> y} for a fresh symbol c to a TRS.
 * Q is not changed. This processor is probably not very useful for general
 * termination proving, but it allows to investigate C_E-termination.
 *
 * @author fuhs
 */
@NoParams
public class QTRSIntroduceCEProcessor extends QTRSProcessor {

    private static String ceSymbolNameProposal = "c";
    private static String var1NameProposal = "x";
    private static String var2NameProposal = "y";

    @Override
    public boolean isQTRSApplicable(QTRSProblem qtrs) {
        return true;
    }

    @Override
    protected Result processQTRS(QTRSProblem qtrs, Abortion aborter, RuntimeInformation rti)
            throws AbortionException {
        // generate fresh name for root symbol of the C_E rules
        Set<String> names = CollectionUtils.getNames(qtrs.getSignature());
        @SuppressWarnings("unchecked")
        Set<TRSVariable> vars = (Set<TRSVariable>)CollectionUtils.getVariables(qtrs.getTerms());
        names.addAll(CollectionUtils.getNames(vars));

        String cName = QTRSIntroduceCEProcessor.getFreshName(names, QTRSIntroduceCEProcessor.ceSymbolNameProposal);
        String xName = QTRSIntroduceCEProcessor.getFreshName(names, QTRSIntroduceCEProcessor.var1NameProposal);
        String yName = QTRSIntroduceCEProcessor.getFreshName(names, QTRSIntroduceCEProcessor.var2NameProposal);

        // generate c, x, y
        FunctionSymbol c = FunctionSymbol.create(cName, 2);
        TRSVariable x = TRSTerm.createVariable(xName);
        TRSVariable y = TRSTerm.createVariable(yName);

        // generate C_E-rules
        ArrayList<TRSTerm> leftArgs = new ArrayList<TRSTerm>(2);
        leftArgs.add(x);
        leftArgs.add(y);
        TRSFunctionApplication left = TRSTerm.createFunctionApplication(c, leftArgs);
        Rule firstRule = Rule.create(left, x);
        Rule secondRule = Rule.create(left, y);

        // build new TRS and return result
        LinkedHashSet<Rule> rules = new LinkedHashSet<Rule>(qtrs.getR());
        rules.add(firstRule);
        rules.add(secondRule);
        ImmutableLinkedHashSet<Rule> immRules = ImmutableCreator.create(rules);
        QTRSProblem newQtrs = QTRSProblem.create(immRules, qtrs.getQ());
        Proof proof = new QTRSIntroduceCEProof(firstRule, secondRule);
        return ResultFactory.proved(newQtrs, YNMImplication.SOUND, proof);
    }

    private static String getFreshName(Set<String> used, String proposal) {
        String res = proposal;
        int i = 0;
        while (used.contains(res)) {
            res = proposal + i++;
        }
        used.add(res);
        return res;
    }


    private class QTRSIntroduceCEProof extends Proof {

        private final Rule r1;
        private final Rule r2;

        public QTRSIntroduceCEProof(Rule r1, Rule r2) {
            this.r1 = r1;
            this.r2 = r2;
        }

        @Override
        public String export(Export_Util o) {
            return "Added C"+o.sub("E")+"-rules " + o.export(this.r1) +
            " and " + o.export(this.r2) + '.';
        }
    }
}
