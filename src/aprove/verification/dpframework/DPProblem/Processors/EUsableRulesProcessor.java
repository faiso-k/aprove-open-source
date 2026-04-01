/*
 * Created on May 23, 2006
 */
package aprove.verification.dpframework.DPProblem.Processors;


import java.util.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Proofs.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.dpframework.TRSProblem.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import immutables.*;

/**
 * Equational usable Rules Processor. Eliminates Rules from R and Equations from E
 * that are not usable - calculated in EUsableRules.
 *
 * @author stein
 * @version $Id$
 */

@NoParams
public class EUsableRulesProcessor extends EDPProblemProcessor {


    @Override
    public boolean isEDPApplicable(EDPProblem edp) {
        //if we only have A and C Equations fulfill the conditions of finite E-equivalenceclasses,
        // non-collapsing Equations with identical unique variables
        return edp.EAndESharpOnlyAnC()
            //we demand minimality
            && edp.getMinimal()
            //check if we can gain something
            && edp.getUsableRules().size() < edp.getR().size();
    }

    @Override
    protected Result processEDPProblem(EDPProblem edp, Abortion aborter) throws AbortionException {

        if (Globals.useAssertions) {
            assert(this.isEDPApplicable(edp));
        }

        Set<Rule> ceRules = null;
        ImmutableSet<Rule> usableRules;
        ImmutableSet<Equation> usableEquations;
        boolean useImproved = false;
        //take improved usable rules and equations in C case
        if(edp.getRwithE().checkC()) {
            useImproved = true;
            ECUsableRules U = new ECUsableRules(edp.getRwithE());
            usableRules = U.getUsableRules(edp.getP(),edp.getESharp());
            usableEquations = U.getUsableEquations(edp.getP(),edp.getESharp());
        }
        else {
            usableRules = edp.getUsableRules();
            usableEquations = edp.getUsableEquations();
        }

        Set<FunctionSymbol> signature = edp.getSignature();
        // find ce-symbol
        final String prefix = "c";
        int postfix = 1;
        FunctionSymbol c = FunctionSymbol.create(prefix, 2);
        while (signature.contains(c)) {
            c = FunctionSymbol.create(prefix+postfix, 2);
            postfix ++;
        }

        TRSVariable x = TRSTerm.createVariable("x");
        TRSVariable y = TRSTerm.createVariable("y");
        TRSFunctionApplication cxy;

        // add c(x,y) -> x, c(x,y) -> y to usable rule set
        cxy = TRSTerm.createFunctionApplication(c, new TRSTerm[]{x, y});

        // add rules
        ceRules = new LinkedHashSet<Rule>();
        ceRules.add(Rule.create(cxy, x));
        ceRules.add(Rule.create(cxy, y));

        Set<Rule> newUsable = new LinkedHashSet<Rule>(usableRules);
        newUsable.addAll(ceRules);
        usableRules = ImmutableCreator.create(newUsable);


        // build new edp-problem
        ETRSProblem rWithE = ETRSProblem.create(usableRules, usableEquations);
        edp = EDPProblem.create(edp.getP(), edp.getESharp(), rWithE, false);

        Result result = ResultFactory.proved(edp, YNMImplication.EQUIVALENT, new EUsableRulesProof(ceRules, useImproved));
        return result;
    }

    private static class EUsableRulesProof extends Proof.DefaultProof {

        private final Set<Rule> ceRules;
        private boolean usedImproved;

        private EUsableRulesProof(Set<Rule> ceRules, boolean usedImproved) {
            this.ceRules = ceRules;
            this.usedImproved = usedImproved;
        }

        @Override
        public String export(Export_Util o, VerbosityLevel level) {
            String res;
            res = "We use the";
            if(this.usedImproved) {
                res += " improved";
            }
            res += " usable rules and equations processor "+o.cite(Citation.DA_STEIN)+
            " to delete all non-usable rules from R " +
                        "and all non-usable equations from E, but " +
                        "we lose minimality and add the following 2 Ce-rules:";
            return o.export(res) + o.set(this.ceRules, Export_Util.RULES);
        }

    }

}

