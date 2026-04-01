/*
 * Created on Jul 4, 2006
 */
package aprove.verification.dpframework.DPProblem.Processors;

import java.util.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Proofs.*;
import aprove.runtime.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import immutables.*;

/**
 * Removes the non usable Equations from ESharp, if we only have
 * A and C Equations in E and their sharped version in ESharp.
 *
 * @author stein
 * @version $Id$
 */

@NoParams
public class ESharpUsableEquationsProcessor extends EDPProblemProcessor {


    @Override
    public boolean isEDPApplicable(EDPProblem edp){
        //processor is only correct for A and C Equations in E and their sharped Version in ESharp
        return !Options.certifier.isCpf() && edp.EAndESharpOnlyAnC()
            //check if we can gain something
            && edp.getUsableESharpEquations().size() < edp.getESharp().size();
    }

    @Override
    protected Result processEDPProblem(EDPProblem edp, Abortion aborter) throws AbortionException {

        if (Globals.useAssertions) {
            assert(this.isEDPApplicable(edp));
        }

        ImmutableSet<Equation> usableESharpEquations = null;
        usableESharpEquations = edp.getUsableESharpEquations();

        ImmutableSet<Equation> oldESharp = edp.getESharp();
        // build new edp-problem
        edp = EDPProblem.create(edp.getP(), usableESharpEquations, edp.getRwithE(), edp.getMinimal());

        Result result = ResultFactory.proved(edp, YNMImplication.EQUIVALENT, new ESharpUsableEquationsProof(oldESharp, usableESharpEquations));
        return result;
    }

    private static class ESharpUsableEquationsProof extends Proof.DefaultProof {

        private final Set<Equation> deletedEquations;

        private ESharpUsableEquationsProof(Set<Equation> oldESharp, Set<Equation> newESharp) {
            Set<Equation> diffSet = new LinkedHashSet<Equation>();
            for(Equation eq:oldESharp) {
                if(!newESharp.contains(eq)) {
                    diffSet.add(eq);
                }
            }
            this.deletedEquations = diffSet;
        }

        @Override
        public String export(Export_Util o, VerbosityLevel level) {
            String res;
            res = "We can delete the following equations of E# with the esharp usable equations processor"+o.cite(Citation.DA_STEIN)+":";
            return o.export(res) + o.set(this.deletedEquations, Export_Util.RULES);
        }

    }

}


