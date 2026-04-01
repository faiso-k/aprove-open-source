package aprove.verification.complexity.LowerBounds;

import java.util.*;

import aprove.cli.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.prooftree.Proofs.Proof.*;
import aprove.runtime.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.complexity.Implications.*;
import aprove.verification.complexity.LowerBounds.AnalysisOrder.*;
import aprove.verification.complexity.LowerBounds.BasicStructures.*;
import aprove.verification.complexity.LowerBounds.GeneratorEquations.*;
import aprove.verification.complexity.LowerBounds.Util.Renaming.*;
import aprove.verification.complexity.TruthValue.*;
import aprove.verification.complexity.Utility.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.Graph.*;

public class CpxTrsLowerBoundsOrderProcessor extends Processor.ProcessorSkeleton {

    @Override
    public boolean isApplicable(BasicObligation obl) {
        TruthValue truth = obl.getTruthValue();
        if (truth instanceof ComplexityYNM) {
            ComplexityYNM complexity = (ComplexityYNM) truth;
            if (complexity.getLowerBound().isInfinite()) {
                return false;
            }
        }
        return obl instanceof CpxTrsLowerBoundsProblem && Options.certifier == Certifier.NONE;
    }

    @Override
    public Result
            process(BasicObligation obl, BasicObligationNode oblNode, Abortion aborter, RuntimeInformation rti) throws AbortionException {
        CpxTrsLowerBoundsOrderWorker worker = new CpxTrsLowerBoundsOrderWorker();
        Result res = worker.process(obl, oblNode, aborter, rti);
        return res;
    }

    /**
     * Helper class to encapsulate the instance-dependent state of the
     * computation by the processor.
     */
    private static class CpxTrsLowerBoundsOrderWorker {
        private DependencyGraph<LowerBoundsTrs> analysisOrderGraph;

        @SuppressWarnings("unused")
        public Result
                process(BasicObligation obl, BasicObligationNode oblNode, Abortion aborter, RuntimeInformation rti) throws AbortionException {
            CpxTrsLowerBoundsProblem cpxObl = (CpxTrsLowerBoundsProblem) obl;
            LowerBoundsTrs trs = cpxObl.getTrs();
            this.analysisOrderGraph = new SimplifiedDependencyGraph(trs);
            RenamingCentral renamingCentral = cpxObl.getRenamingCentral();
            TermGenerator termGenerator = new TermGenerator(trs, renamingCentral);
            GeneratorEquations generatorEquations = new GeneratorEquations(trs, termGenerator);
            TRSFunctionApplication arbitraryTerm = TRSTerm.createFunctionApplication(renamingCentral.freshConstant("*"));
            OrderedCpxTrsLowerBoundsProblem newObl = new OrderedCpxTrsLowerBoundsProblem(trs, renamingCentral, this.analysisOrderGraph, generatorEquations, arbitraryTerm);
            return ResultFactory.proved(newObl, LowerBound.create(), new OrderProof(this.analysisOrderGraph));
        }
    }

    private static class OrderProof extends DefaultProof {

        private DependencyGraph<LowerBoundsTrs> order;

        public OrderProof(DependencyGraph<LowerBoundsTrs> order) {
            super();
            this.order = order.clone();
        }

        @Override
        public String export(Export_Util eu, VerbosityLevel level) {
            StringBuilder sb = new StringBuilder();
            sb.append(eu.escape("Heuristically decided to analyse the following defined symbols:"));
            sb.append(eu.linebreak());
            Iterator<Node<FunctionSymbol>> it = this.order.getNodes().iterator();
            while (it.hasNext()) {
                sb.append(it.next().getObject().export(eu));
                if (it.hasNext()) {
                    sb.append(eu.escape(", "));
                }
            }
            String orderStr = this.order.export(eu);
            if (!orderStr.isEmpty()) {
                sb.append(eu.paragraph());
                sb.append(eu.escape("They will be analysed ascendingly in the following order:"));
                sb.append(eu.linebreak());
                sb.append(orderStr);
            }
            return sb.toString();
        }

    }
}
