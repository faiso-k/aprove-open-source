package aprove.verification.dpframework.DPProblem.Processors;

import java.math.*;
import java.util.*;

import org.w3c.dom.*;

import aprove.prooftree.Export.Utility.*;
import aprove.solver.Engines.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.oldframework.Algebra.Polynomials.SatSearch.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.BooleanSemanticLabelling.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.Formulae.*;
import aprove.verification.oldframework.PropositionalLogic.TheoryPropositions.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.xml.*;
import immutables.*;


/**
 *
 * @author Patrick Kabasci
 * @version $Id$
 *
 */
public class QDPSemanticPOLOLabellingProcessor extends QDPProblemProcessor {

    public static enum QUASI_MODE {
        ALLOW, DISABLE, FORCE
    }

    private final BigInteger range;
    private final QUASI_MODE quasiState;
    private final int dimension;

    @ParamsViaArgumentObject
    public QDPSemanticPOLOLabellingProcessor(Arguments arguments) {
        this.dimension = arguments.dimension;
        this.range = BigInteger.valueOf(arguments.range);
        this.quasiState = arguments.quasi;
    }

    @Override
    public boolean isQDPApplicable(QDPProblem qdp) {
        // Allways applicable.
        return true;
    }


    @Override
    protected Result processQDPProblem(QDPProblem qdp, Abortion aborter) throws AbortionException {
      // First get the P signature of the QDP.
      final Set<Rule> P = this.copyMutable(qdp.getP());
      final Set<Rule> R = qdp.getR();
      final Set<FunctionSymbol> signature = new LinkedHashSet<FunctionSymbol>();
      final Set<TRSVariable> variables= new LinkedHashSet<TRSVariable>();
      for (Rule r: P) {
          r.getLeft().collectFunctionSymbols(signature);
          if (r.getRight() instanceof TRSFunctionApplication) {
              ((TRSFunctionApplication)r.getRight()).collectFunctionSymbols(signature);
          }
          variables.addAll(r.getVariables());
      }
      for (Rule r: qdp.getR()) {
          r.getLeft().collectFunctionSymbols(signature);
          if (r.getRight() instanceof TRSFunctionApplication) {
              ((TRSFunctionApplication)r.getRight()).collectFunctionSymbols(signature);
          }
          variables.addAll(r.getVariables());
      }
      final BSLAutoSearchTermInterpretor ti  = new BSLAutoSearchTermInterpretor(this.quasiState);
      final FormulaFactory<Diophantine> ff = NonCountingCircuitFactory.create(SplitMode.FLATTEN, SplitMode.LEFT_COMB);
      ti.init(ff, this.dimension, signature, variables, false);
      for (Rule r: P) {
          ti.interpretRule(r, true);
      }
      for (Rule r: qdp.getR()) {
          ti.interpretRule(r, false);
      }
      // Now get the monster into the SAT-solver
      final Formula<Diophantine> masterF = ti.getSATFormula();
      final PlainSPCToCircuitConverter spcc =
          PlainSPCToCircuitConverter.create(
              ff.<None> toTheory(),
              new DefaultValueMap<String, BigInteger>(this.range),
              this.range,
              new PoloSatConfigInfo()
          );
      final MINISATEngine.Arguments args = new MINISATEngine.Arguments();
      args.version = 2;
      args.simp = true;
      final MINISATEngine mse = new MINISATEngine(args);
      final SatSearch eng = SatSearch.create(mse, spcc);
      final Map<String, BigInteger> goalState = eng.search(masterF, aborter, ti.interestingVars);
      if (goalState == null) {
          return ResultFactory.unsuccessful();
      }
      ti.result = goalState;
      ti.dump();
      final Set<Rule> newP = new LinkedHashSet<Rule>();
      final Set<Rule> delP = new LinkedHashSet<Rule>();
      final Iterator<Rule> iter = P.iterator();
      while (iter.hasNext()) {
          final Rule cur = iter.next();
          if (!ti.solves(cur)) {
              newP.add(cur);
          } else {
              delP.add(cur);
          }
      }
      final QDPProblem newQDP = qdp.getSubProblem(ImmutableCreator.create(newP));
      // Now check for correctness.
      // First let's see whether we actually found a model.
      ti.checkModel(P);
      ti.checkModel(R);
      // Now check the polynomial interpretation.
      ti.checkPOLO(P, goalState, false);
      ti.checkPOLO(R, goalState, false);
      ti.checkPOLO(delP, goalState, true);
      final Set<Rule> PcupR = new LinkedHashSet<Rule>();
      PcupR.addAll(P);
      PcupR.addAll(R);
      ti.specialize(PcupR, goalState);
      return
          ResultFactory.proved(newQDP, YNMImplication.EQUIVALENT, new QDPSemanticLabellingPOLOProof(ti, qdp, newQDP));
    }

    private TRSFunctionApplication buildfApp(TRSFunctionApplication base, int arg, FunctionSymbol newSym) {
        final ArrayList<TRSTerm> newArgs = new ArrayList<TRSTerm>(newSym.getArity());
        for (int i=0; i<arg; i++) {
            newArgs.add(base.getArgument(i));
        }
        for (int i=arg + 1; i<base.getRootSymbol().getArity(); i++) {
            newArgs.add(base.getArgument(i));
        }
        return TRSTerm.createFunctionApplication(newSym, ImmutableCreator.create(newArgs));
    }

    private boolean contains(Set<FunctionSymbol> set, String name) {
        for (FunctionSymbol fs: set) {
            if (fs.getName().equals(name)) {
                return true;
            }
        }
        return false;
    }

    private Set<Rule> copyMutable(ImmutableSet<Rule> rs) {
        final Set<Rule> ret = new LinkedHashSet<Rule>();
        for (Rule r: rs) {
            ret.add(r);
        }
        return ret;
    }

    private String generateFreshName(String proposal, Set<FunctionSymbol> existing) {
        if (!this.contains(existing, proposal)) {
            return proposal;
        }
        final int i = 0;
        while (true) {
            if (!this.contains(existing, proposal+Integer.toString(i))) {
                return proposal + Integer.toString(i);
            }

        }
    }

    static final class QDPSemanticLabellingPOLOProof extends QDPProof {

        BSLAutoSearchTermInterpretor ti;
        QDPProblem origQdp, newQdp;

        QDPSemanticLabellingPOLOProof (BSLAutoSearchTermInterpretor ti, QDPProblem origQdp, QDPProblem newQdp) {
            this.ti = ti;
            this.origQdp = origQdp;
            this.newQdp = newQdp;
        }

        @Override
        public String export(Export_Util o, VerbosityLevel level) {
            StringBuilder result;
            result = new StringBuilder();
            result.append("We use Semantic Labelling over tuples of bools combined with a Polynomial order to prove this obligation " + o.cite(Citation.SEMLAB));

            result.append(this.ti.getProof(o));

            return result.toString();
        }

        @Override
        public Element toCPF(Document doc, Element[] childrenProofs, XMLMetaData xmlMetaData, CPFModus modus) {
            if (modus.isPositive()) {
                return super.toCPF(doc, childrenProofs, xmlMetaData, modus);
            } else {
                return super.ruleRemovalNontermProof(doc, childrenProofs[0], xmlMetaData, this.newQdp);
            }
        }

        @Override
        public boolean isCPFCheckableProof(CPFModus modus) {
            return !modus.isPositive();
        }

    }

    public static class Arguments {
        public int dimension = 1;
        public int range = 1;
        public QUASI_MODE quasi = QUASI_MODE.DISABLE;
    }

}