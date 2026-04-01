package aprove.verification.dpframework.TRSProblem.Processors;

import java.math.*;
import java.util.*;

import org.w3c.dom.*;

import aprove.prooftree.Export.Utility.*;
import aprove.runtime.*;
import aprove.solver.Engines.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPProblem.Processors.QDPSemanticPOLOLabellingProcessor.*;
import aprove.verification.dpframework.TRSProblem.*;
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
 * Semantic Labelling processor for relative termination problems.
 * Labelling courtesy of Patrick Kabasci.
 * @author Ulrich Schmidt-Goertz, Patrick Kabasci
 * @version $Id$
 *
 */
public class RelTRSSemanticLabellingProcessor extends RelTRSProcessor {

    private final BigInteger range;
    private final QUASI_MODE quasiState;
    private final int dimension;

    @ParamsViaArgumentObject
    public RelTRSSemanticLabellingProcessor(final Arguments arguments) {
        this.dimension = arguments.dimension;
        this.range = BigInteger.valueOf(arguments.range);
        this.quasiState = arguments.quasi;
    }

    @Override
    public Result processRelTRS(final RelTRSProblem problem, final Abortion aborter, final RuntimeInformation rti) throws AbortionException {
        if (Options.certifier.isCeta()) {
            return ResultFactory.notApplicable();
        }

      // First get the P signature of the QDP.
      final Set<Rule> R = problem.getR();
      final Set<Rule> S = problem.getS();

      final Set<FunctionSymbol> signature = new LinkedHashSet<FunctionSymbol>();
      final Set<TRSVariable> variables= new LinkedHashSet<TRSVariable>();

      for (final Rule r: S) {
          r.getLeft().collectFunctionSymbols(signature);
          if (r.getRight() instanceof TRSFunctionApplication) {
              ((TRSFunctionApplication)r.getRight()).collectFunctionSymbols(signature);
          }
          variables.addAll(r.getVariables());
      }
      for (final Rule r: problem.getR()) {
          r.getLeft().collectFunctionSymbols(signature);
          if (r.getRight() instanceof TRSFunctionApplication) {
              ((TRSFunctionApplication)r.getRight()).collectFunctionSymbols(signature);
          }
          variables.addAll(r.getVariables());
      }
      final BSLAutoSearchTermInterpretor ti  = new BSLAutoSearchTermInterpretor(this.quasiState);

      final FormulaFactory<Diophantine> ff = NonCountingCircuitFactory.create(SplitMode.FLATTEN, SplitMode.LEFT_COMB);
      ti.init(ff, this.dimension, signature, variables, true);

      for (final Rule r: S) {
          ti.interpretRule(r, true);
      }
      for (final Rule r: problem.getR()) {
          ti.interpretRule(r, true);
      }

      // Now get the monster into the SAT-solver
      final Formula<Diophantine> masterF = ti.getSATFormula();

      final PlainSPCToCircuitConverter spcc = PlainSPCToCircuitConverter.create(
              ff.<None> toTheory(), new DefaultValueMap<String, BigInteger>(this.range), this.range, new PoloSatConfigInfo());

      final MINISATEngine.Arguments args = new MINISATEngine.Arguments();
      args.version = 2;
      final MINISATEngine mse = new MINISATEngine(args);
      final SatSearch eng = SatSearch.create(mse, spcc);
      final Map<String, BigInteger> goalState = eng.search(masterF, aborter, ti.interestingVars);

      if (goalState == null) {
          return ResultFactory.unsuccessful();
      }
      ti.result = goalState;
      ti.dump();

      final Set<Rule> newR = new LinkedHashSet<Rule>();
      final Set<Rule> delR = new LinkedHashSet<Rule>();
      final Iterator<Rule> iter = R.iterator();
      while (iter.hasNext()) {
          final Rule cur = iter.next();
          if (!ti.solves(cur)) {
              newR.add(cur);
          } else {
              delR.add(cur);
          }
      }
      final Set<Rule> newS = new LinkedHashSet<Rule>();
      final Set<Rule> delS = new LinkedHashSet<Rule>();
      final Iterator<Rule> iterS = S.iterator();
      while (iterS.hasNext()) {
          final Rule cur = iterS.next();
          if (!ti.solves(cur)) {
              newS.add(cur);
          } else {
              delS.add(cur);
          }
      }

      final RelTRSProblem newRelTRS = problem.createSubProblem(
              ImmutableCreator.create(newR), ImmutableCreator.create(newS));

      // Now check for correctness.
      // First let's see whether we actually found a model.
      ti.checkModel(S);
      ti.checkModel(R);
      // Now check the polynomial interpretation.
      ti.checkPOLO(S, goalState, false);
      ti.checkPOLO(R, goalState, false);
      ti.checkPOLO(delS, goalState, true);
      ti.checkPOLO(delR, goalState, true);

      final Set<Rule> ScupR = new LinkedHashSet<Rule>();
      ScupR.addAll(S);
      ScupR.addAll(R);

      ti.specialize(ScupR, goalState);



        return ResultFactory.proved(newRelTRS, YNMImplication.EQUIVALENT, new RelTRSSemanticLabellingPOLOProof(
            ti,
            delR,
            delS,
            problem,
            newRelTRS));

    }

    private TRSFunctionApplication buildfApp(final TRSFunctionApplication base, final int arg, final FunctionSymbol newSym) {
        final ArrayList<TRSTerm> newArgs = new ArrayList<TRSTerm>(newSym.getArity());
        for(int i=0; i<arg; i++) {
            newArgs.add(base.getArgument(i));
        }
        for(int i=arg + 1; i<base.getRootSymbol().getArity(); i++) {
            newArgs.add(base.getArgument(i));
        }
        return TRSTerm.createFunctionApplication(newSym, ImmutableCreator.create(newArgs));
    }

    private boolean contains(final Set<FunctionSymbol> set, final String name) {
        for (final FunctionSymbol fs: set) {
            if (fs.getName().equals(name)) {
                return true;
            }
        }
        return false;
    }

    private Set<Rule> copyMutable(final ImmutableSet<Rule> rs) {
        final Set<Rule> ret = new LinkedHashSet<Rule>();
        for(final Rule r: rs) {
            ret.add(r);
        }
        return ret;
    }

    private String generateFreshName(final String proposal, final Set<FunctionSymbol> existing) {
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

    static final class RelTRSSemanticLabellingPOLOProof extends RelTRSProof {

        BSLAutoSearchTermInterpretor ti;
        Set<Rule> deletedRRules, deletedSRules;
        RelTRSProblem oldProblem;
        RelTRSProblem newProblem;

        RelTRSSemanticLabellingPOLOProof(
                final BSLAutoSearchTermInterpretor ti,
                final Set<Rule> delR,
            final Set<Rule> delS,
            final RelTRSProblem oldProblem,
            final RelTRSProblem newProblem)
        {
            this.ti = ti;
            this.deletedRRules = delR;
            this.deletedSRules = delS;
            this.newProblem = newProblem;
            this.oldProblem = oldProblem;
        }

        @Override
        public String export(final Export_Util o, final VerbosityLevel level) {
            StringBuilder result;
            result = new StringBuilder();
            result.append("We use Semantic Labelling over tuples of bools combined with a polynomial order " + o.cite(Citation.SEMLAB));
            result.append(this.ti.getProof(o));
            result.append(o.linebreak());
            result.append("The following rules were deleted from R:");
            result.append(o.linebreak());
            result.append(o.set(this.deletedRRules, Export_Util.RULES));
            result.append(o.linebreak());
            result.append("The following rules were deleted from S:");
            result.append(o.linebreak());
            result.append(o.set(this.deletedSRules, Export_Util.RULES));
            result.append(o.newline());
            result.append(o.linebreak());

            return result.toString();
        }

        @Override
        public Element toCPF(
            final Document doc,
            final Element[] childrenProofs,
            final XMLMetaData xmlMetaData,
            final CPFModus modus)
        {
            final Element childProof = childrenProofs[0];
            if (modus.isPositive()) {
                final Element unlab =
                    CPFTag.RELATIVE_TERMINATION_PROOF.create(
                        doc,
                        CPFTag.UNLAB.create(
                            doc,
                            CPFTag.trs(doc, xmlMetaData, this.newProblem.getR()),
                            CPFTag.trs(doc, xmlMetaData, this.newProblem.getS()),
                            childProof));
                final XMLMetaData newMetaData = null; // TODO: require metadata over labeled signature
                final Element order = null; // TODO: ti does not provide order;
                final Element model = null; //TODO: ti does not provide model
                final Element rr =
                    CPFTag.RELATIVE_TERMINATION_PROOF.create(doc, CPFTag.RULE_REMOVAL.create(doc,
                            order,
                            CPFTag.trs(
                                doc,
                                newMetaData,
                                this.ti.getLabelledSystem(this.newProblem.getR(), this.ti.result)),
                            CPFTag.trs(
                                doc,
                                newMetaData,
                                this.ti.getLabelledSystem(this.newProblem.getS(), this.ti.result)),
                        unlab));
                final Element semlab =
                    CPFTag.RELATIVE_TERMINATION_PROOF.create(
                        doc,
                        CPFTag.SEMLAB.create(
                            doc,
                            model,
                            CPFTag.trs(
                                doc,
                                newMetaData,
                                this.ti.getLabelledSystem(this.oldProblem.getR(), this.ti.result)),
                            CPFTag.trs(
                                doc,
                                newMetaData,
                                this.ti.getLabelledSystem(this.oldProblem.getS(), this.ti.result)),
                            rr));
                return semlab;
            } else {
                return super.ruleRemovalNontermProof(doc, childProof, xmlMetaData, this.newProblem);
            }
        }

        @Override
        public boolean isCPFCheckableProof(final CPFModus modus) {
            return !modus.isPositive(); // TODO: activate positive mode, once TODOs above have been fixed
        }

    }

    public static class Arguments {
        public int dimension = 1;
        public int range = 1;
        public QUASI_MODE quasi = QUASI_MODE.DISABLE;
    }

}