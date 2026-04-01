package aprove.verification.complexity.CpxIntTrsProblem.Processors;

import java.io.*;
import java.math.*;
import java.util.*;

import aprove.verification.complexity.CpxIntTrsProblem.*;
import aprove.verification.complexity.CpxIntTrsProblem.Exceptions.*;
import aprove.verification.complexity.CpxIntTrsProblem.Structures.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

public class CpxIntTrsToFSTExportProcessor extends CpxIntTrsExportProcessor {

    /**
     * Turns an intTRS into a FST thingy.
     * @param intTrs some intTRS
     * @return a string containing a "FST" doing the same thing
     */
    @Override
    protected void export(final CpxIntTrsProblem obl, final Appendable o) throws IOException {
        CpxIntTrsToFSTExportWorker worker = new CpxIntTrsToFSTExportWorker();
        worker.export(obl, o);
    }

    /**
     * Helper class to encapsulate the instance-dependent state of the
     * computation by the processor.
     */
    private static class CpxIntTrsToFSTExportWorker {
        private int transCounter = 1;
        private final Set<TRSVariable> variables = new LinkedHashSet<>();

        /**
         * Turns an intTRS into a FST thingy.
         * @param intTrs some intTRS
         * @return a string containing a "FST" doing the same thing
         */
        @SuppressWarnings("boxing")
        protected void export(final CpxIntTrsProblem obl, final Appendable o) throws IOException {

            final Set<CpxIntTupleRule> rules = obl.getK().keySet();

            //First, check that we have only one rhs for every rule:
            for (final CpxIntTupleRule rule : rules) {
                if (rule.getRights().size() > 1) {
                    throw new UnsupportedOperationException("Can't encode several rhs into FST");
                }
            }

            //First, normalize the rules to have the same number of arguments:
            final Pair<Map<FunctionSymbol, Integer>, Set<CpxIntTupleRule>> p = CpxIntTrsToFSTExportWorker.normalizeFs(rules);
            final Map<FunctionSymbol, Integer> pcMap = p.x;
            final Set<CpxIntTupleRule> normalizedRules = p.y;

            //Now, handle each rule separately:
            final StringBuilder ruleSB = new StringBuilder();
            for (final CpxIntTupleRule rule : normalizedRules) {
                this.transformRuleToTransition(pcMap, rule, ruleSB);
            }

            //We collected all needed information on the way. Put everything together:
            o.append("model main {\n");

            //Declarations for variables and states:
            o.append("var ");
            boolean notFirst = false;
            for (final TRSVariable v : this.variables) {
                if (notFirst) {
                    o.append(",");
                }
                o.append(v.toString());
                notFirst = true;
            }
            o.append(";\n");
            o.append("states start,stop");
            for (final Integer id : pcMap.values()) {
                o.append(",loc_").append(id.toString());
            }
            o.append(";\n");

            //Connect start to everything:
            for (final Integer id : pcMap.values()) {
                o.append("transition start_").append(id.toString()).append(" :={\n");
                o.append("  from  := start;\n");
                o.append("  to    := loc_").append(id.toString()).append(";\n");
                o.append("  guard :=;\n");
                o.append("  action :=;\n");
                o.append("};\n");
            }

            //Add the transition encoding:
            o.append(ruleSB.toString());

            //Give the start strategy:
            o.append("}\n");
            o.append("strategy dumb {\n");
            o.append("Region init := { state = start && true };\n");
            o.append("}\n");
        }

        /**
         * Transform an intTRS-rule to a FST-style transition
         * @param pcMap a map from function symbol to integers
         * @param rule the rule that should be transformed
         * @param ruleSB the StringBuilder to which we add the encoded transition
         * @throws IOException
         */
        private void transformRuleToTransition(
            final Map<FunctionSymbol, Integer> pcMap,
            final CpxIntTupleRule rule,
            final StringBuilder ruleSB)
        {
            //Rename variables on the left to standard form:
            final CpxIntTupleRule ruleWithX = rule.getWithRenumberedVariables("x");
            final TRSFunctionApplication renamedLHS = ruleWithX.getLeft();
            final TRSFunctionApplication renamedRHS = ruleWithX.getRights().get(0);

            //Do some of the names:
            final String transName = "t_" + ++this.transCounter;
            final String startLocName = "loc_" + pcMap.get(renamedLHS.getRootSymbol());
            final String endLocName = "loc_" + pcMap.get(renamedRHS.getRootSymbol());
            //First step: Note variables so that we can declare them
            this.variables.addAll(renamedLHS.getVariables());
            this.variables.addAll(renamedRHS.getVariables());
            if (ruleWithX.getConstraintTerm() != null) {
                this.variables.addAll(ruleWithX.getConstraintTerm().getVariables());
            }
            //Second step: Encode the condition.
            final TRSTerm cond = ruleWithX.getConstraintTerm();
            final StringBuilder condSB = new StringBuilder();
            if (cond != null) {
                CpxIntTrsToFSTExportWorker.exportIntTerm(cond, condSB);
            }
            //Third step: Encode the updates:
            final StringBuilder updateSB = new StringBuilder();
            final ImmutableList<TRSTerm> vars = renamedLHS.getArguments();
            final ImmutableList<TRSTerm> newValues = renamedRHS.getArguments();
            for (int i = 0; i < vars.size(); i++) {
                final TRSVariable var = (TRSVariable) vars.get(i);
                final TRSTerm value = newValues.get(i);
                if (i > 0) {
                    updateSB.append(", ");
                }
                updateSB.append(var).append("\' = ");
                CpxIntTrsToFSTExportWorker.exportIntTerm(value, updateSB);
            }
            ruleSB.append("transition ").append(transName).append(" :={\n");
            ruleSB.append("  from  := ").append(startLocName).append(";\n");
            ruleSB.append("  to    := ").append(endLocName).append(";\n");
            ruleSB.append("  guard := ").append(condSB).append(";\n");
            ruleSB.append("  action:= ").append(updateSB).append(";\n");
            ruleSB.append("};\n\n");
        }

        private static void exportIntTerm(final TRSTerm t, final StringBuilder sb) {
            if (t.isVariable()) {
                CpxIntTrsToFSTExportWorker.exportIntTerm((TRSVariable) t, sb);
            } else {
                CpxIntTrsToFSTExportWorker.exportIntTerm((TRSFunctionApplication) t, sb);
            }
        }

        private static void exportIntTerm(final TRSVariable v, final StringBuilder sb) {
            sb.append(v);
        }

        private static void exportIntTerm(final TRSFunctionApplication t, final StringBuilder sb) {
            final FunctionSymbol op = t.getRootSymbol();
            final BigInteger i = CpxIntTermHelper.getIntegerValue(t);
            if (i != null) {
                sb.append(op.getName());
                return;
            }
            if (CpxIntTermHelper.fGe.equals(op) || CpxIntTermHelper.fGt.equals(op) || CpxIntTermHelper.fLe.equals(op) || CpxIntTermHelper.fLt.equals(op) || CpxIntTermHelper.fEq.equals(op)) {
                CpxIntTrsToFSTExportWorker.exportIntTerm(t.getArgument(0), sb);
                sb.append(op.getName());
                CpxIntTrsToFSTExportWorker.exportIntTerm(t.getArgument(1), sb);
            } else if (CpxIntTermHelper.fLand.equals(op)) {
                sb.append("(");
                CpxIntTrsToFSTExportWorker.exportIntTerm(t.getArgument(0), sb);
                sb.append(") ").append(op.getName()).append(" (");
                CpxIntTrsToFSTExportWorker.exportIntTerm(t.getArgument(1), sb);
                sb.append(")");
            } else if (CpxIntTermHelper.fAdd.equals(op) || CpxIntTermHelper.fMul.equals(op) || CpxIntTermHelper.fSub.equals(op)) {
                sb.append("(");
                CpxIntTrsToFSTExportWorker.exportIntTerm(t.getArgument(0), sb);
                sb.append(op.getName());
                CpxIntTrsToFSTExportWorker.exportIntTerm(t.getArgument(1), sb);
                sb.append(")");
            } else if (CpxIntTermHelper.fUnaryMinus.equals(op)) {
                sb.append("(0-");
                CpxIntTrsToFSTExportWorker.exportIntTerm(t.getArgument(0), sb);
                sb.append(")");
            } else {
                throw new RuntimeException("Don't know how to export " + op);
            }
        }

        /**
         * Chooses a map m from existing function symbols to an integer. Then turns rules
         * like
         *  f(x1, ..., xn) -> g(t1, ..., tm) | c
         * into a new rule
         *  f(x1, ..., xn, y1 ..., yk) -> g(t1, ..., tm, z1, ..., zl) | c
         * such that n + k = argNum and m + l = argNum holds, where argnum is maximal number of arguments occurring.
         * @param rules some rules
         * @return a pair of the chosen function symbol to integer mapping and the modified rules
         */
        public static
            Pair<Map<FunctionSymbol, Integer>, Set<CpxIntTupleRule>>
            normalizeFs(final Set<CpxIntTupleRule> rules)
        {
            final Map<FunctionSymbol, Integer> pcMap = new LinkedHashMap<>();

            int maxVarNum = 0;
            for (final CpxIntTupleRule rule : rules) {
                final FunctionSymbol lhsSym = rule.getRootSymbol();
                maxVarNum = Math.max(maxVarNum, lhsSym.getArity());
            }

            int pc = 0;
            for (final CpxIntTupleRule rule : rules) {
                final FunctionSymbol lhsSym = rule.getRootSymbol();

                final FunctionSymbol newLhsSym = FunctionSymbol.create(lhsSym.getName(), maxVarNum);
                if (!pcMap.containsKey(newLhsSym)) {
                    pcMap.put(newLhsSym, Integer.valueOf(++pc));
                }

                final TRSTerm rhs = rule.getRights().get(0);
                if (!rhs.isVariable()) {
                    final FunctionSymbol rhsSym = ((TRSFunctionApplication) rhs).getRootSymbol();
                    final FunctionSymbol newRhsSym = FunctionSymbol.create(rhsSym.getName(), maxVarNum);
                    if (!pcMap.containsKey(newRhsSym)) {
                        pcMap.put(newRhsSym, Integer.valueOf(++pc));
                    }
                }

            }

            final Set<CpxIntTupleRule> newRules = new LinkedHashSet<>();
            for (final CpxIntTupleRule rule : rules) {
                try {
                    newRules.addAll(CpxIntTrsToFSTExportWorker.normalizeRule(rule, maxVarNum));
                } catch (final NoValidCpxIntTupleRuleException e) {
                    throw new UnsupportedOperationException();
                }
            }

            return new Pair<>(pcMap, newRules);
        }

        /**
         * @param rule Some rule f(x1, ..., xn) -> COM_1(g(t1, ..., tm)) | c
         * @param argNum number of arguments every term should have after we are done. Should be at
         *  least the max of the arity of all occurring defined symbols
         * @return a new rule f(x1, ..., xn, y1 ..., yk) -> COM_1(g(t1, ..., tm, z1, ..., zl)) | c
         *  such that n + k = argNum and m + l = argNum holds
         * @throws NoValidCpxIntTupleRuleException
         */
        private static LinkedHashSet<CpxIntTupleRule> normalizeRule(final CpxIntTupleRule rule, final int argNum)
            throws NoValidCpxIntTupleRuleException
        {
            final TRSFunctionApplication lhs = rule.getLeft();
            final TRSTerm rhs = rule.getRights().get(0);
            final ImmutableSet<Constraint> constraints = rule.getConstraints();

            final FreshNameGenerator fne = new FreshNameGenerator(FreshNameGenerator.APPEND_NUMBERS);
            fne.lockHasNames(lhs.getVariables());

            final FunctionSymbol lhsFs = lhs.getRootSymbol();
            assert (lhsFs.getArity() <= argNum) : "FS has more arguments than allowed";
            final ArrayList<TRSTerm> newLhsArgs = new ArrayList<>(argNum);
            newLhsArgs.addAll(lhs.getArguments());
            for (int i = newLhsArgs.size(); i < argNum; i++) {
                newLhsArgs.add(TRSTerm.createVariable(fne.getFreshName("y", false)));
            }
            final TRSFunctionApplication newLhs =
                TRSTerm.createFunctionApplication(FunctionSymbol.create(lhsFs.getName(), argNum), newLhsArgs);

            assert (!rhs.isVariable()) : "intTRS with rhs just a variable. Help!";

            final TRSFunctionApplication rhsFA = (TRSFunctionApplication) rhs;
            final FunctionSymbol rhsFs = rhsFA.getRootSymbol();
            assert (rhsFs.getArity() <= argNum) : "FS has more arguments than allowed";
            final ArrayList<TRSTerm> newRhsArgs = new ArrayList<>(argNum);
            newRhsArgs.addAll(rhsFA.getArguments());
            for (int i = newRhsArgs.size(); i < argNum; i++) {
                newRhsArgs.add(TRSTerm.createVariable(fne.getFreshName("z", false)));
            }
            final TRSFunctionApplication newRhs =
                TRSTerm.createFunctionApplication(
                    CpxIntTermHelper.getComSymbol(1),
                    TRSTerm.createFunctionApplication(FunctionSymbol.create(rhsFs.getName(), argNum), newRhsArgs));

            return CpxIntTupleRule.createRules(IGeneralizedRule.create(newLhs, newRhs, null), constraints);
        }
    }
}
