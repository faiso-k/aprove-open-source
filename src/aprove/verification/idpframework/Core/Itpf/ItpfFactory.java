package aprove.verification.idpframework.Core.Itpf;

import java.util.*;

import aprove.verification.idpframework.Algorithms.UsableRules.*;
import aprove.verification.idpframework.Core.BasicStructures.*;
import aprove.verification.idpframework.Core.BasicStructures.Substitutions.*;
import aprove.verification.idpframework.Core.IDPGraph.*;
import aprove.verification.idpframework.Core.Itpf.ItpfPolyAtom.*;
import aprove.verification.idpframework.Core.SemiRings.*;
import aprove.verification.idpframework.Core.Utility.*;
import aprove.verification.idpframework.Core.Utility.Marking.*;
import aprove.verification.idpframework.Polynomials.*;
import aprove.verification.idpframework.Polynomials.Interpretation.*;
import immutables.*;

/**
 * @author Martin Pluecker
 */
public interface ItpfFactory {

    PolyFactory getPolyFactory();

    public static ImmutableList<ItpfQuantor> EMPTY_QUANTORS =
        ImmutableCreator.create(Collections.<ItpfQuantor> emptyList());

    Itpf createQuantorFree(Itpf precondition);

    Itpf createOr(Collection<? extends QuantifiedDisjunction<ItpfConjClause>> ors, FreshVarGenerator freshNames);

    Itpf createAnd(Collection<? extends QuantifiedDisjunction<ItpfConjClause>> ands, FreshVarGenerator freshNames);

    Itpf createOr(FreshVarGenerator freshNames, final QuantifiedDisjunction<ItpfConjClause>... formulas);

    Itpf createAnd(FreshVarGenerator freshNames, final QuantifiedDisjunction<ItpfConjClause>... formulas);

    Itpf createOr(Collection<? extends QuantifiedDisjunction<ItpfConjClause>> ors);

    Itpf createAnd(Collection<? extends QuantifiedDisjunction<ItpfConjClause>> ands);

    Itpf createOr(final QuantifiedDisjunction<ItpfConjClause>... formulas);

    Itpf createAnd(final QuantifiedDisjunction<ItpfConjClause>... formulas);

    Itpf create(ItpfAtom atom, boolean positive, ImmutableSet<ITerm<?>> s);

    Itpf create(ImmutableList<ItpfQuantor> quantification, ItpfAtom atom, boolean positive, ImmutableSet<ITerm<?>> s);

    Itpf create(Map<? extends IVariable<?>, Boolean> quantifiedVariables,
        ItpfAtom atom,
        Boolean positive,
        ImmutableSet<ITerm<?>> s);

    Itpf create(Map<? extends IVariable<?>, Boolean> quantifiedVariables,
        ImmutableSet<ItpfConjClause> clauses);

    Itpf create (QuantifiedDisjunction<ItpfConjClause> formula);

    Itpf createTrue();

    Itpf createFalse();

    ItpfLogVar createLogVar(String string);

    public ItpfConjClause createClause(ItpfAtom atom,
        Boolean positive,
        ImmutableSet<ITerm<?>> s);

    public ItpfConjClause createEmptyClause();

    public ItpfConjClause createClause(final ImmutableMap<ItpfAtom, Boolean> literals,
        ImmutableSet<ITerm<?>> s);

    ItpfConjClause createClause(Collection<? extends ItpfAtom> atoms, boolean positive, ImmutableSet<ITerm<?>> s);

    ItpfQuantor createQuantor(boolean universalQuantor, IVariable<?> variable);

    Itpf create(ImmutableList<ItpfQuantor> quantors,
        ImmutableSet<ItpfConjClause> clauses);

    Itpf create(ImmutableList<ItpfQuantor> quantors, ItpfConjClause clause);

    Itpf create(ItpfConjClause clause);

    Itpf create(ImmutableList<ItpfQuantor> quantors, ItpfConjClause...clauses);
    Itpf create(ItpfConjClause...clauses);

    Itpf create(ImmutableSet<ItpfConjClause> clauses);

    ArrayList<ItpfQuantor> createQuantors(final Collection<? extends IVariable<?>> quantVars, final Set<IVariable<?>> formularVars,
        final boolean univarsalQuantor);

    /**
     * Qunators are added in front of the quantor chain
     * @param quantVars
     * @param formula
     * @return
     */
    Itpf quantifyExist(final Collection<? extends IVariable<?>> quantVars,
        final Itpf formula);

    Itpf quantifyUniversal(final Collection<? extends IVariable<?>> quantVars,
        final Itpf formula);

    <C extends SemiRing<C>> ItpfPolyAtom<C> createPoly(Polynomial<C> poly,
        ConstraintType ct,
        PolyInterpretation<C> interpretation);

    <C extends SemiRing<C>> ItpfBoolPolyVar<C> createBoolPolyVar(IVariable<C> polyVar,
        PolyInterpretation<C> interpretation);

    ItpfEdgeOrientation createEdgeOrientation(IEdge edge,
        Immutable metaData,
        RelDependency relDependency,
        IActiveCondition activeCondition,
        ImmutableTermSubstitution substitutionFrom,
        ImmutableTermSubstitution substitutionTo,
        EdgeOrientationRelation relation);

    ItpfItp createItp(ITerm<?> leftTerm,
        RelDependency kLeft,
        IActiveContext fromActiveContext,
        ItpRelation relation,
        ITerm<?> rightTerm,
        RelDependency kRight,
        IActiveContext toActiveContext);

    ItpfNodeUra createNodeUra(IUsableRulesEstimation eu,
        RelDependency k,
        INode node,
        ImmutableTermSubstitution substitution,
        ItpRelation rel);

    ItpfEdgeUra createEdgeUra(IUsableRulesEstimation usableRulesEstimation,
        RelDependency relDependency,
        IActiveCondition activeCondition,
        IEdge edge,
        ImmutableTermSubstitution newSubstitution,
        ItpRelation relation);

    ItpfTermUra createTermUra(IUsableRulesEstimation eu,
        RelDependency k,
        final IActiveCondition activeCondition,
        ITerm<?> term,
        ItpRelation rel);

    ItpfImplication createImplication(Itpf newPrecondition, Itpf newConclusion);

    public abstract class ItpfFactorySkeleton implements ItpfFactory {

        protected final ItpfTrue TRUE;
        protected final ItpfFalse FALSE;
        protected final ItpfConjClause EMPTY_CLAUSE;

        protected ItpfFactorySkeleton() {
            this.EMPTY_CLAUSE =
                ItpfConjClause.create(
                    ImmutableCreator.create(Collections.<ItpfAtom, Boolean> emptyMap()),
                    ITerm.EMPTY_SET, this);
            this.TRUE = ItpfTrue.create(this);
            this.FALSE = ItpfFalse.create();
        }

        @Override
        public Itpf createQuantorFree(final Itpf formula) {
            return this.create(formula.getClauses());
        }

        @Override
        public Itpf create(final QuantifiedDisjunction<ItpfConjClause> formula) {
            if (formula instanceof Itpf) {
                return (Itpf) formula;
            } else {
                final ImmutableCollection<ItpfConjClause> collection = formula.asCollection();
                ImmutableSet<ItpfConjClause> setCollection;
                if (collection instanceof Set) {
                    setCollection = (ImmutableSet<ItpfConjClause>) collection;
                } else {
                    setCollection = ImmutableCreator.create(new LinkedHashSet<ItpfConjClause>(collection));
                }
                return this.create(formula.getQuantification(), setCollection);
            }
        }

        @Override
        public Itpf createAnd(final FreshVarGenerator freshNames, final QuantifiedDisjunction<ItpfConjClause>... formulas) {
            return this.createAnd(Arrays.asList(formulas), freshNames);
        }

        @Override
        public Itpf createAnd(final QuantifiedDisjunction<ItpfConjClause>... formulas) {
            return this.createAnd(Arrays.asList(formulas), null);
        }

        @Override
        public Itpf createAnd(final Collection<? extends QuantifiedDisjunction<ItpfConjClause>> formulas) {
            return this.createAnd(formulas, null);
        }

        @Override
        public Itpf createOr(final FreshVarGenerator freshNames, final QuantifiedDisjunction<ItpfConjClause>... formulas) {
            return this.createOr(Arrays.asList(formulas), freshNames);
        }

        @Override
        public Itpf createOr(final Collection<? extends QuantifiedDisjunction<ItpfConjClause>> formulas) {
            return this.createOr(formulas, null);
        }

        @Override
        public Itpf createOr(final QuantifiedDisjunction<ItpfConjClause>... formulas) {
            return this.createOr(Arrays.asList(formulas), null);
        }

        protected Itpf or(Collection<? extends QuantifiedDisjunction<ItpfConjClause>> formulas,
            final PolyFactory polyFactory, final FreshVarGenerator freshNames) {

            if (formulas.size() == 1) {
                return this.create(formulas.iterator().next());
            }

            formulas = new LinkedHashSet<QuantifiedDisjunction<ItpfConjClause>>(formulas);
            formulas.remove(this.FALSE);

            if (formulas.size() == 1) {
                return this.create(formulas.iterator().next());
            }

            if (formulas.contains(this.TRUE)) {
                return this.TRUE;
            }

            final Set<IVariable<?>> usedBoundVariables = new HashSet<IVariable<?>>();

            final Set<ItpfConjClause> clauses =
                new LinkedHashSet<ItpfConjClause>();
            final List<ItpfQuantor> quantors = new ArrayList<ItpfQuantor>();
            // rename bound variables
            for (final QuantifiedDisjunction<ItpfConjClause> rawFormula : formulas) {
                final Map<IVariable<?>, IVariable<?>> varRenaming =
                    new HashMap<IVariable<?>, IVariable<?>>();

                Set<IVariable<?>> boundVars;
                if (rawFormula instanceof Itpf) {
                    boundVars = ((Itpf) rawFormula).getBoundVariables();
                } else {
                    boundVars = ItpfUtil.collectBoundVariables(rawFormula.getQuantification());
                }

                for (final IVariable<?> var : boundVars) {
                    if (freshNames != null) {
                        freshNames.lockName(var.getName());
                    }
                    if (!usedBoundVariables.add(var)) {
                        if (freshNames == null) {
                            throw new IllegalArgumentException("need fresh names generator for quantified formulas");
                        }
                        varRenaming.put(var, freshNames.getFreshVariable(var, false));
                    }
                }

                if (!varRenaming.isEmpty()) {
                    final VarRenaming renaming =
                        VarRenaming.create(
                            ImmutableCreator.create(varRenaming), true,
                            polyFactory);

                    for (final ItpfConjClause clause : rawFormula.asCollection()) {
                        clauses.add(clause.applySubstitution(renaming));
                    }

                    for (final ItpfQuantor quantor : rawFormula.getQuantification()) {
                        final IVariable<?> renamed =
                            varRenaming.get(quantor.getVariable());
                        if (renamed != null) {
                            quantors.add(this.createQuantor(
                                quantor.isUniversalQuantor(), renamed));
                        } else {
                            quantors.add(quantor);
                        }
                    }
                } else {
                    clauses.addAll(rawFormula.asCollection());
                    quantors.addAll(rawFormula.getQuantification());
                }
            }
            return this.create(ImmutableCreator.create(quantors),
                ImmutableCreator.create(clauses));
        }

        protected Itpf and(Collection<? extends QuantifiedDisjunction<ItpfConjClause>> formulas,
            final PolyFactory polyFactory, final FreshVarGenerator freshNames) {

            if (formulas.size() == 1) {
                return this.create(formulas.iterator().next());
            }

            formulas = new LinkedHashSet<QuantifiedDisjunction<ItpfConjClause>>(formulas);
            formulas.remove(this.TRUE);

            if (formulas.size() == 1) {
                return this.create(formulas.iterator().next());
            }

            if (formulas.contains(this.FALSE)) {
                return this.FALSE;
            }

            final Set<IVariable<?>> usedBoundVariables = new HashSet<IVariable<?>>();

            final List<ItpfQuantor> quantors = new ArrayList<ItpfQuantor>();
            // rename bound variables
            Set<ItpfConjClause> clauses = new LinkedHashSet<ItpfConjClause>(1);
            clauses.add(this.createEmptyClause());

            for (final QuantifiedDisjunction<ItpfConjClause> rawFormula : formulas) {
                final Map<IVariable<?>, IVariable<?>> varRenaming =
                    new HashMap<IVariable<?>, IVariable<?>>();

                Set<IVariable<?>> boundVars;
                if (rawFormula instanceof Itpf) {
                    boundVars = ((Itpf) rawFormula).getBoundVariables();
                } else {
                    boundVars = ItpfUtil.collectBoundVariables(rawFormula.getQuantification());
                }

                for (final IVariable<?> var : boundVars) {
                    if (freshNames != null) {
                        freshNames.lockName(var.getName());
                    }
                    if (!usedBoundVariables.add(var)) {
                        if (freshNames == null) {
                            throw new IllegalArgumentException("need fresh names generator for quantified formulas");
                        }

                        varRenaming.put(var, freshNames.getFreshVariable(var, false));
                    }
                }

                Collection<ItpfConjClause> renamedClauses;
                if (!varRenaming.isEmpty()) {
                    final VarRenaming renaming =
                        VarRenaming.create(
                            ImmutableCreator.create(varRenaming), true,
                            polyFactory);
                    renamedClauses = new LinkedHashSet<ItpfConjClause>();
                    for (final ItpfConjClause clause : rawFormula.asCollection()) {
                        renamedClauses.add(clause.applySubstitution(renaming));
                    }
                    for (final ItpfQuantor quantor : rawFormula.getQuantification()) {
                        final IVariable<?> renamed =
                            varRenaming.get(quantor.getVariable());
                        if (renamed != null) {
                            quantors.add(this.createQuantor(
                                quantor.isUniversalQuantor(), renamed));
                        } else {
                            quantors.add(quantor);
                        }
                    }
                } else {
                    renamedClauses = rawFormula.asCollection();
                    quantors.addAll(rawFormula.getQuantification());
                }

                final Set<ItpfConjClause> newClauses =
                    new LinkedHashSet<ItpfConjClause>(clauses.size()
                        * renamedClauses.size());

                for (final ItpfConjClause clause : clauses) {
                    renamed: for (final ItpfConjClause renamed : renamedClauses) {
                        final LiteralMap literals =
                            new LiteralMap(clause.getLiterals());
                        for (final Map.Entry<? extends ItpfAtom, Boolean> renamedLiteral : renamed.getLiterals().entrySet()) {
                            final Boolean value =
                                literals.put(renamedLiteral.getKey(),
                                    renamedLiteral.getValue());
                            if (literals.isUnsatisfiable()) {
                                continue renamed;
                            }
                        }

                        final LinkedHashSet<ITerm<?>> combinedS =
                            new LinkedHashSet<ITerm<?>>(clause.getS());
                        combinedS.addAll(renamed.getS());

                        newClauses.add(this.createClause(
                            ImmutableCreator.create(literals),
                            ImmutableCreator.create(combinedS)));
                    }
                }
                clauses = newClauses;
            }

            return this.create(ImmutableCreator.create(quantors),
                ImmutableCreator.create(clauses));
        }

        @Override
        public Itpf quantifyExist(final Collection<? extends IVariable<?>> quantVars,
            final Itpf formula) {
            if (quantVars.isEmpty()) {
                return formula;
            }

            final ArrayList<ItpfQuantor> quantors =
                this.createQuantors(quantVars, formula.getFreeVariables(), false);

            quantors.addAll(formula.getQuantification());

            return this.create(ImmutableCreator.create(quantors),
                formula.getClauses());
        }

        @Override
        public Itpf quantifyUniversal(final Collection<? extends IVariable<?>> quantVars,
            final Itpf formula) {
            if (quantVars.isEmpty()) {
                return formula;
            }

            final ArrayList<ItpfQuantor> quantors =
                this.createQuantors(quantVars, formula.getFreeVariables(), true);

            quantors.addAll(formula.getQuantification());
            return this.create(ImmutableCreator.create(quantors),
                formula.getClauses());
        }

        @Override
        public ArrayList<ItpfQuantor> createQuantors(final Collection<? extends IVariable<?>> quantVars, final Set<IVariable<?>> formularVars,
            final boolean univarsalQuantor) {
            final ArrayList<ItpfQuantor> quantors =
                new ArrayList<ItpfQuantor>(quantVars.size());

            for (final IVariable<?> var : quantVars) {
                if (formularVars.contains(var)) {
                    quantors.add(this.createQuantor(univarsalQuantor, var));
                }
            }
            return quantors;
        }

        @Override
        public final Itpf createFalse() {
            return this.FALSE;
        }

        @Override
        public final Itpf createTrue() {
            return this.TRUE;
        }

        @Override
        public ItpfConjClause createEmptyClause() {
            return this.EMPTY_CLAUSE;
        }

    }

}
