package aprove.verification.idpframework.Core.Itpf;

import java.util.*;
import java.util.concurrent.*;

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
public class SharingItpfFactory extends ItpfFactory.ItpfFactorySkeleton {

    private final ConcurrentMap<Itpf, Itpf> formulas =
        new ConcurrentHashMap<Itpf, Itpf>();

    private final ConcurrentMap<ItpfConjClause, ItpfConjClause> clauses =
        new ConcurrentHashMap<ItpfConjClause, ItpfConjClause>();

    private final ConcurrentMap<ItpfLogVar, ItpfLogVar> logVars =
        new ConcurrentHashMap<ItpfLogVar, ItpfLogVar>();

    private final ConcurrentMap<ItpfPolyAtom<?>, ItpfPolyAtom<?>> polys =
        new ConcurrentHashMap<ItpfPolyAtom<?>, ItpfPolyAtom<?>>();

    private final ConcurrentMap<ItpfBoolPolyVar<?>, ItpfBoolPolyVar<?>> boolPolyVars =
        new ConcurrentHashMap<ItpfBoolPolyVar<?>, ItpfBoolPolyVar<?>>();

    private final ConcurrentMap<ItpfEdgeOrientation, ItpfEdgeOrientation> edgeOrientation =
        new ConcurrentHashMap<ItpfEdgeOrientation, ItpfEdgeOrientation>();

    private final ConcurrentMap<ItpfItp, ItpfItp> itps =
        new ConcurrentHashMap<ItpfItp, ItpfItp>();

    private final ConcurrentMap<ItpfNodeUra, ItpfNodeUra> nodeUras =
        new ConcurrentHashMap<ItpfNodeUra, ItpfNodeUra>();

    private final ConcurrentMap<ItpfEdgeUra, ItpfEdgeUra> edgeUras =
        new ConcurrentHashMap<ItpfEdgeUra, ItpfEdgeUra>();

    private final ConcurrentMap<ItpfTermUra, ItpfTermUra> termUras =
        new ConcurrentHashMap<ItpfTermUra, ItpfTermUra>();

    private final ConcurrentMap<ItpfImplication, ItpfImplication> implications =
        new ConcurrentHashMap<ItpfImplication, ItpfImplication>();

    private final ConcurrentMap<ItpfQuantor, ItpfQuantor> quantors =
        new ConcurrentHashMap<ItpfQuantor, ItpfQuantor>();

    private final PolyFactory polyFactory;

    public SharingItpfFactory(final PolyFactory polyFactory) {
        this.polyFactory = polyFactory;
        this.formulas.put(this.TRUE, this.TRUE);
        this.formulas.put(this.FALSE, this.FALSE);
        this.clauses.put(this.EMPTY_CLAUSE, this.EMPTY_CLAUSE);
    }

    @Override
    public PolyFactory getPolyFactory() {
        return this.polyFactory;
    }

    @Override
    public ItpfConjClause createClause(final ImmutableMap<ItpfAtom, Boolean> literals,
        final ImmutableSet<ITerm<?>> s) {
        return this.shareObject(this.clauses, ItpfConjClause.create(literals, s, this));
    }

    @Override
    public ItpfConjClause createClause(final ItpfAtom atom,
        final Boolean positive,
        final ImmutableSet<ITerm<?>> s) {
        final LiteralMap literals = new LiteralMap();
        literals.put(atom, positive);
        return this.createClause(ImmutableCreator.create(literals), s);
    }

    @Override
    public ItpfConjClause createClause(final Collection<? extends ItpfAtom> atoms,
        final boolean positive,
        final ImmutableSet<ITerm<?>> s) {
        final LiteralMap literals = new LiteralMap();
        literals.putAll(atoms, positive);
        return this.createClause(ImmutableCreator.create(literals), s);
    }

    @Override
    public Itpf create(final ItpfAtom atom,
        final boolean positive,
        final ImmutableSet<ITerm<?>> s) {
        return this.create(this.createClause(atom, positive, s));
    }

    @Override
    public Itpf create(final ImmutableList<ItpfQuantor> quantification,
        final ItpfAtom atom,
        final boolean positive,
        final ImmutableSet<ITerm<?>> s) {
        return this.create(quantification, this.createClause(atom, positive, s));
    }

    @Override
    public Itpf create(final ItpfConjClause clause) {
        return this.create(ImmutableCreator.create(Collections.singleton(clause)));
    }

    @Override
    public Itpf create(final ImmutableList<ItpfQuantor> quantification, final ItpfConjClause... clauses) {
        return this.create(quantification, ImmutableCreator.create(new LinkedHashSet<ItpfConjClause>(
            Arrays.asList(clauses))));
    }

    @Override
    public Itpf create(final ItpfConjClause... clauses) {
        return this.create(ImmutableCreator.create(new LinkedHashSet<ItpfConjClause>(
            Arrays.asList(clauses))));
    }

    public Itpf create(final Set<ItpfConjClause> clauses) {
        return this.create(
            ImmutableCreator.create(Collections.<ItpfQuantor> emptyList()),
            ImmutableCreator.create(clauses));
    }

    @Override
    public Itpf create(final ImmutableSet<ItpfConjClause> clauses) {
        return this.create(
            ImmutableCreator.create(Collections.<ItpfQuantor> emptyList()),
            clauses);
    }

    @Override
    public Itpf create(final ImmutableList<ItpfQuantor> quantors,
        final ItpfConjClause clause) {
        return this.create(quantors, ImmutableCreator.create(Collections.singleton(clause)));
    }


    @Override
    public Itpf create(final ImmutableList<ItpfQuantor> quantors,
        final ImmutableSet<ItpfConjClause> clauses) {
        return this.shareObject(this.formulas, new ItpfFormula(quantors, clauses, this));
    }

    @Override
    public Itpf createAnd(final Collection<? extends QuantifiedDisjunction<ItpfConjClause>> formulas, final FreshVarGenerator freshNames) {
        return this.shareObject(this.formulas, this.and(formulas, this.polyFactory, freshNames));
    }

    @Override
    public Itpf createOr(final Collection<? extends QuantifiedDisjunction<ItpfConjClause>> formulas, final FreshVarGenerator freshNames) {
        return this.shareObject(this.formulas, this.or(formulas, this.polyFactory, freshNames));
    }

    @Override
    public ItpfLogVar createLogVar(final String name) {
        return this.shareObject(this.logVars, ItpfLogVar.create(name));
    }

    @SuppressWarnings("unchecked")
    @Override
    public <C extends SemiRing<C>> ItpfPolyAtom<C> createPoly(final Polynomial<C> poly,
        final ConstraintType ct,
        final PolyInterpretation<C> interpretation) {
        return (ItpfPolyAtom<C>) this.shareObject(this.polys, ItpfPolyAtom.create(poly, ct, interpretation));
    }

    @SuppressWarnings("unchecked")
    @Override
    public <C extends SemiRing<C>> ItpfBoolPolyVar<C> createBoolPolyVar(final IVariable<C> polyVar,
        final PolyInterpretation<C> interpretation) {
        return (ItpfBoolPolyVar<C>) this.shareObject(this.boolPolyVars, ItpfBoolPolyVar.create(polyVar, interpretation,
            this));
    }

    @Override
    public ItpfEdgeOrientation createEdgeOrientation(final IEdge edge,
        final Immutable metaData,
        final RelDependency relDependency,
        final IActiveCondition activeCondition,
        final ImmutableTermSubstitution substitutionFrom,
        final ImmutableTermSubstitution substitutionTo,
        final EdgeOrientationRelation relation) {
        return this.shareObject(this.edgeOrientation, ItpfEdgeOrientation.create(edge, metaData,
            relDependency, activeCondition, substitutionFrom, substitutionTo, relation, this));
    }

    @Override
    public Itpf create(final Map<? extends IVariable<?>, Boolean> quantifiedVariables,
        final ItpfAtom atom,
        final Boolean positive,
        final ImmutableSet<ITerm<?>> s) {
        return this.create(quantifiedVariables,
            ImmutableCreator.create(Collections.singleton(this.createClause(atom,
                positive, s))));

    }

    @Override
    public Itpf create(final Map<? extends IVariable<?>, Boolean> quantifiedVariables,
        final ImmutableSet<ItpfConjClause> clauses) {
        final List<ItpfQuantor> quantors =
            new ArrayList<ItpfQuantor>(quantifiedVariables.size());

        for (final Map.Entry<? extends IVariable<?>, Boolean> quantifiedVariable : quantifiedVariables.entrySet()) {
            quantors.add(this.createQuantor(quantifiedVariable.getValue(),
                quantifiedVariable.getKey()));
        }

        return this.create(ImmutableCreator.create(quantors), clauses);
    }

    @Override
    public ItpfQuantor createQuantor(final boolean universalQuantor,
        final IVariable<?> variable) {
        return this.shareObject(this.quantors, ItpfQuantor.create(universalQuantor, variable, this));
    }

    @Override
    public ItpfItp createItp(final ITerm<?> leftTerm,
        final RelDependency kLeft,
        final IActiveContext contextL,
        final ItpRelation relation,
        final ITerm<?> rightTerm,
        final RelDependency kRight,
        final IActiveContext contextR) {
        return this.shareObject(this.itps, ItpfItp.create(leftTerm, kLeft, contextL, relation,
            rightTerm, kRight, contextR, this));
    }

    @Override
    public ItpfNodeUra createNodeUra(final IUsableRulesEstimation eu,
        final RelDependency k,
        final INode node,
        final ImmutableTermSubstitution substitution,
        final ItpRelation rel) {
        return this.shareObject(this.nodeUras, ItpfNodeUra.create(eu, k, node, substitution, rel, this));
    }

    @Override
    public ItpfEdgeUra createEdgeUra(final IUsableRulesEstimation eu,
        final RelDependency k,
        final IActiveCondition activeCondition,
        final IEdge edge,
        final ImmutableTermSubstitution substitution,
        final ItpRelation rel) {
        return this.shareObject(this.edgeUras, ItpfEdgeUra.create(eu, k, activeCondition, edge, substitution, rel, this));
    }

    @Override
    public ItpfTermUra createTermUra(final IUsableRulesEstimation eu,
        final RelDependency k,
        final IActiveCondition activeCondition,
        final ITerm<?> term,
        final ItpRelation rel) {
        return this.shareObject(this.termUras, ItpfTermUra.create(eu, k, activeCondition, term, rel, this));
    }

    @Override
    public ItpfImplication createImplication(final Itpf precondition,
        final Itpf conclusion) {
        return this.shareObject(this.implications, ItpfImplication.create(precondition,
            conclusion, this));
    }

    private <O> O shareObject(final ConcurrentMap<O, O> pool, final O object) {
        return ConcurrentUtil.addToCache(pool, object, object);
    }

}
