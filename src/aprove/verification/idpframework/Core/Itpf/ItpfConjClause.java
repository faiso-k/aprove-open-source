package aprove.verification.idpframework.Core.Itpf;

import java.util.*;
import java.util.Map.Entry;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.verification.idpframework.Core.*;
import aprove.verification.idpframework.Core.BasicStructures.*;
import aprove.verification.idpframework.Core.BasicStructures.Substitutions.*;
import aprove.verification.idpframework.Core.IDPGraph.*;
import aprove.verification.idpframework.Core.Utility.*;
import aprove.verification.idpframework.Core.Utility.Marking.*;
import aprove.verification.idpframework.Processors.ItpfRules.*;
import aprove.verification.idpframework.Processors.ItpfRules.Execution.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import immutables.*;

/**
 * An ItpfConjClause is a CONJUNCTION of literals.
 * @author Martin Pluecker
 */
public class ItpfConjClause extends ExecutionExportable.ExecutionExportableSkeleton implements Exportable, XmlExportable, IDPExportable,
        Immutable, HasVariables<IVariable<?>>,
        SelfMarkable<ExecutionResult<QuantifiedDisjunction<ItpfConjClause>, ItpfConjClause>, ItpfConjClause>,
        Iterable<Map.Entry<ItpfAtom, Boolean>>, ItpfAtomReplaceData {

    /**
     * @param literals A map from the atom to true iff pos literal, false iff
     * neg literal.
     * @return A new conjunctive clause.
     */
    public static ItpfConjClause create(final ImmutableMap<ItpfAtom, Boolean> literals,
        final ImmutableSet<ITerm<?>> S,
        final ItpfFactory factory) {
        return new ItpfConjClause(literals, S, factory);
    }

    protected final ImmutableMap<ItpfAtom, Boolean> literals;
    protected final ImmutableSet<ITerm<?>> S;

    protected final MarksHandler<ExecutionResult<QuantifiedDisjunction<ItpfConjClause>, ItpfConjClause>, ItpfConjClause, ItpfConjClause> marksHandler;
    protected final int hashCode;

    protected volatile ImmutableSet<IVariable<?>> variables;
    protected volatile ImmutableSet<ImmutablePair<INode, ImmutableTermSubstitution>> nodes;
    protected volatile ImmutableSet<ITerm<?>> terms;
    protected volatile ImmutableSet<IFunctionSymbol<?>> functionSymbols;

    private final ItpfFactory factory;
    private final ExecutionMarksHandler executionMarksHandler;

    /**
     * @param literals A map from the atom to true iff pos literal, false iff
     * neg literal.
     */
    private ItpfConjClause(final ImmutableMap<ItpfAtom, Boolean> literals, final ImmutableSet<ITerm<?>> S,
            final ItpfFactory factory) {

        if (literals.isEmpty()) {
            this.S = ITerm.EMPTY_SET;
        } else {
            if (Globals.useAssertions) {
                assert S.equals(ItpfUtil.expandS(S)) : "expand your S!";
            }
            this.S = S;
        }

        this.literals = literals;
        this.executionMarksHandler = new ExecutionMarksHandler(this);
        this.marksHandler =
            new MarksHandler<ExecutionResult<QuantifiedDisjunction<ItpfConjClause>, ItpfConjClause>, ItpfConjClause, ItpfConjClause>(
                this);
        final int prime = 31;
        assert factory != null;
        this.factory = factory;
        this.hashCode = prime + (literals.hashCode() + prime * this.S.hashCode()) * prime;
    }

    public Collection<IFunctionSymbol<?>> getFunctionSymbols() {
        if (this.functionSymbols == null) {
            synchronized (this) {
                if (this.functionSymbols == null) {
                    final Set<IFunctionSymbol<?>> vars = new LinkedHashSet<IFunctionSymbol<?>>();
                    for (final ItpfAtom atom : this.literals.keySet()) {
                        atom.collectFunctionSymbols(vars);
                    }
                    return this.functionSymbols = ImmutableCreator.create(vars);
                }
            }
        }
        return this.functionSymbols;
    }

    public ItpfConjClause replaceAllFunctionSymbols(final FunctionSymbolReplacement replaceMap) {
        boolean changed = false;
        final LiteralMap newLiterals = new LiteralMap();
        for (final Map.Entry<? extends ItpfAtom, Boolean> literal : this.literals.entrySet()) {
            final ItpfAtom newAtom = literal.getKey().replaceAllFunctionSymbols(replaceMap);
            newLiterals.put(newAtom, literal.getValue());
            if (newLiterals.isUnsatisfiable()) {
                return null;
            }
            changed = changed || newAtom != literal.getKey();
        }

        final Set<ITerm<?>> newS = new LinkedHashSet<ITerm<?>>();
        for (final ITerm<?> s : this.S) {
            newS.add(s.replaceAllFunctionSymbols(replaceMap));
        }

        if (changed) {
            return this.factory.createClause(ImmutableCreator.create(newLiterals), ImmutableCreator.create(newS));
        } else {
            return this;
        }
    }

    public ImmutableMap<ItpfAtom, Boolean> getLiterals() {
        return this.literals;
    }

    @Override
    public ImmutableSet<ITerm<?>> getS() {
        return this.S;
    }

    @Override
    public MarksHandler<ExecutionResult<QuantifiedDisjunction<ItpfConjClause>, ItpfConjClause>, ItpfConjClause, ItpfConjClause> getMarks() {
        return this.marksHandler;
    }

    @Override
    public ExecutionResult<QuantifiedDisjunction<ItpfConjClause>, ItpfConjClause> getSelfMark() {
        return new ExecutionResult<QuantifiedDisjunction<ItpfConjClause>, ItpfConjClause>(
            new QuantifiedDisjunction<ItpfConjClause>(ItpfFactory.EMPTY_QUANTORS, this), ImplicationType.EQUIVALENT,
            ApplicationMode.NoOp, true);
    }

    @Override
    public void addExecutionMark(final ExecutionUid mark) {
        this.executionMarksHandler.addExecutionMark(mark);
    }

    @Override
    public boolean isExecutionMarked(final ExecutionUid mark) {
        return this.executionMarksHandler.isExecutionMarked(mark);
    }

    @Override
    public Set<ExecutionUid> getExecutionMarks() {
        return this.executionMarksHandler.getExecutionMarks();
    }

    @Override
    public void collectExecutionMarks(final Map<ExecutionUid, ExecutionMarkable> executionMarks) {
        this.executionMarksHandler.collectExecutionMarks(executionMarks);
        for (final Map.Entry<ItpfAtom, Boolean> literal : this.literals.entrySet()) {
            literal.getKey().collectExecutionMarks(executionMarks);
        }
    }

    @Override
    public ImmutableSet<IVariable<?>> getVariables() {
        if (this.variables == null) {
            synchronized (this) {
                if (this.variables == null) {
                    final Set<IVariable<?>> vars = new LinkedHashSet<IVariable<?>>();
                    for (final ItpfAtom atom : this.literals.keySet()) {
                        atom.collectVariables(vars);
                    }
                    return this.variables = ImmutableCreator.create(vars);
                }
            }
        }
        return this.variables;
    }

    public ImmutableSet<ImmutablePair<INode, ImmutableTermSubstitution>> getNodes() {
        if (this.nodes == null) {
            synchronized (this) {
                if (this.nodes == null) {
                    final Set<ImmutablePair<INode, ImmutableTermSubstitution>> nds =
                        new LinkedHashSet<ImmutablePair<INode, ImmutableTermSubstitution>>();
                    for (final ItpfAtom atom : this.literals.keySet()) {
                        atom.collectNodes(nds);
                    }
                    return this.nodes = ImmutableCreator.create(nds);
                }
            }
        }
        return this.nodes;
    }

    public ImmutableSet<ITerm<?>> getTerms() {
        if (this.terms == null) {
            synchronized (this) {
                if (this.terms == null) {
                    final Set<ITerm<?>> terms = new LinkedHashSet<ITerm<?>>();
                    for (final ItpfAtom atom : this.literals.keySet()) {
                        atom.collectTerms(terms, false);
                    }
                    return this.terms = ImmutableCreator.create(terms);
                }
            }
        }
        return this.terms;
    }

    public ItpfConjClause applySubstitution(final PolyTermSubstitution sigma) {
        if (sigma.isEmpty()) {
            return this;
        }
        boolean changed = false;
        final LiteralMap newLiterals = new LiteralMap();
        for (final Map.Entry<? extends ItpfAtom, Boolean> literal : this.literals.entrySet()) {
            final ItpfAtom newAtom = literal.getKey().applySubstitution(sigma);
            newLiterals.put(newAtom, literal.getValue());
            if (newAtom.isTrivial() == YNM.YES || newAtom != literal.getKey()) {
                changed = true;
            }
        }

        final Set<ITerm<?>> newS = new LinkedHashSet<ITerm<?>>();
        boolean changedS = false;
        for (final ITerm<?> s : this.S) {
            final ITerm<?> sSigma = s.applySubstitution(sigma);
            newS.add(sSigma);
            changedS = changedS || s != sSigma;
            changed = changed || changedS;
        }

        ImmutableSet<ITerm<?>> newImmutableS;
        if (changedS) {
            newImmutableS = ImmutableCreator.create(ItpfUtil.expandS(newS));
        } else {
            newImmutableS = this.S;
        }

        if (changed) {
            return this.factory.createClause(ImmutableCreator.create(newLiterals), newImmutableS);
        } else {
            return this;
        }
    }

    @Override
    public Iterator<Entry<ItpfAtom, Boolean>> iterator() {
        return this.literals.entrySet().iterator();
    }

    @Override
    public boolean isEmpty() {
        return this.literals.isEmpty();
    }

    @Override
    public int size() {
        return this.literals.size();
    }

    @Override
    public ImmutableCollection<Entry<ItpfAtom, Boolean>> asCollection() {
        return ImmutableCreator.create(this.literals.entrySet());
    }

    @Override
    public boolean isSingleton(final Entry<ItpfAtom, Boolean> content) {
        return this.literals.size() == 1;
    }

    @Override
    public boolean equals(final Object obj) {
        if (this == obj) {
            return true;
        }
        if (obj == null) {
            return false;
        }
        if (!(obj instanceof ItpfConjClause)) {
            return false;
        }
        final ItpfConjClause other = (ItpfConjClause) obj;
        if (other.hashCode != this.hashCode) {
            return false;
        }
        return this.literals.equals(other.literals) && this.S.equals(other.S);
    }

    @Override
    public int hashCode() {
        return this.hashCode;
    }

    @Override
    public void export(final StringBuilder sb,
        final Export_Util eu,
        final VerbosityLevel verbosityLevel,
        final ExecutionStepColorization colors) {
        if (verbosityLevel.compareTo(VerbosityLevel.HIGH) >= 0) {
            sb.append("(");
        }

        if (!this.literals.isEmpty()) {
            for (final Map.Entry<? extends ItpfAtom, Boolean> literal : this.literals.entrySet()) {
                final Integer color = colors.getColor(literal.getKey());
                if (color != null) {
                    final StringBuilder literalSb = new StringBuilder();

                    literal.getKey().export(!literal.getValue(), literalSb, eu, verbosityLevel, colors);

                    sb.append(eu.bold(eu.fontColorCode(literalSb.toString(), color)));
                } else {
                    literal.getKey().export(!literal.getValue(), sb, eu, verbosityLevel, colors);
                }

                sb.append(eu.andSign());
            }
            sb.setLength(sb.length() - eu.andSign().length());
        } else {
            this.factory.createTrue().export(sb, eu, verbosityLevel, colors);
        }

        if (verbosityLevel.compareTo(VerbosityLevel.HIGH) >= 0) {
            sb.append(", ");
            sb.append(eu.set(this.S, Export_Util.NICE_SIMPLE));
            sb.append(")");
        }
    }

    @Override
    public Map<String, String> getXmlAttribs(final XmlExporter xe) {
        return null;
    }

    @Override
    public XmlContentsMap getXmlContents(final XmlExporter xe) {
        final XmlContentsMap objects = new XmlContentsMap();

        if (!this.literals.isEmpty()) {
            for (final Map.Entry<? extends ItpfAtom, Boolean> literal : this.literals.entrySet()) {
                if (literal.getValue()) {
                    objects.add(literal.getKey());
                } else {
                    objects.add(new ItpfNegationWrapper(literal.getKey()));
                }
            }
        } else {
            objects.add(this.factory.createTrue());
        }

        return objects;
    }
}
