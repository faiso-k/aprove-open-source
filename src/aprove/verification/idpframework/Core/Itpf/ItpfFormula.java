package aprove.verification.idpframework.Core.Itpf;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.idpframework.Core.BasicStructures.*;
import aprove.verification.idpframework.Core.BasicStructures.Substitutions.*;
import aprove.verification.idpframework.Core.IDPGraph.*;
import aprove.verification.idpframework.Core.Utility.*;
import aprove.verification.idpframework.Core.Utility.Marking.*;
import aprove.verification.idpframework.Processors.ItpfRules.Execution.*;
import aprove.verification.oldframework.Utility.*;
import immutables.*;

/**
 * @author Martin Pluecker
 */
public class ItpfFormula extends Itpf implements XmlExportable {

    private final ImmutableSet<ItpfConjClause> clauses;
    private final ItpfFactory factory;

    private volatile ImmutableSet<IVariable<?>> boundVariables;
    private volatile ImmutableSet<IVariable<?>> freeVariables;
    private volatile ImmutableSet<ImmutablePair<INode, ImmutableTermSubstitution>> nodes;
    private volatile ImmutableSet<IVariable<?>> variables;
    private volatile ImmutableSet<ITerm<?>> terms;
    private volatile ImmutableSet<ITerm<?>> nonVariableTerms;
    private volatile ImmutableSet<IFunctionSymbol<?>> functionSymbols;

    protected ItpfFormula(final ImmutableList<ItpfQuantor> quantification, final ImmutableSet<ItpfConjClause> clauses,
            final ItpfFactory factory) {
        super(quantification, clauses);
        this.clauses = clauses;
        this.factory = factory;
    }

    @Override
    protected Itpf applySubstitutionNoCheck(final PolyTermSubstitution sigma, final boolean substituteBoundVariables) {
        boolean changed = false;
        final LinkedHashSet<ItpfConjClause> newClauses = new LinkedHashSet<ItpfConjClause>();
        for (final ItpfConjClause clause : this.clauses) {
            final ItpfConjClause newClause = clause.applySubstitution(sigma);
            newClauses.add(newClause);
            if (newClause != clause) {
                changed = true;
            }
        }

        ImmutableList<ItpfQuantor> newquantification;
        if (substituteBoundVariables) {
            newquantification = this.getSubstitutedquantification(sigma);
            changed = changed || newquantification != this.quantification;
        } else {
            newquantification = this.quantification;
        }

        if (changed) {
            return this.factory.create(newquantification, ImmutableCreator.create(newClauses));
        } else {
            return this;
        }
    }

    private ImmutableList<ItpfQuantor> getSubstitutedquantification(final PolyTermSubstitution sigma) {
        boolean changedquantification = false;
        final List<ItpfQuantor> substitutedquantification = new ArrayList<ItpfQuantor>(this.quantification.size());

        for (final ItpfQuantor quantor : this.quantification) {
            final ITerm<?> substitution = sigma.substituteTerm(quantor.getVariable());
            if (!substitution.equals(quantor.getVariable())) {
                if (!substitution.isVariable()) {
                    throw new UnsupportedOperationException("quantor is substituted by term");
                }
                substitutedquantification.add(this.factory.createQuantor(quantor.isUniversalQuantor(),
                    (IVariable<?>) substitution));
                changedquantification = true;
            } else {
                substitutedquantification.add(quantor);
            }
        }

        if (changedquantification) {
            return ImmutableCreator.create(substitutedquantification);
        } else {
            return this.quantification;
        }
    }

    @Override
    public void export(final StringBuilder sb,
        final Export_Util eu,
        final VerbosityLevel verbosityLevel,
        final ExecutionStepColorization colors) {
        //        exportToXml(sb, eu);
        for (final ItpfQuantor quantor : this.quantification) {
            quantor.export(sb, eu, verbosityLevel);
            sb.append(" ");
        }
        if (this.clauses.isEmpty()) {
            this.factory.createFalse().export(sb, eu, verbosityLevel, colors);
        } else {
            final Iterator<ItpfConjClause> iter = this.clauses.iterator();
            while (iter.hasNext()) {
                iter.next().export(sb, eu, verbosityLevel, colors);
                if (iter.hasNext()) {
                    sb.append(" ");
                    sb.append(eu.orSign());
                    sb.append(" ");
                }
            }
        }
    }

    public void exportToXml(final StringBuilder sb, final Export_Util eu) {
        try {
            final XmlExporter exporter = XmlExporter.create(this);
            exporter.export(sb);
        } catch (final Exception e) {
            e.printStackTrace();
        }

    }

    @Override
    public XmlContentsMap getXmlContents(final XmlExporter xe) {
        final XmlContentsMap objects = new XmlContentsMap();

        for (final ItpfQuantor quantor : this.quantification) {
            objects.add(quantor);
        }

        for (final ItpfConjClause clause : this.clauses) {
            objects.add(clause);
        }

        return objects;
    }

    @Override
    public Map<String, String> getXmlAttribs(final XmlExporter xe) {
        return null;
    }

    @Override
    public ImmutableSet<IVariable<?>> getBoundVariables() {
        if (this.boundVariables == null) {
            synchronized (this) {
                if (this.boundVariables == null) {
                    return this.boundVariables = ImmutableCreator.create(ItpfUtil.collectBoundVariables(this.quantification));
                }
            }
        }
        return this.boundVariables;
    }

    @Override
    public ImmutableSet<ItpfConjClause> getClauses() {
        return this.clauses;
    }

    @Override
    public ImmutableSet<IVariable<?>> getFreeVariables() {
        if (this.freeVariables == null) {
            synchronized (this) {
                if (this.freeVariables == null) {
                    final Set<IVariable<?>> free = new LinkedHashSet<IVariable<?>>(this.getVariables());
                    free.removeAll(this.getBoundVariables());
                    return this.freeVariables = ImmutableCreator.create(free);
                }
            }
        }
        return this.freeVariables;
    }

    @Override
    public ImmutableSet<IVariable<?>> getVariables() {
        if (this.variables == null) {
            synchronized (this) {
                if (this.variables == null) {
                    final Set<IVariable<?>> vars = new LinkedHashSet<IVariable<?>>();
                    for (final ItpfConjClause clause : this.clauses) {
                        vars.addAll(clause.getVariables());
                    }
                    return this.variables = ImmutableCreator.create(vars);
                }
            }
        }
        return this.variables;
    }

    @Override
    public ImmutableSet<ImmutablePair<INode, ImmutableTermSubstitution>> getNodes() {
        if (this.nodes == null) {
            synchronized (this) {
                if (this.nodes == null) {
                    final Set<ImmutablePair<INode, ImmutableTermSubstitution>> nds =
                        new LinkedHashSet<ImmutablePair<INode, ImmutableTermSubstitution>>();
                    for (final ItpfConjClause clause : this.clauses) {
                        nds.addAll(clause.getNodes());
                    }
                    return this.nodes = ImmutableCreator.create(nds);
                }
            }
        }
        return this.nodes;
    }

    @Override
    public ImmutableSet<ITerm<?>> getTerms(final boolean dropVars) {
        if (this.terms == null) {
            synchronized (this) {
                this.collectTerms();
            }
        }
        if (dropVars) {
            return this.nonVariableTerms;
        } else {
            return this.terms;
        }
    }

    @Override
    public void collectExecutionMarks(final Map<ExecutionUid, ExecutionMarkable> executionMarks) {
        this.executionMarksHandler.collectExecutionMarks(executionMarks);
        for (final ItpfConjClause clause : this.clauses) {
            clause.collectExecutionMarks(executionMarks);
        }
    }

    private void collectTerms() {
        final Set<ITerm<?>> terms = new LinkedHashSet<ITerm<?>>();
        for (final ItpfConjClause clause : this.clauses) {
            terms.addAll(clause.getTerms());
        }
        this.terms = ImmutableCreator.create(terms);

        final Set<ITerm<?>> nonVariableTerms = new LinkedHashSet<ITerm<?>>();
        for (final ITerm<?> term : terms) {
            if (!term.isVariable()) {
                nonVariableTerms.add(term);
            }
        }
        this.nonVariableTerms = ImmutableCreator.create(nonVariableTerms);
    }

    @Override
    public ImmutableSet<IFunctionSymbol<?>> getFunctionSymbols() {
        if (this.functionSymbols == null) {
            synchronized (this) {
                if (this.functionSymbols == null) {
                    final Set<IFunctionSymbol<?>> fss = new LinkedHashSet<>();
                    for (final ItpfConjClause clause : this.clauses) {
                        fss.addAll(clause.getFunctionSymbols());
                    }
                    return this.functionSymbols = ImmutableCreator.create(fss);
                }
            }
        }
        return this.functionSymbols;
    }

    @Override
    public Itpf replaceAllFunctionSymbols(final FunctionSymbolReplacement replaceMap) {
        boolean changed = false;
        final Set<ItpfConjClause> newClauses = new LinkedHashSet<ItpfConjClause>();
        for (final ItpfConjClause clause : this.clauses) {
            final ItpfConjClause newClause = clause.replaceAllFunctionSymbols(replaceMap);
            newClauses.add(newClause);
            changed = changed || newClause != clause;
        }
        if (changed) {
            return this.factory.create(this.quantification, ImmutableCreator.create(newClauses));
        } else {
            return this;
        }
    }

    @Override
    public Itpf getQuantorfree() {
        return this.factory.create(this.clauses);
    }

    @Override
    public boolean isFalse() {
        return this.clauses.isEmpty();
    }

    @Override
    public boolean isTrue() {
        return this.clauses.contains(this.factory.createEmptyClause());
    }

    @Override
    public ExecutionResult<Conjunction<Itpf>, Itpf> getSelfMark() {
        return new ExecutionResult<Conjunction<Itpf>, Itpf>(new Conjunction<Itpf>(this), ImplicationType.EQUIVALENT,
            ApplicationMode.NoOp, true);
    }
}
