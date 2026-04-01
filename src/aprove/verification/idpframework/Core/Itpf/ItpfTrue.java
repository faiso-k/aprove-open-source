/**
 * @author mpluecke
 * @version $Id$
 */
package aprove.verification.idpframework.Core.Itpf;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.idpframework.Core.BasicStructures.*;
import aprove.verification.idpframework.Core.BasicStructures.Substitutions.*;
import aprove.verification.idpframework.Core.IDPGraph.*;
import aprove.verification.idpframework.Core.Utility.Marking.*;
import aprove.verification.idpframework.Processors.ItpfRules.Execution.*;
import aprove.verification.oldframework.Utility.*;
import immutables.*;

public class ItpfTrue extends Itpf {

    static ItpfTrue create(final ItpfFactory factory) {
        return new ItpfTrue(factory);
    }

    private final ImmutableSet<ItpfConjClause> clauseSet;

    private ItpfTrue(final ItpfFactory factory) {
        super(ItpfFactory.EMPTY_QUANTORS, ImmutableCreator.create(Collections.singleton(factory.createEmptyClause())));
        this.clauseSet = (ImmutableSet<ItpfConjClause>) this.items;
   }

    @Override
    public final boolean isFalse() {
        return false;
    }

    @Override
    public final boolean isTrue() {
        return true;
    }

    @Override
    protected Itpf applySubstitutionNoCheck(final PolyTermSubstitution sigma,
        final boolean substituteBoundVariables) {
        return this;
    }

    @Override
    public ImmutableSet<IVariable<?>> getBoundVariables() {
        return ITerm.EMPTY_VARIABLES;
    }

    @Override
    public ImmutableSet<ItpfConjClause> getClauses() {
        return this.clauseSet;
    }

    @Override
    public ImmutableSet<IVariable<?>> getFreeVariables() {
        return ITerm.EMPTY_VARIABLES;
    }

    @Override
    public void collectExecutionMarks(final Map<ExecutionUid, ExecutionMarkable> executionMarks) {
        this.executionMarksHandler.collectExecutionMarks(executionMarks);
    }

    @Override
    public ImmutableSet<IFunctionSymbol<?>> getFunctionSymbols() {
        return IFunctionSymbol.EMPTY_SET;
    }

    @Override
    public ImmutableSet<IVariable<?>> getVariables() {
        return ITerm.EMPTY_VARIABLES;
    }

    @Override
    public ImmutableSet<ImmutablePair<INode, ImmutableTermSubstitution>> getNodes() {
        return INode.EMPTY_SET_WITH_SUBSTITUTION;
    }

    @Override
    public ImmutableSet<ITerm<?>> getTerms(final boolean dropVars) {
        return ITerm.EMPTY_SET;
    }

    @Override
    public Itpf replaceAllFunctionSymbols(final FunctionSymbolReplacement replaceMap) {
        return this;
    }

    @Override
    public Itpf getQuantorfree() {
        return this;
    }

    @Override
    public void export(final StringBuilder sb,
        final Export_Util eu,
        final VerbosityLevel verbosityLevel,
        final ExecutionStepColorization colors) {
        sb.append("TRUE");
    }

    @Override
    public Map<String, String> getXmlAttribs(XmlExporter eu) {
        Map<String, String> m = new HashMap<String, String>();
        m.put("name", "TRUE");
        return m;
    }

    @Override
    public XmlContentsMap getXmlContents(XmlExporter xe) {
        return null;
    }

    @Override
    public ExecutionResult<Conjunction<Itpf>, Itpf> getSelfMark() {
        return new ExecutionResult<Conjunction<Itpf>, Itpf>(new Conjunction<Itpf> (this), ImplicationType.EQUIVALENT, ApplicationMode.NoOp, true);
    }

}

