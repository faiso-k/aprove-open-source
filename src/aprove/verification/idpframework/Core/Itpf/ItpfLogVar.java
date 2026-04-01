package aprove.verification.idpframework.Core.Itpf;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.idpframework.Core.BasicStructures.*;
import aprove.verification.idpframework.Core.BasicStructures.Substitutions.*;
import aprove.verification.idpframework.Core.IDPGraph.*;
import aprove.verification.idpframework.Processors.ItpfRules.Execution.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import immutables.*;

/**
 * @author Martin Pluecker
 */
@Deprecated
public class ItpfLogVar extends ItpfAtom.ItpfAtomSkeleton {

    static ItpfLogVar create(final String name) {
        return new ItpfLogVar(name);
    }

    private final String name;

    private ItpfLogVar(final String name) {
        this.name = name;
    }

    @Override
    public ItpfAtom applySubstitution(final PolyTermSubstitution sigma) {
        return this;
    }

    @Override
    public void collectExecutionMarks(final Map<ExecutionUid, ExecutionMarkable> executionMarks) {
        this.executionMarksHandler.collectExecutionMarks(executionMarks);
    }

    @Override
    public void collectFunctionSymbols(final Set<IFunctionSymbol<?>> fss) {
    }

    @Override
    public void collectVariables(final Set<IVariable<?>> vars) {
    }

    @Override
    public void collectTerms(final Set<ITerm<?>> terms, final boolean dropVars) {

    }

    @Override
    public void collectNodes(final Set<ImmutablePair<INode, ImmutableTermSubstitution>> nds) {
        // nothing to do here
    }

    @Override
    public void export(final boolean negated,
        final StringBuilder sb,
        final Export_Util o,
        final VerbosityLevel verbosityLevel, final ExecutionStepColorization colors) {
        if (negated) {
            sb.append("!");
        }
        sb.append(this.name);
    }

    @Override
    public Map<String, String> getXmlAttribs(final XmlExporter eu) {
        final Map<String, String> m = new HashMap<String, String>();
        m.put("name", this.name);
        return m;
    }

    @Override
    public XmlContentsMap getXmlContents(final XmlExporter xe) {
        return null;
    }

    @Override
    public boolean isLogVar() {
        return true;
    }

    @Override
    public YNM isTrivial() {
        return YNM.MAYBE;
    }

    @Override
    public ItpfAtom replaceAllFunctionSymbols(final FunctionSymbolReplacement replaceMap) {
        return this;
    }

    @Override
    public int hashCode() {
        return this.name.hashCode();
    }

    @Override
    public boolean equals(final Object obj) {
        if (this == obj) {
            return true;
        }
        if (obj == null) {
            return false;
        }
        if (this.getClass() != obj.getClass()) {
            return false;
        }
        final ItpfLogVar other = (ItpfLogVar) obj;
        return this.name.equals(other.name);
    }


}
