/**
 * @author mpluecke
 * @version $Id$
 */
package aprove.verification.idpframework.Core.Itpf;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.idpframework.Algorithms.UsableRules.*;
import aprove.verification.idpframework.Core.BasicStructures.*;
import aprove.verification.idpframework.Core.BasicStructures.Substitutions.*;
import aprove.verification.idpframework.Core.IDPGraph.*;
import aprove.verification.idpframework.Core.PredefinedFunctions.*;
import aprove.verification.idpframework.Polynomials.*;
import aprove.verification.idpframework.Processors.ItpfRules.Execution.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import immutables.*;

public class ItpfItp extends ItpfAtom.ItpfAtomSkeleton {

    public static final IActiveContext EMPTY_CONTEXT = IActiveContext.EMPTY_CONTEXT;

    public static ItpfItp create(final ITerm<?> l,
        final RelDependency kLeft,
        final IActiveContext contextL,
        final ItpRelation rel,
        final ITerm<?> r,
        final RelDependency kRight,
        final IActiveContext contextR,
        final ItpfFactory factory) {
        return new ItpfItp(l, kLeft, contextL, rel, r, kRight, contextR, factory);
    }

    protected final ITerm<?> l, r;
    protected final RelDependency kLeft, kRight;
    protected final ItpRelation relation;
    protected final IActiveContext contextL;
    protected final IActiveContext contextR;
    protected final int hash;

    private final ItpfFactory factory;

    private ItpfItp(
            final ITerm<?> l,
            final RelDependency kLeft,
            final IActiveContext contextL,
            final ItpRelation rel,
            final ITerm<?> r,
            final RelDependency kRight,
            final IActiveContext contextR,
            final ItpfFactory factory) {
        super();
        this.l = l;
        if (kLeft != null) {
            this.kLeft = kLeft;
        } else {
            this.kLeft = RelDependency.Increasing;
        }
        if (contextL != null) {
            this.contextL = contextL;
        } else {
            this.contextL = IActiveContext.EMPTY_CONTEXT;
        }

        this.relation = rel;
        this.r = r;

        if (kRight != null) {
            this.kRight = kRight;
        } else {
            this.kRight = RelDependency.Increasing;
        }
        if (contextR != null) {
            this.contextR = contextR;
        } else {
            this.contextR = IActiveContext.EMPTY_CONTEXT;
        }

        this.factory = factory;
        final int prime = 31;
        int result = 1;
        result = prime * result + this.kLeft.hashCode();
        result = prime * result + this.contextL.hashCode();
        result = prime * result + this.kRight.hashCode();
        result = prime * result + this.contextR.hashCode();
        result = prime * result + l.hashCode();
        result = prime * result + r.hashCode();
        result = prime * result + this.relation.hashCode();
        this.hash = result;

//        if (Globals.useAssertions) {
//            assert rel != ItpRelation.EQ || (canIgnoreContextL() && canIgnoreContextR()) : "relation EQ not allowed under a context";
//        }
}

    @Override
    public ItpfItp applySubstitution(final PolyTermSubstitution sigma) {
        if (sigma.isEmpty()) {
            return this;
        }
        final ITerm<?> newL = this.l.applySubstitution(sigma);
        final ITerm<?> newR = this.r.applySubstitution(sigma);
        final boolean changed = this.l != newL || this.r != newR;
        return changed ? this.factory.createItp(newL, this.kLeft, this.contextL, this.relation,
            newR, this.kRight, this.contextR) : this;
    }

    @Override
    public void collectExecutionMarks(final Map<ExecutionUid, ExecutionMarkable> executionMarks) {
        this.executionMarksHandler.collectExecutionMarks(executionMarks);
    }

    @Override
    public void collectFunctionSymbols(final Set<IFunctionSymbol<?>> fss) {
        this.l.collectFunctionSymbols(fss);
        this.r.collectFunctionSymbols(fss);
    }

    @Override
    public ItpfAtom replaceAllFunctionSymbols(final FunctionSymbolReplacement replaceMap) {
        final ITerm<?> newL = this.l.replaceAllFunctionSymbols(replaceMap);
        final ITerm<?> newR = this.r.replaceAllFunctionSymbols(replaceMap);
        final IActiveContext newContextL;
        if (this.contextL != null) {
            newContextL = this.contextL.replaceFunctionSymbols(replaceMap);
        } else {
            newContextL = null;
        }
        final IActiveContext newContextR;
        if (this.contextR != null) {
            newContextR = this.contextR.replaceFunctionSymbols(replaceMap);
        } else {
            newContextR = null;
        }

        if (newL != this.l || newR != this.r || newContextL != this.contextL
            || newContextR != this.contextR) {
            return this.factory.createItp(newL, this.kLeft, newContextL,
                this.relation, newR, this.kRight, newContextR);
        } else {
            return this;
        }
    }

    @Override
    public void collectVariables(final Set<IVariable<?>> vars) {
        this.l.collectVariables(vars);
        this.r.collectVariables(vars);
    }

    @Override
    public void collectNodes(final Set<ImmutablePair<INode, ImmutableTermSubstitution>> nds) {
        // nothing to do here
    }

    @Override
    public void collectTerms(final Set<ITerm<?>> terms, final boolean dropVars) {
        if (!dropVars || !this.l.isVariable()) {
            terms.add(this.l);
        }

        if (!dropVars || !this.r.isVariable()) {
            terms.add(this.r);
        }
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
        final ItpfItp other = (ItpfItp) obj;
        return this.kLeft == other.kLeft && this.kRight == other.kRight
            && this.relation == other.relation
            && this.contextL.equals(other.contextL)
            && this.contextR.equals(other.contextR)
            && this.l.equals(other.l) && this.r.equals(other.r);
    }

    @Override
    public void export(final boolean negated,
        final StringBuilder sb,
        final Export_Util o,
        final VerbosityLevel verbosityLevel, final ExecutionStepColorization colors)
    {
        if (negated) {
            sb.append(o.notSign());
        }
        if (negated || verbosityLevel.compareTo(VerbosityLevel.HIGH) >= 0) {
            sb.append("(");
        }
        sb.append(this.l.export(o));
        if (verbosityLevel.compareTo(VerbosityLevel.HIGH) >= 0 && !this.canIgnoreContextL()) {
            sb.append(o.sub(this.kLeft.getK().toString()));
            if (!this.contextL.isEmpty()) {
                sb.append(" @ ");
                this.contextL.export(sb, o, verbosityLevel);
            }
        }
        boolean rTrue = false;
        if (!this.r.isVariable()) {
            rTrue =
                IDPPredefinedMap.DEFAULT_MAP.getBooleanTrue().equals(
                    ((IFunctionApplication<?>) this.r).getRootSymbol().getSemantics());
        }
        if (!this.relation.equals(ItpRelation.TO_TRANS) || !rTrue
            || verbosityLevel.compareTo(VerbosityLevel.HIGH) >= 0) {
            sb.append(" ");
            sb.append(this.relation.export(o));
            sb.append(" ");
            sb.append(this.r.export(o));
        }
        if (verbosityLevel.compareTo(VerbosityLevel.HIGH) >= 0 && !this.canIgnoreContextR()) {
            sb.append(o.sub(this.kRight.getK().toString()));
            if (!this.contextR.isEmpty()) {
                sb.append(" @ ");
                this.contextR.export(sb, o, verbosityLevel);
            }
        }
        if (negated || verbosityLevel.compareTo(VerbosityLevel.HIGH) >= 0) {
            sb.append(")");
        }
    }

    @Override
    public Map<String, String> getXmlAttribs(XmlExporter xe) {
        Map<String, String> m = new HashMap<String, String>();
        return m;
    }

    @Override
    public XmlContentsMap getXmlContents(XmlExporter xe) {
        XmlContentsMap contents = new XmlContentsMap();
        contents.add("l", this.l);
        contents.add("kLeft", this.kLeft);
        contents.add("contextL", this.contextL);
        contents.add("relation", this.relation);
        contents.add("r", this.r);
        contents.add("contextR", this.contextR);
        return contents;
    }

    public boolean canIgnoreContextL() {
        return this.kLeft == null || this.kLeft == RelDependency.Increasing
            && IActiveContext.EMPTY_CONTEXT.equals(this.contextL);
    }

    public boolean canIgnoreContextR() {
        return this.kRight == null || this.kRight == RelDependency.Increasing
            && IActiveContext.EMPTY_CONTEXT.equals(this.contextR);
    }

    public IActiveContext getContextL() {
        return this.contextL;
    }

    public IActiveContext getContextR() {
        return this.contextR;
    }

    public RelDependency getKLeft() {
        return this.kLeft;
    }

    public RelDependency getKRight() {
        return this.kRight;
    }

    public ITerm<?> getL() {
        return this.l;
    }

    public ITerm<?> getR() {
        return this.r;
    }

    public ItpRelation getRelation() {
        return this.relation;
    }

    @Override
    public YNM isTrivial() {
        switch (this.relation) {
        case EQ:
        case TO_TRANS:
        case TO_SYM_TRANS:
            return this.l.equals(this.r) ? YNM.YES : YNM.MAYBE;
        default:
            return YNM.MAYBE;
        }
    }

    @Override
    public boolean isItp() {
        return true;
    }

    @Override
    public int hashCode() {
        return this.hash;
    }

}
