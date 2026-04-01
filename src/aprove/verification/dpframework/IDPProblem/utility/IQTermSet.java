/**
 *
 * @author mpluecke
 * @version $Id$
 */
package aprove.verification.dpframework.IDPProblem.utility;

import java.util.*;

import org.w3c.dom.*;

import aprove.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.PfFunctions.*;
import aprove.verification.dpframework.IDPProblem.PfFunctions.domains.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.xml.*;
import immutables.*;

public class IQTermSet implements Immutable, XMLObligationExportable, SimpleQTermSet, CPFAdditional {

    private final QTermSet q;

    private final boolean isEmpty;
    private final int hashCode;
    private final IDPPredefinedMap predefinedMap;

    public IQTermSet(final QTermSet q, final IDPPredefinedMap predefinedMap) {
        this.q = q;
        this.predefinedMap = predefinedMap;
        this.isEmpty = q.isEmpty() ;// && predefFunctions.isEmpty();
        this.hashCode = q.hashCode() ;//+ predefFunctions.hashCode();
    }

    public boolean isEmpty() {
        return this.isEmpty;
    }

    /* (non-Javadoc)
     * @see aprove.verification.dpframework.IDPProblem.utility.SimpleQTermSet#getExplicitSignature()
     */
    public ImmutableSet<FunctionSymbol> getExplicitSignature() {
        return this.q.getSignature();
    }

    /* (non-Javadoc)
     * @see aprove.verification.dpframework.IDPProblem.utility.SimpleQTermSet#canAllLhsBeRewritten(java.util.Set)
     */
    @Override
    public boolean canAllLhsBeRewritten(final Set<? extends HasLHS> R) {
        if (R.isEmpty()) {
            return true;
        }
        if (this.isEmpty) {
            return false;
        }

        for (final HasLHS rule : R) {
            if (!this.canBeRewrittenWithNonEmptyQ(rule.getLeft())) {
                return false;
            }
        }
        return true;
    }

    /* (non-Javadoc)
     * @see aprove.verification.dpframework.IDPProblem.utility.SimpleQTermSet#canAllBeRewritten(java.util.Collection)
     */
    @Override
    public boolean canAllBeRewritten(final Collection<TRSFunctionApplication> terms) {
        if (terms.isEmpty()) {
            return true;
        }
        if (this.isEmpty) {
            return false;
        }

        for (final TRSTerm t : terms) {
            if (!this.canBeRewrittenWithNonEmptyQ(t)) {
                return false;
            }
        }
        return true;
    }

    /* (non-Javadoc)
     * @see aprove.verification.dpframework.IDPProblem.utility.SimpleQTermSet#canBeRewritten(aprove.verification.dpframework.BasicStructures.Term)
     */
    @Override
    public boolean canBeRewritten(final TRSTerm t) {
        if (this.isEmpty) {
            return false;
        }
        return this.canBeRewrittenWithNonEmptyQ(t);
    }

    private boolean canBeRewrittenWithNonEmptyQ(final TRSTerm t) {
        if (Globals.useAssertions) {
            assert(!this.isEmpty);
        }
        if (this.q.canBeRewritten(t)) {
            return true;
        }
        for (final TRSFunctionApplication subTerm : t.getNonVariableSubTerms()) {
            final PredefinedFunction<? extends Domain> func = this.predefinedMap.getPredefinedFunction(subTerm.getRootSymbol());
            if (func != null && func.isPredefLhs(subTerm, this.predefinedMap)) {
                return true;
            }
        }
        return false;
    }

    /**
     * checks whether t can be rewritten
     * @param t
     */
    public boolean canAlwaysRewritteAnArgUnifiedPredefLhs(final TRSFunctionApplication t) {
        if (this.isEmpty) {
            return false;
        }
        return this.canAlwaysRewritteAnArgUnifiedPredefLhsNonemptyQW(t);
    }

    private boolean canAlwaysRewritteAnArgUnifiedPredefLhsNonemptyQW(final TRSFunctionApplication t) {
        if (Globals.useAssertions) {
            assert(!this.isEmpty);
        }

        for (final TRSTerm arg : t.getArguments()) {
            if (!arg.isVariable()) {
                final PredefinedFunction<? extends Domain> func = this.predefinedMap.getPredefinedFunction(((TRSFunctionApplication) arg).getRootSymbol());
                if (func != null && func.canMatchPredefLhs(arg, this.predefinedMap)) {
                    return true;
                }
            }
        }
        return false;
    }

    /* (non-Javadoc)
     * @see aprove.verification.dpframework.IDPProblem.utility.SimpleQTermSet#canBeRewrittenAtRoot(aprove.verification.dpframework.BasicStructures.FunctionApplication)
     */
    @Override
    public boolean canBeRewrittenAtRoot(final TRSFunctionApplication t) {
        if (this.q.canBeRewrittenAtRoot(t)) {
            return true;
        }
        final PredefinedFunction<? extends Domain> func = this.predefinedMap.getPredefinedFunction(t.getRootSymbol());
        if (func != null && func.isPredefLhs(t, this.predefinedMap)) {
            return true;
        }
        return false;
    }

    /* (non-Javadoc)
     * @see aprove.verification.dpframework.IDPProblem.utility.SimpleQTermSet#someTermCanBeRewritten(java.lang.Iterable)
     */
    @Override
    public boolean someTermCanBeRewritten(final Iterable<? extends TRSTerm> terms) {
        if (this.isEmpty) {
            return false;
        }
        for (final TRSTerm t : terms) {
            if (this.canBeRewrittenWithNonEmptyQ(t)) {
                return true;
            }
        }
        return false;
    }

    /* (non-Javadoc)
     * @see aprove.verification.dpframework.IDPProblem.utility.SimpleQTermSet#canBeRewrittenBelowRoot(aprove.verification.dpframework.BasicStructures.Term)
     */
    @Override
    public boolean canBeRewrittenBelowRoot(final TRSTerm t){
        if (t.isVariable()) {
            return false;
        }
        return this.someTermCanBeRewritten(((TRSFunctionApplication) t).getArguments());
    }

    public QTermSet getWrappedQ() {
        return this.q;
    }

    public IDPPredefinedMap getPreDefinedMap() {
        return this.predefinedMap;
    }

    public ImmutableSet<TRSFunctionApplication> getExplicitTerms() {
        return this.q.getTerms();
    }

    @Override
    public boolean equals(final Object other) {
        if(this == other) {
            return true;
        }
        if(other instanceof IQTermSet) {
            final IQTermSet i = (IQTermSet) other;
            return i.hashCode == this.hashCode && this.q.equals(i.q);
        }
        return false;
    }

    @Override
    public int hashCode() {
        return this.hashCode;
    }

    @Override
    public Element toDOM(final Document doc, final XMLMetaData xmlMetaData) {
        final Element e = this.q.toDOM(doc, xmlMetaData);
        return e;
    }

    @Override
    public Element toCPF(final Document doc, final XMLMetaData xmlMetaData) {
        final Element qTag = this.q.toCPF(doc, xmlMetaData);
        return qTag;
    }

}
