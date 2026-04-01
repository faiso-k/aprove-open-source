package aprove.verification.dpframework.TRSProblem.Utility;

import java.util.*;

import org.w3c.dom.*;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.xml.*;
import immutables.*;

public final class NonEmptyContext extends Context {

    private final FunctionSymbol f;
    private final ImmutableArrayList<TRSTerm> before;
    private final Context directSubcontext;
    private final ImmutableArrayList<TRSTerm> after;

    public NonEmptyContext(
        final FunctionSymbol f,
            final ImmutableArrayList<TRSTerm> before, final Context directSubcontext,
            final ImmutableArrayList<TRSTerm> after) {
        this.f = f;
        this.before = before;
        this.directSubcontext = directSubcontext;
        this.after = after;
    }

    public FunctionSymbol getRootSymbol() {
        return this.f;
    }

    public ImmutableArrayList<TRSTerm> getTermsBeforeDirectSubcontext() {
        return this.before;
    }

    public Context getDirectSubcontext() {
        return this.directSubcontext;
    }

    public ImmutableArrayList<TRSTerm> getTermsAfterDirectSubcontext() {
        return this.after;
    }

    public int getPositionOfDirectSubcontext() {
        return this.before.size();
    }

    @Override
    public TRSTerm replace(final TRSTerm t) {
        final ArrayList<TRSTerm> args = new ArrayList<TRSTerm>();
        args.addAll(this.before);
        args.add(this.directSubcontext.replace(t));
        args.addAll(this.after);
        return TRSTerm.createFunctionApplication(this.f, ImmutableCreator.create(args));
    }

    /**
     * @return the Position of the "Box" in this Context
     */
    @Override
    public Position getPosition() {
        final Position suffix = this.directSubcontext.getPosition();
        return suffix.prepend(this.before.size());
    }

    /**
     * index != positionOfDirectSubcontext !
     */
    public TRSTerm getArgument(final int index) {
        final int beforeSize = this.before.size();
        if (index <= beforeSize - 1) {
            return this.before.get(index);
        } else {
            return this.after.get(index - beforeSize - 1);
        }
    }

    @Override
    public Context getSubcontext(final int depth) {
        if (depth == 0) {
            return this;
        }
        if (depth < 0) {
            throw new IllegalArgumentException();
        }
        return this.directSubcontext.getSubcontext(depth - 1);
    }


    public boolean isFunctionApplication() {
        return true;
    }

    /**
     * this.isEmptyContext must be false !
     */
    public int getArity() {
        return this.f.getArity();
    }

    @Override
    public Context applySubstitution(final TRSSubstitution subst) {
        final ArrayList<TRSTerm> beforeNewTemp = new ArrayList<TRSTerm>();
        for (int i = 0; i <= this.before.size() - 1; i++) {
            beforeNewTemp.add(this.before.get(i).applySubstitution(subst));
        }
        final ImmutableArrayList<TRSTerm> beforeNew =
            ImmutableCreator.create(beforeNewTemp);
        final Context newDirectSubcontext =
            this.directSubcontext.applySubstitution(subst);
        final ArrayList<TRSTerm> afterNewTemp = new ArrayList<TRSTerm>();
        for (int i = 0; i <= this.after.size() - 1; i++) {
            afterNewTemp.add(this.after.get(i).applySubstitution(subst));
        }
        final ImmutableArrayList<TRSTerm> afterNew =
            ImmutableCreator.create(afterNewTemp);
        return new NonEmptyContext(this.f, beforeNew, newDirectSubcontext,
            afterNew);
    }

    @Override
    public Element toDOM(final Document doc, final XMLMetaData xmlMetaData) {
        final Element contextTag = XMLTag.CONTEXT.createElement(doc);
        contextTag.appendChild(this.getRootSymbol().toDOM(doc, xmlMetaData));
        for (final TRSTerm t : this.before) {
            contextTag.appendChild(t.toDOM(doc, xmlMetaData));
        }
        contextTag.appendChild(this.getDirectSubcontext().toDOM(doc,
            xmlMetaData));
        for (final TRSTerm t : this.after) {
            contextTag.appendChild(t.toDOM(doc, xmlMetaData));
        }
        return contextTag;
    }

    @Override
    public Element toCPF(final Document doc, final XMLMetaData xmlMetaData) {
        final Element funContext = CPFTag.FUN_CONTEXT.createElement(doc);
        funContext.appendChild(this.getRootSymbol().toCPF(doc, xmlMetaData));
        final Element beforeTag = CPFTag.BEFORE.createElement(doc);
        for (final TRSTerm t : this.before) {
            beforeTag.appendChild(t.toCPF(doc, xmlMetaData));
        }
        funContext.appendChild(beforeTag);
        funContext.appendChild(this.getDirectSubcontext().toCPF(doc, xmlMetaData));
        final Element afterTag = CPFTag.AFTER.createElement(doc);
        for (final TRSTerm t : this.after) {
            afterTag.appendChild(t.toCPF(doc, xmlMetaData));
        }
        funContext.appendChild(afterTag);
        return funContext;
    }

    @Override
    public boolean isEmptyContext() {
        return false;
    }

    @Override
    public int hashCode() {
        final int prime = 31;
        int result = 1;
        result = prime * result + ((after == null) ? 0 : after.hashCode());
        result = prime * result + ((before == null) ? 0 : before.hashCode());
        result = prime * result + ((directSubcontext == null) ? 0 : directSubcontext.hashCode());
        result = prime * result + ((f == null) ? 0 : f.hashCode());
        return result;
    }

    @Override
    public boolean equals(Object obj) {
        if (this == obj)
            return true;
        if (obj == null)
            return false;
        if (getClass() != obj.getClass())
            return false;
        NonEmptyContext other = (NonEmptyContext) obj;
        if (after == null) {
            if (other.after != null)
                return false;
        } else if (!after.equals(other.after))
            return false;
        if (before == null) {
            if (other.before != null)
                return false;
        } else if (!before.equals(other.before))
            return false;
        if (directSubcontext == null) {
            if (other.directSubcontext != null)
                return false;
        } else if (!directSubcontext.equals(other.directSubcontext))
            return false;
        if (f == null) {
            if (other.f != null)
                return false;
        } else if (!f.equals(other.f))
            return false;
        return true;
    }



}
