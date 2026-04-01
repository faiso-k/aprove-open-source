package aprove.verification.dpframework.TRSProblem.Utility;

import org.w3c.dom.*;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.xml.*;

public final class Box extends Context {

    public static final Box Instance = new Box();

    private Box(){}

    @Override
    public Element toDOM(final Document doc, final XMLMetaData xmlMetaData) {
        final Element contextTag = XMLTag.CONTEXT.createElement(doc);
        contextTag.appendChild(XMLTag.BOX.createElement(doc));
        return contextTag;
    }

    @Override
    public Element toCPF(final Document doc, final XMLMetaData xmlMetaData) {
        return CPFTag.BOX.create(doc);
    }

    @Override
    public boolean isEmptyContext() {
        return true;
    }

    @Override
    public TRSTerm replace(final TRSTerm t) {
        return t;
    }

    @Override
    public Position getPosition() {
        return Position.create();
    }

    @Override
    public Context applySubstitution(final TRSSubstitution subst) {
        return this;
    }

    @Override
    public Context getSubcontext(final int depth) {
        if (depth != 0) {
            throw new IllegalArgumentException();
        }
        return this;
    }
}
