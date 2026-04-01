package aprove.input.Programs.xtc.tagHandler;

import java.util.*;

import org.xml.sax.*;

import aprove.input.Programs.xtc.*;
import aprove.input.Utility.XML.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;

public class FunappTag extends Producer<TRSTerm> implements
        TagHandler<XTCTagNames>, Consumer<TRSTerm> {

    private NameTag nameTag;

    public FunappTag(Consumer<TRSTerm> parent) {
        super(parent);
    }

    @Override
    public void appendCDATA(String cdata) {
    }

    @Override
    public void finish() {
        this.produce();
    }

    @Override
    public TagHandler<XTCTagNames> getSubHandler(XTCTagNames tag)
            throws IllegalArgumentException, UnsupportedOperationException {
        switch (tag) {
        case name:
            this.nameTag = new NameTag();
            return this.nameTag;
        case arg:
            return new ArgTag(this);
        default:
            throw new IllegalSubTagException(XTCTagNames.funapp.toString(),
                    tag.toString());
        }
    }

    private final ArrayList<TRSTerm> subTerms = new ArrayList<TRSTerm>();

    @Override
    public void consume(TRSTerm t) {
        this.subTerms.add(t);
    }

    @Override
    public TRSTerm getResult() {
        FunctionSymbol f = FunctionSymbol.create(this.nameTag.getName(),
                this.subTerms.size());
        return TRSTerm.createFunctionApplication(f, this.subTerms);
    }

    @Override
    public void setAttributes(Attributes attributes) {
        if (attributes.getLength() != 0) {
            throw new IllegalTagAttributeException(XTCTagNames.funapp,
                    attributes.getLocalName(0));
        }
    }
}
