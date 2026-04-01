package aprove.input.Programs.xtc.tagHandler;

import org.xml.sax.*;

import aprove.input.Programs.xtc.*;
import aprove.input.Utility.XML.*;
import aprove.verification.dpframework.BasicStructures.*;

public class VarTag extends Producer<TRSTerm> implements TagHandler<XTCTagNames> {

    public VarTag(Consumer<TRSTerm> parent) {
        super(parent);
    }

    String name = "";

    @Override
    public void appendCDATA(String cdata) {
        this.name += cdata;
    }

    @Override
    public void finish() {
        this.produce();
    }

    @Override
    public TagHandler<XTCTagNames> getSubHandler(XTCTagNames tag)
            throws IllegalArgumentException, UnsupportedOperationException {
        throw new NoChildTagsAllowed(XTCTagNames.var.toString());
    }

    @Override
    public TRSTerm getResult() {
        return TRSTerm.createVariable(this.name);
    }

    @Override
    public void setAttributes(Attributes attributes) {
        if (attributes.getLength() != 0) {
            throw new IllegalTagAttributeException(XTCTagNames.var,
                    attributes.getLocalName(0));
        }
    }
}
