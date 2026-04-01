package aprove.input.Programs.xtc.tagHandler;

import org.xml.sax.*;

import aprove.input.Programs.xtc.*;
import aprove.input.Utility.XML.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.BasicStructures.Condition.*;

public class ConditionTag extends Producer<Condition> implements
        TagHandler<XTCTagNames> {

    private TermWrappingTag lhsTag;
    private TermWrappingTag rhsTag;

    public ConditionTag(Consumer<Condition> parent) {
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
        case lhs:
            this.lhsTag = new TermWrappingTag(XTCTagNames.lhs);
            return this.lhsTag;
        case rhs:
            this.rhsTag = new TermWrappingTag(XTCTagNames.rhs);
            return this.rhsTag;
        default:
            throw new IllegalSubTagException(XTCTagNames.condition.toString(),
                tag.toString());
        }
    }

    @Override
    public Condition getResult() {
        TRSTerm lhs = this.lhsTag.getTerm();
        TRSTerm rhs = this.rhsTag.getTerm();
        return Condition.create(lhs, rhs, ConditionType.ARROW);
    }

    @Override
    public void setAttributes(Attributes attributes) {
        if (attributes.getLength() != 0) {
            throw new IllegalTagAttributeException(XTCTagNames.condition,
                    attributes.getLocalName(0));
        }
    }
}
