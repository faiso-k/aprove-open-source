package aprove.input.Programs.xtc.tagHandler;

import java.util.*;

import org.xml.sax.*;

import aprove.input.Programs.xtc.*;
import aprove.input.Utility.XML.*;
import aprove.verification.dpframework.BasicStructures.*;

public class ConditionsTag implements TagHandler<XTCTagNames>,
        Consumer<Condition> {

    private final List<Condition> conditions = new LinkedList<Condition>();

    @Override
    public void appendCDATA(String cdata) {
    }

    @Override
    public void finish() {
    }

    @Override
    public TagHandler<XTCTagNames> getSubHandler(XTCTagNames tag)
            throws IllegalArgumentException, UnsupportedOperationException {
        switch (tag) {
        case condition:
            return new ConditionTag(this);
        default:
            throw new IllegalSubTagException(XTCTagNames.conditions.toString(),
                tag.toString());
        }
    }

    public List<Condition> getConditions() {
        return this.conditions;
    }

    @Override
    public void consume(Condition t) {
        this.conditions.add(t);
    }

    @Override
    public void setAttributes(Attributes attributes) {
        if (attributes.getLength() != 0) {
            throw new IllegalTagAttributeException(XTCTagNames.conditions,
                    attributes.getLocalName(0));
        }
    }
}
