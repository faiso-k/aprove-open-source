package aprove.input.Programs.xtc.tagHandler;

import org.xml.sax.*;

import aprove.input.Programs.xtc.*;
import aprove.input.Utility.*;
import aprove.input.Utility.XML.*;

public class ConditiontypeTag implements TagHandler<XTCTagNames> {

    enum ConditionType {
        JOIN, ORIENTED, OTHER;
    }

    private RawTrs rawtrs;
    private String conditiontypeString = "";

    public ConditiontypeTag(RawTrs rawtrs) {
        this.rawtrs = rawtrs;
    }

    @Override
    public void appendCDATA(String cdata) {
        this.conditiontypeString += cdata;
    }

    @Override
    public void finish() {
        ConditionType t =
            ConditionType.valueOf(this.conditiontypeString.trim());
        /* TODO set conditiontype in rawtrs. must apply retroactive for all existing conditional rules and also for all newly added rules. */
        switch (t) {
        case JOIN:
        case ORIENTED:
        case OTHER:
        }
    }

    @Override
    public TagHandler<XTCTagNames> getSubHandler(XTCTagNames tag)
            throws IllegalArgumentException, UnsupportedOperationException {
        throw new NoChildTagsAllowed(XTCTagNames.conditiontype.toString());
    }

    @Override
    public void setAttributes(Attributes attributes) {
        if (attributes.getLength() != 0) {
            throw new IllegalTagAttributeException(XTCTagNames.conditiontype,
                    attributes.getLocalName(0));
        }
    }
}
