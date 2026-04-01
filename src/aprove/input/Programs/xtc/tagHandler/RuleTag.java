package aprove.input.Programs.xtc.tagHandler;

import java.util.*;

import org.xml.sax.*;

import aprove.input.Programs.xtc.*;
import aprove.input.Utility.*;
import aprove.input.Utility.XML.*;
import aprove.verification.dpframework.BasicStructures.*;

public class RuleTag implements TagHandler<XTCTagNames> {

    private final RawTrs rawtrs;
    private TermWrappingTag lhstag;
    private TermWrappingTag rhstag;
    private ConditionsTag conditionstag;
    private final boolean relative;

    public RuleTag(RawTrs rawtrs, boolean relative) {
        this.rawtrs = rawtrs;
        this.relative = relative;
    }

    @Override
    public void appendCDATA(String cdata) {
    }

    @Override
    public void finish() {
        TRSTerm lhs = this.lhstag.getTerm();
        TRSTerm rhs = this.rhstag.getTerm();
        List<Condition> conditions;
        if (this.conditionstag != null) {
            conditions = this.conditionstag.getConditions();
        } else {
            conditions = Collections.emptyList();
        }
        boolean relative = this.relative;

        this.rawtrs.addAbstractRule(lhs, rhs, conditions, relative, false);
    }

    @Override
    public TagHandler<XTCTagNames> getSubHandler(XTCTagNames tag)
            throws IllegalArgumentException, UnsupportedOperationException {
        switch (tag) {
        case lhs:
            this.lhstag = new TermWrappingTag(XTCTagNames.lhs);
            return this.lhstag;
        case rhs:
            this.rhstag = new TermWrappingTag(XTCTagNames.rhs);
            return this.rhstag;
        case conditions:
            this.conditionstag = new ConditionsTag();
            return this.conditionstag;
        default:
            throw new IllegalSubTagException(XTCTagNames.rule.toString(),
                tag.toString());
        }
    }

    @Override
    public void setAttributes(Attributes attributes) {
        if (attributes.getLength() != 0) {
            throw new IllegalTagAttributeException(XTCTagNames.rule,
                    attributes.getLocalName(0));
        }
    }
}
