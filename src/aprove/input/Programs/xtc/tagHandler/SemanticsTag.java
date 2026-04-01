package aprove.input.Programs.xtc.tagHandler;

import org.xml.sax.*;

import aprove.input.Programs.xtc.*;
import aprove.input.Utility.XML.*;
import aprove.verification.dpframework.IDPProblem.PfFunctions.*;
import aprove.verification.dpframework.IDPProblem.PfFunctions.domains.*;

public class SemanticsTag implements TagHandler<XTCTagNames>,
        Consumer<PredefinedFunction<? extends Domain>> {

    private PredefinedFunction<? extends Domain> semantics = null;
    private Domain domain = null;

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
        case integers:
            this.domain = DomainFactory.INTEGERS;
            return new EmptyTag(tag);
        case naturals:
            throw new UnsupportedOperationException();
        case booleans:
            this.domain = DomainFactory.BOOLEAN;
            return new EmptyTag(tag);

        case logical_and:
        case logical_or:
        case logical_not:
            return new PredefinedLogicalFunctionTag(tag, this);

        case cast:
        case plus:
        case minus:
        case u_minus:
        case times:
        case div:
        case modulo:
        case greater_than:
        case greater_equals:
        case less_than:
        case less_equals:
        case equals:
        case not_equals:
            return new PredefinedArithmeticFunctionTag(tag, this);

        default:
            throw new IllegalSubTagException(XTCTagNames.semantics.toString(),
                tag.toString());
        }
    }

    @Override
    public void consume(PredefinedFunction<? extends Domain> semantics) {
        this.semantics = semantics;
    }

    public PredefinedFunction<? extends Domain> getFunctionSemantics() {
        return this.semantics;
    }

    public Domain getDomain() {
        return this.domain;
    }

    @Override
    public void setAttributes(Attributes attributes) {
        if (attributes.getLength() != 0) {
            throw new IllegalTagAttributeException(XTCTagNames.semantics,
                    attributes.getLocalName(0));
        }
    }
}
