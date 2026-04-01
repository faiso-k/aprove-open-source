package aprove.input.Programs.xtc.tagHandler;

import org.xml.sax.*;

import aprove.input.Programs.xtc.*;
import aprove.input.Utility.*;
import aprove.input.Utility.XML.*;

/**
 * Handler for {@code problem} Tag.
 */
public class ProblemTag extends Producer<RawTrs> implements
        TagHandler<XTCTagNames> {

    public ProblemTag(Consumer<RawTrs> parent) {
        super(parent);
    }

    private final RawTrs rawtrs = new RawTrs();

    @Override
    public TagHandler<XTCTagNames> getSubHandler(XTCTagNames tag) {
        switch (tag) {
        case trs:
            return new TrsTag(this.rawtrs);
        case strategy:
            return new StrategyTag(this.rawtrs);
        case startterm:
            return new StarttermTag(this.rawtrs);
        case status:
            return new StatusTag(this.rawtrs);
        case metainformation:
            return new MetainformationTag(this.rawtrs);
        default:
            throw new IllegalSubTagException(XTCTagNames.problem.toString(),
                tag.toString());
        }
    }

    @Override
    public void appendCDATA(String cdata) {
    }

    @Override
    public void finish() {
        this.produce();
    }

    public RawTrs getRawTrs() {
        return this.rawtrs;
    }

    @Override
    public RawTrs getResult() {
        return this.rawtrs;
    }

    @Override
    public void setAttributes(Attributes attributes) {
        int l = attributes.getLength();
        for (int i = 0; i < l; i++) {
            String localName = attributes.getLocalName(i);
            String qName = attributes.getQName(i);
            String value = attributes.getValue(i);
            if (!localName.equals(qName)) {
                continue; // ignore non-local attributes
            }
            if ("type".equals(localName)) {
                if ("complexity".equals(value)) {
                    this.rawtrs.setComplexity(true);
                } else if ("termination".equals(value)) {
                    this.rawtrs.setComplexity(false);
                } else {
                    throw new IllegalTagAttributeValueException(
                            XTCTagNames.problem, qName, value);
                }
            } else {
                throw new IllegalTagAttributeException(XTCTagNames.problem,
                        qName);
            }
        }
    }
}
