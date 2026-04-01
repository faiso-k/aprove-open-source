package aprove.input.Programs.xtc.tagHandler;

import org.xml.sax.*;

import aprove.input.Programs.xtc.*;
import aprove.input.Utility.*;
import aprove.input.Utility.XML.*;

public class StrategyTag implements TagHandler<XTCTagNames> {

    enum StrategyType {
        // note that the spelling of the enum entries must be identical to
        // the spelling for the strategy name in the XTC format
        FULL, INNERMOST, OUTERMOST, PARALLELINNERMOST;
    }

    private String strategyString = "";
    private RawTrs rawtrs;

    public StrategyTag(RawTrs rawtrs) {
        this.rawtrs = rawtrs;
    }

    @Override
    public void appendCDATA(String cdata) {
        this.strategyString += cdata;
    }

    @Override
    public void finish() {
        StrategyType s = StrategyType.valueOf(this.strategyString.trim());
        switch (s) {
        case INNERMOST:
            this.rawtrs.setInnermost(true);
            break;
        case OUTERMOST:
            this.rawtrs.setOutermost(true);
            break;
        case PARALLELINNERMOST:
            this.rawtrs.setParallelInnermost(true);
            break;
        case FULL:
            break;
        }
    }

    @Override
    public TagHandler<XTCTagNames> getSubHandler(XTCTagNames tag)
            throws IllegalArgumentException, UnsupportedOperationException {
        throw new NoChildTagsAllowed(XTCTagNames.strategy.toString());
    }

    @Override
    public void setAttributes(Attributes attributes) {
        if (attributes.getLength() != 0) {
            throw new IllegalTagAttributeException(XTCTagNames.strategy,
                    attributes.getLocalName(0));
        }
    }
}
