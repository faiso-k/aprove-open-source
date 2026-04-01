package aprove.input.Programs.xtc.tagHandler;

import java.util.*;

import org.xml.sax.*;

import aprove.input.Programs.xtc.*;
import aprove.input.Utility.XML.*;
import aprove.verification.dpframework.IDPProblem.PfFunctions.*;
import aprove.verification.dpframework.IDPProblem.PfFunctions.domains.*;
import immutables.*;

public abstract class PredefinedFunctionTag extends
        Producer<PredefinedFunction<? extends Domain>> implements
        TagHandler<XTCTagNames> {

    protected final List<Domain> domains = new LinkedList<Domain>();
    protected final XTCTagNames tag;

    public PredefinedFunctionTag(
            Consumer<PredefinedFunction<? extends Domain>> parent,
            XTCTagNames tag) {
        super(parent);
        this.tag = tag;
    }

    @Override
    public void appendCDATA(String cdata) {
    }

    @Override
    public void finish() {
        this.produce();
    }

    protected void addDomain(Domain dom) {
        this.domains.add(dom);
    }

    protected abstract class PfConstructor {
        PredefinedFunction<? extends Domain> getPf(PredefinedFunction.Func func,
                XTCTagNames tag,
                List<Domain> domains) {
            List<IntegerDomain> intDoms = new LinkedList<IntegerDomain>();
            List<BooleanDomain> boolDoms = new LinkedList<BooleanDomain>();
            for (Domain dom : domains) {
                if (dom instanceof BooleanDomain) {
                    if (!func.isBooleanFunction()) {
                        throw new IllegalArgumentException(
                            "No boolean domains allowed for <" + tag.toString()
                                + ">");
                    }
                    boolDoms.add((BooleanDomain) dom);
                } else if (dom instanceof IntegerDomain) {
                    if (!func.isIntFunction()) {
                        throw new IllegalArgumentException(
                            "No integer domains allowed for <" + tag.toString()
                                + ">");
                    }
                    intDoms.add((IntegerDomain) dom);
                } else {
                    throw new IllegalArgumentException("Unknown domain.");
                }
            }

            if (domains.size() != func.getArity()) {
                throw new IllegalArgumentException("Expected "
                    + Integer.toString(func.getArity()) + " domain(s) for <"
                    + tag.toString() + ">");
            }

            ImmutableList<IntegerDomain> imIntDoms =
                ImmutableCreator.create(intDoms);
            ImmutableList<BooleanDomain> imBoolDoms =
                ImmutableCreator.create(boolDoms);

            return this.generate(imIntDoms, imBoolDoms);
        }

        abstract PredefinedFunction<? extends Domain> generate(ImmutableList<IntegerDomain> imIntDoms,
                ImmutableList<BooleanDomain> imBoolDoms);
    }

    @Override
    public void setAttributes(Attributes attributes) {
        if (attributes.getLength() != 0) {
            throw new IllegalTagAttributeException(this.tag,
                    attributes.getLocalName(0));
        }
    }
}