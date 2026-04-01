package aprove.input.Programs.xtc.tagHandler;

import java.util.*;

import org.xml.sax.*;

import aprove.input.Programs.xtc.*;
import aprove.input.Utility.*;
import aprove.input.Utility.XML.*;
import aprove.verification.oldframework.BasicStructures.*;

public class FuncsymTag implements TagHandler<XTCTagNames> {

    private final RawTrs rawtrs;
    private NameTag nameTag;
    private ArityTag arityTag;
    private TheoryTag theoryTag;
    private ReplacementmapTag replacementmapTag;
    private SemanticsTag semanticsTag;

    public FuncsymTag(RawTrs rawtrs) {
        this.rawtrs = rawtrs;
    }

    @Override
    public void appendCDATA(String cdata) {
    }

    @Override
    public void finish() {
        if (this.nameTag == null) {
            throw new IllegalArgumentException("<name> tag required.");
        }
        if (this.arityTag == null) {
            throw new IllegalArgumentException("<arity> tag required.");
        }
        String name = this.nameTag.getName();
        int arity = this.arityTag.getArity();
        FunctionSymbol sym = FunctionSymbol.create(name, arity);
        this.rawtrs.addArityMapEntry(name, arity);
        if (this.theoryTag != null) {
            TheoryTag.Names theory = this.theoryTag.getTheory();
            switch (theory) {
            case A:
                this.rawtrs.addAssociativeName(name);
                break;
            case C:
                this.rawtrs.addCommutativeName(name);
                break;
            case AC:
                this.rawtrs.addAssociativeAndCommutativeName(name);
                break;
            }
        }
        if (this.replacementmapTag != null) {
            Set<Integer> replacements =
                this.replacementmapTag.getReplacements();
            this.rawtrs.addReplacementMapEntry(name, replacements);
        }
        if (this.semanticsTag != null) {
            if (this.semanticsTag.getFunctionSemantics() != null) {
                this.rawtrs.addPredefinedFunctionSemantics(sym,
                    this.semanticsTag.getFunctionSemantics());
            } else if (this.semanticsTag.getDomain() != null) {
                this.rawtrs.addDomainSemantics(sym,
                    this.semanticsTag.getDomain());
            }
        }
    }

    @Override
    public TagHandler<XTCTagNames> getSubHandler(XTCTagNames tag)
            throws IllegalArgumentException, UnsupportedOperationException {
        switch (tag) {
        case name:
            this.nameTag = new NameTag();
            return this.nameTag;
        case arity:
            this.arityTag = new ArityTag();
            return this.arityTag;
        case theory:
            this.theoryTag = new TheoryTag();
            return this.theoryTag;
        case replacementmap:
            this.replacementmapTag = new ReplacementmapTag();
            return this.replacementmapTag;
        case semantics:
            this.semanticsTag = new SemanticsTag();
            return this.semanticsTag;
        default:
            throw new IllegalSubTagException(XTCTagNames.funcsym.toString(),
                tag.toString());
        }
    }

    @Override
    public void setAttributes(Attributes attributes) {
        if (attributes.getLength() != 0) {
            throw new IllegalTagAttributeException(XTCTagNames.funcsym,
                    attributes.getLocalName(0));
        }
    }
}
