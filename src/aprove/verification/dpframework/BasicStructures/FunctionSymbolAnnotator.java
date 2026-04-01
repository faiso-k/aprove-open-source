package aprove.verification.dpframework.BasicStructures;

import java.util.*;

import org.w3c.dom.*;

import aprove.verification.oldframework.BasicStructures.*;
import aprove.xml.*;

/**
 * @author thiemann
 *
 * A class to annotate labels/sharps/.... to xml-elements in CPF-format.
 */
public abstract class FunctionSymbolAnnotator {

    public abstract Element annotate(Document doc, Element e, XMLMetaData preMetaData);

    public static final FunctionSymbolAnnotator EMPTY_ANNOTATOR =
            new FunctionSymbolAnnotator() {

        @Override
        public Element annotate(Document doc, Element e, XMLMetaData preMetaData) {
            return e;
        }

    };

    public static final FunctionSymbolAnnotator SHARP_ANNOTATOR =
            new FunctionSymbolAnnotator() {

        @Override
        public Element annotate(Document doc, Element e, XMLMetaData preMetaData) {
            return CPFTag.SHARP.create(doc, e);
        }

    };

    public static FunctionSymbolAnnotator createNumlabAnnotator(final List<IntLabel> labels) {
        return new FunctionSymbolAnnotator() {

            @Override
            public Element annotate(Document doc, Element e, final XMLMetaData preMetaData) {
                Element numlabel = CPFTag.NUMBER_LABEL.create(doc);
                for (Label label : labels) {
                    numlabel.appendChild(label.toCPF(doc, preMetaData));
                }
                return CPFTag.LABELED_SYMBOL.create(doc, e, numlabel);
            }

        };

    }

    public static FunctionSymbolAnnotator createSymlabAnnotator(final List<FunctionSymbol> labels) {
        return new FunctionSymbolAnnotator() {

            @Override
            public Element annotate(Document doc, Element e, final XMLMetaData preMetaData) {
                Element symlabel = CPFTag.SYMBOL_LABEL.create(doc, e);
                for (Label label : labels) {
                    symlabel.appendChild(label.toCPF(doc, preMetaData));
                }
                return CPFTag.LABELED_SYMBOL.create(doc, e, symlabel);
            }

        };

    }

}
