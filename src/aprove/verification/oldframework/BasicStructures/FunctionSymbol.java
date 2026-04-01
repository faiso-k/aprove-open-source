package aprove.verification.oldframework.BasicStructures;

import java.util.*;

import org.w3c.dom.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Export.Utility.Export_Util.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.xml.*;
import immutables.*;

/**
 * A FunctionSymbol is a String (the name) together with an arity (a natural number).
 *
 * There are no sorts, types, definedFunctionSymbols, TupleSymbols, origins, ... !!!
 *
 * Two FunctionSymbols are equal iff they have equal names and equal arities.
 *
 * Created on 11.04.2005
 *
 * @author thiemann
 */
public final class FunctionSymbol
implements
    Immutable,
    Exportable,
    Comparable<FunctionSymbol>,
    Label,
    HasName,
    HasFunctionSymbols,
    HasArity,
    HasRootSymbol
{

    /**
     * @param doc The document.
     * @param xmlMetaData The meta data.
     * @param fs The FunctionSymbols.
     * @return A CPF-signature element created from a set of FunctionSymbols.
     */
    public static Element cpfSignature(
        Document doc,
        XMLMetaData xmlMetaData,
        Collection<? extends FunctionSymbol> fs
    ) {
        final Element sig = CPFTag.SIGNATURE.create(doc);
        for (FunctionSymbol f : fs) {
            sig.appendChild(
                CPFTag.SYMBOL.create(doc, f.toCPF(doc, xmlMetaData), CPFTag.ARITY.create(doc, f.getArity()))
            );
        }
        return sig;
    }

    /**
     * @param name The name.
     * @param arity The arity.
     * @return A function symbol for a non-null String as name and a natural number as arity.
     */
    public static FunctionSymbol create(String name, int arity) {
        return new FunctionSymbol(name, arity);
    }

    /**
     * @param sig A signature.
     * @return True if the specified signature contains only constants. False otherwise.
     */
    public static boolean onlyConstants(Iterable<? extends FunctionSymbol> sig) {
        for (FunctionSymbol f : sig) {
            if (f.arity > 0) {
                return false;
            }
        }
        return true;
    }

    /**
     * The arity (number of arguments).
     */
    private final int arity;

    /**
     * Cached hash value.
     */
    private final int hashCode;

    /**
     * The name.
     */
    private final String name;

    /**
     * The constructor takes a non-null String as name and a natural number as arity.
     * @param name The name.
     * @param arity The arity.
     */
    private FunctionSymbol(String name, int arity) {
        if (Globals.useAssertions) {
            assert (name != null);
            assert (arity >= 0);
        }
        this.name = name;
        this.arity = arity;
        this.hashCode = (arity << 24) + 49031901 * name.hashCode();
    }

    @Override
    public int compareTo(FunctionSymbol f) {
        final int comp = this.name.compareTo(f.name);
        if (comp != 0) {
            return comp;
        }
        return this.arity == f.arity ? 0 : (this.arity < f.arity ? -1 : 1);
    }

    @Override
    public boolean equals(Object other) {
        if (this == other) {
            return true;
        }
        if (other instanceof FunctionSymbol) {
            final FunctionSymbol f = (FunctionSymbol)other;
            return f.hashCode == this.hashCode && f.name.equals(this.name) && f.arity == this.arity;
        }
        return false;
    }

    @Override
    public String export(Export_Util eu) {
        String actualString = this.name;
        String[] splittedStr;
        // special function symbols: | is not permitted as part of a function symbol in the TPDP.
        if (actualString.contains("|")) {
            splittedStr = actualString.split("[|]");
            // a function symbol of the form model|symbol|label is used for certain semantic labellings
            // Here, model is only present in the output for verification and is thus colored red.
            if (splittedStr.length == 3) {
                return eu.fontcolor(eu.sup(eu.escape(splittedStr[0])), Color.RED)
                    + eu.fontcolor(eu.escape(splittedStr[1]) + eu.sup(eu.escape(splittedStr[2])), Color.BLUE);
            }
        }
        final char head = 94;
        splittedStr = actualString.split("\\" + head, 2);
        if (splittedStr.length == 2) {
            final String fstStr = eu.escape(splittedStr[0]);
            final String sndStr = eu.escape(splittedStr[1]);
            actualString = fstStr + eu.sup(sndStr);
        } else {
            actualString = eu.escape(actualString);
        }
        return eu.fontcolor(actualString, Color.BLUE);
        /*
        if(eu instanceof PLAIN_Util) {
            return eu.fontcolor(actualString, Export_Util.BLUE);
        }
        if(this.arity == 0) {
            return eu.fontcolor(actualString, Export_Util.BLUE);
        }
        return eu.fontcolor(actualString + eu.sub("" + this.arity), Export_Util.BLUE);
        */
    }

    @Override
    public int getArity() {
        return this.arity;
    }

    @Override
    public Set<FunctionSymbol> getFunctionSymbols() {
        return java.util.Collections.singleton(this);
    }

    @Override
    public String getName() {
        return this.name;
    }

    @Override
    public FunctionSymbol getRootSymbol() {
        return this;
    }

    @Override
    public int hashCode() {
        return this.hashCode;
    }

    @Override
    public Element toCPF(Document doc, XMLMetaData xmlMetaData) {
        if (xmlMetaData != null) {
            final XMLMetaData preData = xmlMetaData.getPreData();
            final Pair<FunctionSymbol, FunctionSymbolAnnotator> f_a = xmlMetaData.getLabelMap().get(this);
            if (f_a == null) {
                // unknown symbol
                return this.toCPF(doc, null);
            }
            final Element e = f_a.x.toCPF(doc, preData);
            return f_a.y.annotate(doc, e, preData);
        } else {
            return CPFTag.NAME.create(doc, doc.createTextNode(this.name));
        }
    }

    @Override
    public Element toDOM(Document doc, XMLMetaData xmlMetaData) {
        return this.toDOMSymbol(doc, null);
    }

    @Override
    public Element toDOMLabel(Document doc, XMLMetaData xmlMetaData) {
        return this.toDOM(doc, xmlMetaData);
    }

    /**
     * @param doc The document.
     * @param tupledMap TODO
     * @return TODO
     */
    public Element toDOMSymbol(Document doc, Map<FunctionSymbol, FunctionSymbol> tupledMap) {
        final Element e = XMLTag.FUNCTION_SYMBOL.createElement(doc);
        if (tupledMap != null && tupledMap.get(this) != null) {
            final FunctionSymbol fSym = tupledMap.get(this);
            XMLAttribute.FUNNAME.setAttribute(e, fSym.name);
            XMLAttribute.ARITY.setAttribute(e, "" + fSym.arity);
            XMLAttribute.SHARP.setAttribute(e, "true");
        } else {
            XMLAttribute.FUNNAME.setAttribute(e, this.name);
            XMLAttribute.ARITY.setAttribute(e, "" + this.arity);
        }
        return e;
    }

    @Override
    public String toString() {
        return this.name + (this.arity == 0 ? "" : "_" + this.arity);
    }

}
