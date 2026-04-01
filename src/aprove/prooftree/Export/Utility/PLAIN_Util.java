/*
 * Created on 31.03.2004
 */
package aprove.prooftree.Export.Utility;

import java.util.*;

import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * @author nowonder
 */
public class PLAIN_Util extends Export_Util {

    public static final int LINE = 0;

    // constants used should start from 0 and then count upwards
    // there should be no gaps!!!

    /**
     * table entries are Strings for:
     * 1. Empty Collection
     * 2. Begin Collection
     * 3. Begin Item
     * 4. End Item
     * 5. Seperator between two Items
     * 6. End Collection
     */
    private static final String[][] layouts = new String[][] { {"empty set", "{", "", "", ", ", "}" }, // 0. SIMPLESET
        {"", "", "- ", "", "\n", "" }, // 1. ENUMERATE
        {"none\n", "\n", "\n    ", "", "\n", "\n" }, // 2. BLOCKQUOTE
        {"", "", "*", "", "\n", "" }, // 3. ITEMIZE
        {"none\n", "\n", "   ", "", "\n", "\n" }, // 4. RULES
        {"none\n", "", "   ", "", "\n", "" }, // 5. NUMERATED_RULES
        {"", "", "", "", "", "" }, // 6. CENTER/SCGRAPHS
        {"", "", "", "", "\n", "" }, // 7. TABLEROWS
        {"", "", "", "", "\n", "" }, // 8. TABLE
        {"none", "   ", "", "", ", ", "" }, // 9. NICER_SET
        {"none", "", "", "", "", "" }, //10. CONCATENATE
        {"none", "", "", "", " || ", "" }, //11. PARALLEL
        {"{}", "{", "", "", ", ", "}" }, // 12. EVEN MORE SIMLER
        {"", " [ ", "", "", " /\\ ", " ] " }, // 13. PACOND
        {"", " [ ", "", "", " & ", " ] " } // 14. PACONDDOT
        };

    public PLAIN_Util() {
    }

    /**
     * layouts a collection of plain-able objects in a given style
     * if one objects in the collection is not plain-able, then toString will be used
     * as representation of this object
     * @param set
     * @param style
     * @return String
     */
    public static String setPLAIN(final Collection<?> set, final int style) {
        PLAIN_Able o;
        final String[] layout = PLAIN_Util.layouts[style];
        if (set == null) {
            return " Null Pointer in PLAIN Set Procedure! \n";
        }
        if (set.isEmpty()) {
            return layout[Export_Util.EMPTY_ENTRY];
        }
        final StringBuilder sb = new StringBuilder();
        sb.append(layout[Export_Util.BEGINCOL_ENTRY]);
        // first entry
        final Iterator<?> i = set.iterator();
        o = PLAIN_Util.safePLAIN(i.next());
        sb.append(layout[Export_Util.BEGINITEM_ENTRY] + o.toPLAIN() + layout[Export_Util.ENDITEM_ENTRY]);
        // remaining entries
        while (i.hasNext()) {
            o = PLAIN_Util.safePLAIN(i.next());
            sb.append(layout[Export_Util.SEPERATE_ENTRY]
                + layout[Export_Util.BEGINITEM_ENTRY]
                + o.toPLAIN()
                + layout[Export_Util.ENDITEM_ENTRY]);
        }
        sb.append(layout[Export_Util.ENDCOL_ENTRY]);
        return sb.toString();
    }

    private static void addTableSeparatorLine(
        final List<Integer> widths,
        final char separatorChar,
        final StringBuilder sb)
    {
        for (int columnIndex = 0; columnIndex < widths.size(); columnIndex++) {
            if (columnIndex == 0) {
                sb.append(separatorChar);
            }
            final int width = 1 + widths.get(columnIndex) + 1;
            for (int j = 0; j < width; j++) {
                sb.append("-");
            }
            sb.append(separatorChar);
        }
        sb.append("\n");
    }

    /**
     * if object implements toPLAIN then this will be used,
     * otherwise toString will be used for toPLAIN
     */
    private static PLAIN_Able safePLAIN(final Object o) {
        if (o instanceof PLAIN_Able) {
            return ((PLAIN_Able) o);
        }
        // Why does safePLAIN does not special case Exportable
        // like safeHTML and safeLaTeX?
        return (new StringPLAIN(o));
    }

    @Override
    public String allQuantor() {
        return "\\/";
    }

    @Override
    public String andSign() {
        return " & ";
    }

    @Override
    public String appSpace() {
        return " ";
    }

    @Override
    public String atSign() {
        return "@";
    }

    @Override
    public String backslash() {
        return "\\";
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String body(final String string) {
        return string;
    }

    @Override
    public String bold(final String s) {
        return s;
    }

    @Override
    public String calligraphic(final String s) {
        return s;
    }

    public String cite(final String cite) {
        return "";
    }

    @Override
    public String complete() {
        return "<=";
    }

    @Override
    public String cond_linebreak() {
        return "\n";
    }

    @Override
    public String eqSign() {
        return "=";
    }

    @Override
    public String equivalent() {
        return "<=>";
    }

    @Override
    public String escape(final String raw) {
        return raw;
    }

    @Override
    public String existQuantor() {
        return "\\E";
    }

    @Override
    public String export(final Object o) {
        final PLAIN_Able e = PLAIN_Util.safePLAIN(o);
        return e.toPLAIN();
    }

    @Override
    public String fontcolor(final String s, final Color color) {
        return s;
    }

    @Override
    public String fontColorCode(final String s, final int color) {
        return s;
    }

    /**
     * @return a/b.
     */
    @Override
    public String fraction(final String numerator, final String denominator) {
        final StringBuilder sb = new StringBuilder(numerator);
        sb.append("/");
        sb.append(denominator);
        return sb.toString();
    }

    @Override
    public String geSign() {
        return ">=";
    }

    @Override
    public String gtSign() {
        return ">";
    }

    @Override
    public String haskellCase(final StringBuffer arg, final List<Pair<StringBuffer, StringBuffer>> cases) {
        final StringBuffer o = new StringBuffer();
        boolean first = true;
        o.append("case ");
        o.append(arg);
        o.append(" of {\n");
        for (final Pair<StringBuffer, StringBuffer> c : cases) {
            if (!first) {
                o.append(";\n");
            }
            o.append(c.getKey() + " " + c.getValue());
            first = false;
        }
        o.append("}\n");
        return o.toString();
    }

    @Override
    public String haskellCond(final List<Pair<StringBuffer, StringBuffer>> crs, final String arrow) {
        final StringBuffer o = new StringBuffer();
        for (final Pair<StringBuffer, StringBuffer> c : crs) {
            if (c.getKey() != null) {
                o.append("|");
                o.append(c.getKey());
            }
            o.append(c.getValue());
        }
        return o.toString();
    }

    @Override
    public String haskellCons(final String text) {
        return text;
    }

    @Override
    public String haskellIf(final StringBuffer cond, final StringBuffer tc, final StringBuffer fc) {
        final StringBuffer o = new StringBuffer();
        o.append("if ");
        o.append(cond);
        o.append(" then ");
        o.append(tc);
        o.append(" else ");
        o.append(fc);
        return o.toString();
    }

    @Override
    public String haskellKeyWord(final String text) {
        return text;
    }

    @Override
    public String haskellLet(final List<StringBuffer> locals, final StringBuffer res) {
        final StringBuffer o = new StringBuffer();
        boolean first = true;
        o.append("let {\n");
        for (final StringBuffer local : locals) {
            if (!first) {
                o.append(";\n");
            }
            o.append(local);
            first = false;
        }
        o.append("} in ");
        o.append(res);
        return o.toString();
    }

    @Override
    public String haskellNoCond(final StringBuffer res, final String arrow) {
        final StringBuffer o = new StringBuffer();
        o.append(" ");
        o.append(arrow);
        o.append(" ");
        o.append(res);
        return o.toString();
    }

    @Override
    public String haskellRules(final StringBuffer name, final List<Pair<StringBuffer, StringBuffer>> rules) {
        final StringBuffer o = new StringBuffer();
        for (final Pair<StringBuffer, StringBuffer> r : rules) {
            o.append(name);
            o.append(" ");
            o.append(r.getKey());
            o.append(r.getValue());
            o.append(";\n");
        }
        return o.toString();
    }

    @Override
    public String haskellVar(final String text) {
        return text;
    }

    @Override
    public String haskellWhere(final List<StringBuffer> locals, final StringBuffer res) {
        final StringBuffer o = new StringBuffer();
        boolean first = true;
        o.append(res);
        o.append(" where {\n");
        for (final StringBuffer local : locals) {
            if (!first) {
                o.append(";\n");
            }
            o.append(local);
            first = false;
        }
        o.append("} \n");
        return o.toString();
    }

    @Override
    public String hline() {
        final StringBuffer res = new StringBuffer();
        for (int i = 0; i < 80; i++) {
            res.append("-");
        }
        return res.toString();
    }

    @Override
    public String idpCCGE() {
        return this.geSign();
    }

    @Override
    public String idpCCGT() {
        return this.gtSign();
    }

    @Override
    public String idpCCWGT() {
        return this.irrSign() + this.idpCCGT();
    }

    @Override
    public String idpItpfEq() {
        return this.eqSign();
    }

    @Override
    public String idpItpfTo() {
        return this.rightarrow();
    }

    @Override
    public String idpItpfToPlus() {
        return this.rightarrow() + this.sup("+");
    }

    @Override
    public String idpItpfToTrans() {
        return this.rightarrow() + this.sup("*");
    }

    @Override
    public String implication() {
        return " ==> ";
    }

    @Override
    public String indent(final String text) {
        return text;
    }

    @Override
    public String index(final List<?> l, final boolean highlight) {
        final StringBuilder sb = new StringBuilder();
        final Iterator<?> it = l.iterator();
        while (it.hasNext()) {
            sb.append(it.next());
            if (it.hasNext()) {
                sb.append(".");
            }
        }
        sb.append("\n");
        return sb.toString();
    }

    @Override
    public String irrSign() {
        return "~";
    }

    @Override
    public String italic(final String s) {
        return s;
    }

    @Override
    public String jokerSign() {
        return "_";
    }

    @Override
    public String leftarrow() {
        return "<-";
    }

    @Override
    public String leftrightarrow() {
        return "<->";
    }

    @Override
    public String colon() {
        return ":";
    }

    @Override
    public String probabilistiChoiceOperator() {
        return "||";
    }

    @Override
    public String leSign() {
        return "<=";
    }

    @Override
    public String linebreak() {
        return "\n";
    }

    @Override
    public String ltSign() {
        return "<";
    }

    @Override
    public String math(final String s) {
        return s;
    }

    @Override
    public String mu() {
        return "mu";
    }

    @Override
    public String multSign() {
        return "*";
    }

    @Override
    public String newline() {
        return "\n\n";
    }

    @Override
    public String nonStrictRelativ() {
        return "_>=_";
    }

    @Override
    public String notSign() {
        return "!";
    }

    @Override
    public String orSign() {
        return " | ";
    }

    @Override
    public String paragraph() {
        return "\n\n";
    }

    @Override
    public String pipeSign() {
        return "|";
    }

    @Override
    public String preFormatted(final String i) {
        return i;
    }

    @Override
    public String quote(final String s) {
        return "\"" + s + "\"";
    }

    @Override
    public String reducesTo() {
        return "=";
    }

    @Override
    public String rightarrow() {
        return "->";
    }

    @Override
    public String set(final Collection c, final int type) {
        return PLAIN_Util.setPLAIN(c, type);
    }

    @Override
    public String sigma() {
        return "sigma";
    }

    @Override
    public String sound() {
        return "=>";
    }

    @Override
    public String strictRelativ() {
        return "_>_";
    }

    @Override
    public String sub(final String s) {
        return "_" + s;
    }

    @Override
    public String succ() {
        return ">";
    }

    @Override
    public String succeq() {
        return ">=";
    }

    @Override
    public String sup(final String s) {
        return "^" + s;
    }

    @Override
    public String table(final List<List<String>> rows) {
        final ArrayList<Integer> columnWidths = new ArrayList<Integer>();
        final StringBuilder sb = new StringBuilder();

        //First, get column width:
        for (final List<String> row : rows) {
            int columnIndex = 0;
            for (final String cellEntry : row) {
                int newMax = cellEntry.length();
                if (columnWidths.size() > columnIndex) {
                    final int oldMax = columnWidths.get(columnIndex);
                    if (oldMax > newMax) {
                        newMax = oldMax;
                    }
                    columnWidths.set(columnIndex, newMax);
                } else {
                    columnWidths.add(newMax);
                }
                columnIndex++;
            }
        }

        //Now format the actual table:
        PLAIN_Util.addTableSeparatorLine(columnWidths, '.', sb);
        final Iterator<List<String>> rowIterator = rows.iterator();
        while (rowIterator.hasNext()) {
            final List<String> row = rowIterator.next();
            int columnIndex = 0;
            for (final String cellEntry : row) {
                if (columnIndex == 0) {
                    sb.append("| ");
                }

                final int colWidth = java.lang.Math.max(1, columnWidths.get(columnIndex));
                sb.append(String.format("%-" + colWidth + "s", cellEntry));
                sb.append(" | ");
                columnIndex++;
            }
            sb.append("\n");
            if (rowIterator.hasNext()) {
                PLAIN_Util.addTableSeparatorLine(columnWidths, '+', sb);
            }
        }
        PLAIN_Util.addTableSeparatorLine(columnWidths, '\'', sb);

        return sb.toString();
    }

    @Override
    public String tableEnd() {
        return ">>>\n";
    }

    @Override
    public String tableRow(final Collection<?> c) {
        final StringBuilder sb = new StringBuilder();
        sb.append(" ");
        final Iterator<?> iter = c.iterator();
        while (iter.hasNext()) {
            final Object element = iter.next();
            sb.append(this.export(element));
            if (iter.hasNext()) {
                sb.append(" \t");
            } else {
                sb.append("\n");
            }
        }
        return sb.toString();
    }

    @Override
    public String tableStart(final int maxColumns) {
        return "<<<\n";
    }

    @Override
    public String tttext(final String text) {
        return text;
    }

    @Override
    public String verb(final String text) {
        return text;
    }

    @Override
    public Object wrapAsRaw(final Object o) {
        return new StringPLAIN(o);
    }

    @Override
    public String isElement() {
        return "in";
    }

    @Override
    public String Omega() {
        return "Omega";
    }
}

/*
 * @author thiemann
 * implents the PLAIN_Able Interface for any type, toString is used for toPLAIN
 */
class StringPLAIN implements PLAIN_Able {

    Object o;

    StringPLAIN(final Object o) {
        this.o = o;
    }

    @Override
    public String toPLAIN() {
        if (this.o != null) {
            return (this.o.toString());
        } else {
            return "";
        }
    }
}
