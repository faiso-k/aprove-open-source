/*
 * Created on 18.03.2003
 */
package aprove.prooftree.Export.Utility;

import java.util.*;

import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * @author thiemann, luecking
 */
public class HTML_Util extends Export_Util {

    public static final int LINE = 0;

    // constants used should start from 0 and then count upwards
    // there should be no gaps!!!

    /**
     * Tags used for indentation.
     */
    private static final String[] indentlayout =
        new String[] {"<table style=\"margin-left: ", "pt\"><tr><td>", "</td></tr></table>" };

    /**
     * Static value for indents in pt.
     */
    private static final int indentsize = 25;

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
        {"", "<ol>", "<li>", "</li>", "\n", "</ol>" }, // 1. ENUMERATE
        {"none<br>", "<blockquote>", "<br>", "", "\n", "</blockquote>" }, // 2. BLOCKQUOTE
        {"", "<ul>", "<li>", "</li>", "\n", "</ul>" }, // 3. ITEMIZE
        {"none<br>", "<blockquote>", "<br>", "", "\n", "</blockquote>" }, // 4. RULES
        {"none<br>", "<blockquote>", "<br>", "", "\n", "</blockquote>" }, // 5. NUMERATED_RULES
        {"", "<center>", "", "", "</center>" }, // 6. CENTER/SCGRAPHS
        {"", "", "<tr>", "</tr>", "\n", "" }, // 7. TABLEROWS
        {"", "<table border=\"1\"><tr>", "<td align=\"center\" valign=\"top\">", "</td>", "\n", "</tr></table>" }, // 8. TABLE
        {"none<br>", "<blockquote> <br>", "", "", ", ", "</blockquote>" }, // 9. NICER_SET
        {"none<br>", "", "", "", "", "" }, //10. CONCATENATE
        {"none", "", "", "", " || ", "" }, //11. PARALLEL
        {"{}", "{", "", "", ", ", "}" }, // 12. EVEN MORE SIMPLER
        {"", " [ ", "", "", " &#8743; ", " ] " }, // 13. PACOND
        {"", " [ ", "", "", " &#8743; ", " ] " } // 14. PACONDDOT
        };

    public HTML_Util() {
    }

    /**
     * layouts a collection of html-able objects in a gvien style
     * if one objects in the collection is not html-able, then toString will be used
     * as representation of this object
     * @param set
     * @param style
     * @return String
     */
    public static String setHTML(final Collection<?> set, final int style) {
        HTML_Able o;
        final String[] layout = HTML_Util.layouts[style];
        if (set == null) {
            return " Null Pointer in HTML Set Procedure! \n";
        }
        if (set.isEmpty()) {
            return layout[Export_Util.EMPTY_ENTRY];
        }
        final StringBuilder sb = new StringBuilder();
        sb.append(layout[Export_Util.BEGINCOL_ENTRY]);
        final Iterator<?> i = set.iterator();
        // first entry
        Object obj = i.next();
        if (style == Export_Util.RULES && obj instanceof Pair) {
            final Pair p = (Pair) obj;
            o =
                new StringHTML(HTML_Util.safeHTML(p.x).toHTML()
                    + " "
                    + new HTML_Util().rightarrow()
                    + " "
                    + HTML_Util.safeHTML(p.y).toHTML(), true);
        } else {
            o = HTML_Util.safeHTML(obj);
        }
        sb.append(layout[Export_Util.BEGINITEM_ENTRY] + o.toHTML() + layout[Export_Util.ENDITEM_ENTRY]);
        // remaining entries
        while (i.hasNext()) {
            obj = i.next();
            if (style == Export_Util.RULES && obj instanceof Pair) {
                final Pair p = (Pair) obj;
                o =
                    new StringHTML(HTML_Util.safeHTML(p.x).toHTML()
                        + " "
                        + new HTML_Util().rightarrow()
                        + " "
                        + HTML_Util.safeHTML(p.y).toHTML(), true);
            } else {
                o = HTML_Util.safeHTML(obj);
            }
            sb.append(layout[Export_Util.SEPERATE_ENTRY]
                + layout[Export_Util.BEGINITEM_ENTRY]
                + o.toHTML()
                + layout[Export_Util.ENDITEM_ENTRY]);
        }
        sb.append(layout[Export_Util.ENDCOL_ENTRY]);
        return sb.toString();
    }

    /**
     * if object implements toHTML then this will be used,
     * otherwise toString will be used for toHTML
     */
    private static HTML_Able safeHTML(final Object o) {
        //System.out.println("Calling html export on "+o.getClass());
        if (o instanceof HTML_Able) {
            return ((HTML_Able) o);
        }
        if (o instanceof Exportable) {
            return new StringHTML(((Exportable) o).export(new HTML_Util()), true);
        }
        /**
         * Workaround stuff. The assumption, that Strings are passed
         * unescaped, is widely used. So we escape Strings from escaping. */
        if (o instanceof String) {
            return new StringHTML(o, true);
        }
        return new StringHTML(o, false);
    }

    @Override
    public String allQuantor() {
        return "&#8704;";
    }

    @Override
    public String andSign() {
        return "&#8743;";
    }

    @Override
    public String appSpace() {
        return "&#160;";
    }

    @Override
    public String atSign() {
        return "@";
    }

    @Override
    public String backslash() {
        return "\\";
    }

    @Override
    public String body(final String text) {
        return "<html><body>" + text + "</body></html>";
    }

    @Override
    public String bold(final String s) {
        return "<b>" + s + "</b>";
    }

    @Override
    public String calligraphic(final String s) {
        return "<i>" + s + "</i>";
    }

    public String cite(final String cite) {
        return "";
    }

    @Override
    public String complete() {
        return "&#8658;";
    }

    @Override
    public String cond_linebreak() {
        return "<br>";
    }

    @Override
    public String eqSign() {
        return "&#61;";
    }

    @Override
    public String equivalent() {
        return "&#8660;";
    }

    @Override
    public String escape(final String raw) {
        return StringHTML.escape(raw);
    }

    @Override
    public String existQuantor() {
        return "&#8707;";
    }

    @Override
    public String export(final Object o) {
        if (o instanceof String) {
            return (String) o;
        } else if (o instanceof HTML_Able) {
            return ((HTML_Able) o).toHTML();
        } else if (o instanceof Exportable) {
            return ((Exportable) o).export(this);
        } else {
            return o.toString();
        }
    }

    @Override
    public String fontcolor(final String s, final Color color) {
        String col = "";
        switch (color) {
        case BLACK:
            col = "#000000";
            break;
        case RED:
            col = "#cc0000";
            break;
        case GREEN:
            col = "#00cc00";
            break;
        case YELLOW:
            col = "#cccc00";
            break;
        case BLUE:
            col = "#0000cc";
            break;
        case GRAY:
            col = "#ffffff";
            break;
        case DARKBLUE:
            col = "#000088";
            break;
        case BROWN:
            col = "#666600";
            break;
        default:
            col = "#000000";
            break;
        }
        return "<font color=\"" + col + "\">" + s + "</font>";
    }

    @Override
    public String fontColorCode(final String s, final int color) {
        String col = Integer.toHexString(color);
        for (int i = col.length() - 6; i > 0; i--) {
            col = "0" + col;
        }

        return "<font color=\"#" + col + "\">" + s + "</font>";
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
        return "&ge;";
    }

    @Override
    public String gtSign() {
        return "&gt;";
    }

    @Override
    public String haskellCase(final StringBuffer arg, final List<Pair<StringBuffer, StringBuffer>> cases) {
        final StringBuffer o = new StringBuffer();
        o.append("<table cellspacing=\"0\" cellpadding=\"0\" border=\"0\" frame=\"void\" >\n");
        o.append("<tr>");
        o.append("<td valign=\"top\" >case&#160;</td>");
        o.append("<td valign=\"top\" colspan=\"2\">");
        o.append(arg);
        o.append(" of");
        o.append("</td>");
        o.append("</tr>");
        for (final Pair<StringBuffer, StringBuffer> c : cases) {
            o.append("<tr>");
            o.append("<td>&#160;</td>");
            o.append("<td valign=\"top\">");
            o.append(c.getKey());
            o.append("</td>");
            o.append("<td valign=\"top\">");
            o.append(c.getValue());
            o.append("</td>");
            o.append("</tr>\n");
        }
        o.append("</table>");
        return o.toString();
    }

    @Override
    public String haskellCond(final List<Pair<StringBuffer, StringBuffer>> crs, final String arrow) {
        final StringBuffer o = new StringBuffer();
        o.append("<table cellspacing=\"0\" cellpadding=\"0\" border=\"0\" frame=\"void\" >\n");
        for (final Pair<StringBuffer, StringBuffer> c : crs) {
            o.append("<tr>");
            o.append("<td valign=\"top\">&#160;|&#160;</td>");
            o.append("<td valign=\"top\">");
            o.append(c.getKey());
            o.append("</td>");
            o.append("<td valign=\"bottom\">");
            o.append("<table cellspacing=\"0\" cellpadding=\"0\" border=\"0\" frame=\"void\" >\n");
            o.append("<tr>");
            o.append("<td valign=\"top\">&#160;");
            o.append(arrow);
            o.append("&#160;</td>");
            o.append("<td valign=\"top\">");
            o.append(c.getValue());
            o.append("</td>");
            o.append("</tr>\n");
            o.append("</table>");
            o.append("</td>");
            o.append("</tr>\n");
        }
        o.append("</table>");
        return o.toString();
    }

    @Override
    public String haskellCons(final String text) {
        return this.fontcolor(text, Color.BROWN);
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
        o.append("<table cellspacing=\"0\" cellpadding=\"0\" border=\"0\" frame=\"void\" >\n");
        for (final StringBuffer local : locals) {
            o.append("<tr>");
            if (first) {
                o.append("<td valign=\"top\">");
                o.append("let&#160;");
                o.append("</td>");
            } else {
                o.append("<td>");
                o.append("</td>");
            }
            o.append("<td valign=\"top\">");
            o.append(local);
            o.append("</td>");
            first = false;
            o.append("</tr>\n");
        }
        o.append("<td valign=\"top\">");
        o.append("in&#160;");
        o.append("</td>");
        o.append("<td valign=\"top\">");
        o.append(res);
        o.append("</td>");
        o.append("</tr>\n");
        o.append("</table>");
        return o.toString();
    }

    @Override
    public String haskellNoCond(final StringBuffer res, final String arrow) {
        final StringBuffer o = new StringBuffer();
        o.append("&#160;");
        o.append(arrow);
        o.append("&#160;");
        o.append(res);
        return o.toString();
    }

    @Override
    public String haskellRules(final StringBuffer name, final List<Pair<StringBuffer, StringBuffer>> rules) {
        final StringBuffer o = new StringBuffer();
        o.append("<table cellspacing=\"0\" cellpadding=\"0\" border=\"0\" frame=\"void\" >\n");
        for (final Pair<StringBuffer, StringBuffer> r : rules) {
            o.append("<tr>");
            o.append("<td valign=\"top\">");
            o.append(name);
            o.append("&#160;</td>");
            o.append("<td valign=\"top\">");
            o.append(r.getKey());
            o.append("</td>");
            o.append("<td valign=\"top\">");
            o.append(r.getValue());
            o.append("</td>");
            o.append("</tr>\n");
        }
        o.append("</table>");
        return o.toString();
    }

    @Override
    public String haskellVar(final String text) {
        return this.fontcolor(text, Color.DARKBLUE);
    }

    @Override
    public String haskellWhere(final List<StringBuffer> locals, final StringBuffer res) {
        final StringBuffer o = new StringBuffer();
        boolean first = true;
        o.append("<table cellspacing=\"0\" cellpadding=\"0\" border=\"0\" frame=\"void\" >\n");
        o.append("<td  valign=\"top\" colspan=\"2\">");
        o.append(res);
        o.append("</td>");
        o.append("</tr>\n");
        for (final StringBuffer local : locals) {
            o.append("<tr>");
            if (first) {
                o.append("<td valign=\"top\">");
                o.append("where&#160;");
                o.append("</td>");
            } else {
                o.append("<td>");
                o.append("</td>");
            }
            o.append("<td valign=\"top\">");
            o.append(local);
            o.append("</td>");
            first = false;
            o.append("</tr>\n");
        }
        o.append("</table>");
        return o.toString();
    }

    @Override
    public String hline() {
        return "<hr>";
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
        return "&#8658;";
    }

    @Override
    public String indent(final String text) {
        return HTML_Util.indentlayout[0]
            + HTML_Util.indentsize
            + HTML_Util.indentlayout[1]
            + text
            + HTML_Util.indentlayout[2];
    }

    @Override
    public String index(final List<?> l, final boolean highlight) {
        final StringBuilder sb = new StringBuilder();
        final String placeholder = ".";
        final int s = l.size();
        for (int i = 0; i < s; i++) {
            if (i == (s - 1)) {
                if (highlight) {
                    sb.append(this.bold(this.export(l.get(i))));
                } else {
                    sb.append(this.export(l.get(i)));
                }
            } else if (i == (s - 2)) {
                if (highlight) {
                    sb.append(this.bold(this.export(l.get(i)) + placeholder));
                } else {
                    sb.append(this.export(l.get(i)) + placeholder);
                }
            } else {
                sb.append(this.export(l.get(i)) + placeholder);
            }
        }

        sb.append('\n');
        return sb.toString();
    }

    @Override
    public String irrSign() {
        return "~";
    }

    @Override
    public String italic(final String s) {
        return "<i>" + s + "</i>";
    }

    @Override
    public String jokerSign() {
        return "_";
    }

    @Override
    public String leftarrow() {
        return "&#8592;";
    }

    @Override
    public String leftrightarrow() {
        return "&#8596;";
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
        return "&le;";
    }

    @Override
    public String linebreak() {
        return "<br>";
    }

    @Override
    public String ltSign() {
        return "&lt;";
    }

    @Override
    public String math(final String s) {
        return s;
    }

    @Override
    public String mu() {
        return "&micro;";
    }

    @Override
    public String multSign() {
        return "&middot;";
    }

    @Override
    public String newline() {
        return "<br>";
    }

    @Override
    public String nonStrictRelativ() {
        return "&#8805;";
    }

    @Override
    public String notSign() {
        return "!";
    }

    @Override
    public String orSign() {
        return "&#8744;";
    }

    @Override
    public String paragraph() {
        return "<p>";
    }

    @Override
    public String pipeSign() {
        return "|";
    }

    @Override
    public String preFormatted(final String i) {
        return "<pre>" + i + "</pre>";
    }

    @Override
    public String quote(final String s) {
        return "<blockquote>" + s + "</blockquote>";
    }

    @Override
    public String reducesTo() {
        return "=";
    }

    @Override
    public String rightarrow() {
        return "&#8594;";
    }

    @Override
    public String set(final Collection c, final int type) {
        return HTML_Util.setHTML(c, type);
    }

    @Override
    public String sigma() {
        return "&#963;";
    }

    @Override
    public String sound() {
        return "&#8656;";
    }

    @Override
    public String strictRelativ() {
        return ">";
    }

    @Override
    public String sub(final String s) {
        return "<sub>" + s + "</sub>";
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
        return "<sup>" + s + "</sup>";
    }

    @Override
    public String table(final List<List<String>> rows) {
        final StringBuilder sb = new StringBuilder();
        sb.append("<table>\n");
        for (final List<String> row : rows) {
            sb.append(" <tr>\n");
            for (final String cellEntry : row) {
                sb.append("   <td>" + cellEntry + "</td>\n");
            }
            sb.append(" </tr>\n");
        }

        return sb.toString();
    }

    @Override
    public String tableEnd() {
        return "</table>";
    }

    @Override
    public String tableRow(final Collection<?> c) {
        final StringBuilder sb = new StringBuilder("<tr>");
        for (final Object obj : c) {
            sb.append("<td>");
            sb.append(this.export(obj));
            sb.append("</td>");
        }
        sb.append("</tr>\n");
        return sb.toString();
    }

    @Override
    public String tableStart(final int maxColumns) {
        return "<table>";
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
        return new StringHTML(o, true);
    }

    private String format(final String string) {
        if (string.length() == 1) {
            return "0" + string;
        }
        return string;
    }

    @Override
    public String isElement() {
        return "&isin;";
    }

    @Override
    public String Omega() {
        return "&Omega;";
    }
}
