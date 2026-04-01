package aprove.prooftree.Export.Utility;

import java.util.*;

import aprove.verification.oldframework.Haskell.*;
import aprove.verification.oldframework.Haskell.Modules.Module;
import aprove.verification.oldframework.Haskell.Visitors.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * @author Achim Luecking
 * @version $Id$
 */
public abstract class Export_Util {

    // TODO (noschinski): Document the new semantics of escaping.

    public static enum Color {
        BLACK,
        RED,
        GREEN,
        YELLOW,
        BLUE,
        GRAY,
        DARKBLUE,
        BROWN
    }

    public static final int SIMPLESET = 0;
    public static final int ENUMERATE = 1;
    public static final int BLOCKQUOTE = 2;
    public static final int ITEMIZE = 3;
    public static final int RULES = 4;
    public static final int NUMERATED_RULES = 5;
    public static final int CENTER = 6;
    public static final int TABLEROWS = 7;
    public static final int TABLE = 8;
    public static final int NICE_SET = 9;
    public static final int CONCATENATE = 10;
    public static final int PARALLEL = 11;
    public static final int NICE_SIMPLE = 12;
    public static final int PACOND = 13;
    public static final int PACONDDOT = 14;


    public static final String[][] layouts = new String [][]{};

    public static final int EMPTY_ENTRY = 0;
    public static final int BEGINCOL_ENTRY = 1;
    public static final int BEGINITEM_ENTRY = 2;
    public static final int ENDITEM_ENTRY = 3;
    public static final int SEPERATE_ENTRY = 4;
    public static final int ENDCOL_ENTRY = 5;

    public abstract String export(Object o);
    public abstract String set(Collection<?> c, int type);
    public abstract String bold(String s);
    public abstract String italic(String s);
    public abstract String allQuantor();
    public abstract String existQuantor();
    public abstract String implication();
    public abstract String sound();
    public abstract String complete();
    public abstract String equivalent();
    public abstract String orSign();
    public abstract String andSign();
    public abstract String notSign();
    public abstract String nonStrictRelativ();
    public abstract String strictRelativ();
    public abstract String reducesTo();
    public abstract String linebreak();
    public abstract String cond_linebreak(); // conditional linebreak: real linebreak in HTML_Util, empty String in LaTeX_Util (cause LaTeX does not like to many linebreaks.. ;-) )
    public abstract String paragraph();
    public abstract String newline();
    public abstract String index(List<?> l, boolean highlight); // highlight determines if last entry of List l should be highlighted
    public abstract String quote(String s);
    public abstract String fontcolor(String s, Color color);
    public abstract String fontColorCode(final String s, final int color);
    public abstract String sup(String s);
    public abstract String sub(String s);
    public abstract String calligraphic(String s);
    public abstract String math(String s);
    public abstract String hline();
    public abstract String tttext(String text);
    public abstract String verb(String text);
    public abstract String succ();
    public abstract String succeq();
    public abstract String leftarrow();
    public abstract String rightarrow();
    public abstract String leftrightarrow();
    public abstract String colon();
    public abstract String probabilistiChoiceOperator();
    public abstract String indent(String text);
    public abstract String atSign();
    public abstract String irrSign();
    public abstract String jokerSign();
    public abstract String appSpace();
    public abstract String backslash();
    public abstract String multSign();
    public abstract String eqSign();
    public abstract String geSign();
    public abstract String gtSign();
    public abstract String leSign();
    public abstract String ltSign();
    public abstract String sigma();
    public abstract String mu();
    public abstract String pipeSign();
    public abstract String fraction(String numerator, String denominator);
    public abstract String isElement();
    public abstract String Omega();

    public abstract String idpCCGE();
    public abstract String idpCCGT();
    public abstract String idpCCWGT();
    public abstract String idpItpfTo();
    public abstract String idpItpfToPlus();
    public abstract String idpItpfToTrans();
    public abstract String idpItpfEq();


    /**
     * Display a pre-formatted (that is, whitespace-based formatting like
     * indenting) string properly.
     * @param i The pre-formatted input
     * @return Some representation that the input is displayed as it was intended
     */
    public abstract String preFormatted(String i);

    /**
     * Wraps object to disable escaping.
     *
     * <p>Wraps the <code>o</code> into another object, so that
     * <code>o.toString()</code> is considered as formatted, not as plain
     * text. This is done by implementing the $FOO_Able interface for the
     * $FOO_Util (e.g. HTML_Able for HTML_Util).
     *
     * <p>This can be used if e.g. HTML_Util.set() shall be called with a
     * list of Strings containing HTML, which should be interpreted. Without
     * this method, HTML_Util would escape the embedde HTML code. By
     * applying this method to each list member, this can be prevented</p>
     *
     * <p>FIXME: It would be nice, if StringHTML, StringPLAIN, ... had
     * a common base class besides Object, so we could return something
     * more specific ...</p>
     */
    public abstract Object wrapAsRaw(Object o);

    /**
     * Escape all special chars in a string.
     *
     * <p>
     * Intention of this method: Put any plain text string into a
     * LaTeX, HTML, whatever document without needing to worry about
     * characters which may have a meaning in the output format. This
     * method is <em>not</em> intended to be a formatter, so linebreaks
     * et. al have to be inserted by the according methods.
     * </p>
     *
     * <p>
     * For e.g. HTML this means replacing &lt;, &gt, &amp; by
     * &amp;lt;, &amp;gt; &amp;amp;.
     * </p>
     */
    public abstract String escape(String raw);

    // table* was primarily written as a quick hack for visualizing
    // matrix interpretations
    public abstract String tableStart(int maxColumns);

    /**
     * @param c positive number that specifies how many columns
     *  the table may have
     * @return
     */
    public abstract String tableRow(Collection<?> c);
    public abstract String tableEnd();

    public String cite(final Citation cite) {
        return this.export("["+cite.toString()+"]");
    }

    public String cite(final Citation[] cites) {
        return this.cite(Arrays.asList(cites));
    }

    public String cite(final Collection<Citation> cites) {
        if (cites.isEmpty()) {
            return "";
        }
        final StringBuilder sb = new StringBuilder();
        sb.append('[');
        final Iterator<Citation> it = cites.iterator();
        while (it.hasNext()) {
            final Citation cite = it.next();
            sb.append(cite.toString());
            if (it.hasNext()) {
                sb.append(',');
            }
        }
        sb.append(']');
        return this.export(sb.toString());
    }

    public String haskellObject(final HaskellObject ho, final Module module){
        return (new ExportVisitor(module.getModules(), module, this, new StringBuffer())).applyTo(ho);
    }

    public abstract String haskellLet(List<StringBuffer> locals,StringBuffer res);
    public abstract String haskellWhere(List<StringBuffer> locals,StringBuffer res);
    public abstract String haskellIf(StringBuffer cond,StringBuffer tc,StringBuffer fc);
    public abstract String haskellCase(StringBuffer arg,List<Pair<StringBuffer,StringBuffer>> cases);
    public abstract String haskellRules(StringBuffer name,List<Pair<StringBuffer,StringBuffer>> rules);
    public abstract String haskellCond(List<Pair<StringBuffer,StringBuffer>> crs,String arrow);
    public abstract String haskellNoCond(StringBuffer res,String arrow);
    public abstract String haskellVar(String text);
    public abstract String haskellCons(String text);
    public abstract String haskellKeyWord(String text);

    /** exports a List of exportable Objects to a humand readable enumeration of the general form
     * a, b, c, ... and z using closingWord as seperator between the second last and the last word.
     * @param list list of objects to be enumerated. Objects are converted into Strings by the
     * export method
     * @param closingWord seperator between the second last and the last word
     */
    public String exportToEnumeratingText(final Collection list, final String closingWord) {
        final StringBuilder forReturn = new StringBuilder();
        int i = 0;
        final int n = list.size();
        for (final Object elem : list) {
            i++;
            if (i != 1) {
                if (i == n) {
                    forReturn.append(closingWord + " ");
                } else {
                    forReturn.append(", ");
                }
            }
            forReturn.append(this.export(elem));
        }
        return forReturn.toString();
    }

    public abstract String body(String string);

    /**
     * @param rows quadratic matrix of entries for a table
     * @return matrix formated as table (left-aligned cell entries)
     */
    public abstract String table(List<List<String>> rows);

}
