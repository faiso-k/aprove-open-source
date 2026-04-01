package aprove.prooftree.Export.Utility;

import java.util.*;

import aprove.verification.oldframework.Rewriting.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * @author Achim Luecking
 * @version $Id$
 */
public class LaTeX_Util extends Export_Util{


    @Override
    public String allQuantor() {
        return "\\forall{}";
    }

    @Override
    public String existQuantor() {
        return "\\exists{}";
    }

    @Override
    public String implication() {
        return "\\Longrightarrow{}";
    }

    @Override
    public String nonStrictRelativ(){
        return "\\succsim{}";
    }

   @Override
    public String strictRelativ(){
       // FIXME: what is the command?
        return "\\succ{}";
    }

    @Override
    public String reducesTo(){
        return "="; //\\twoheadrightarrow{}";
    }

    @Override
    public String notSign(){
        return "\\neg";
    }

    @Override
    public String orSign(){
        return "\\vee{}";
    }

    @Override
    public String andSign(){
        return "\\wedge{}";
    }


    public static final int SCGRAPHS = 6;

    /**
     * table entries are Strings for:
     * 1. Empty Collection
     * 2. Begin Collection
     * 3. Begin Item
     * 4. End Item
     * 5. Seperator between two Items
     * 6. End Collection
     */

    private static final String[][] layouts = new String [][] {
        {"$$\\emptyset$$","$$\\left\\{","",""," , ","\\right\\}$$"}, // 0. SIMPLESET
        {"","\\begin{enumerate}","\\item","","\n","\\end{enumerate}"}, // 1. ENUMERATE
        {"none","\\begin{quote}","","","\\\\\n","\\end{quote}"}, // 2. BLOCKQUOTE
        {"","\\begin{itemize}","\\item","","","\\end{itemize}"}, // 3. ITEMIZE
        //        {"","\\begin{itemize}","\\item","","\\\\n","\\end{itemize}"}, // 3. ITEMIZE
        {"none","\\begin{longtable}{rcl}","","","\\\\\n","\\end{longtable}"}, // 4. RULES
        {"none","\\begin{eqnarray}","","","\\\\\n","\\end{eqnarray}"}, // 5. NUMERATED_RULES
        {"","\\begin{center}","","","\\hspace{5ex}\n","\\end{center}"}, // 6. CENTER/SCGRAPHS
        {"","","","","","",""}, // 7. TABLEROWS
        {"","\\begin{tabular}","","","","\\\\\n","\\end{tabular}"}, // 8. TABLE
        {"none", "$$", "", "", " , ", "$$"},  // 9. NICE_SET
        {"none", "", "", "", "", ""}, //10. CONCATENATE
        {"none", "", "", "", " || ", ""}, //11. PARALLEL
        {"$$\\emptyset$$","$$\\left\\{","",""," , ","\\right\\}$$"}, // 12. = 0.
        {"", " \\[ ", "", "", " \\wedge ", " \\] "}, // 13. PACOND
        {"", " \\[ ", "", "", " \\wedge ", " \\] "} // 14. PACONDDOT
    };


    public LaTeX_Util(){}

    public static String setSCGraph(final Set set){
          return LaTeX_Util.setLaTeX(set, LaTeX_Util.SCGRAPHS);
    }

    public static String setESCGraph(final Set set){
      return LaTeX_Util.setLaTeX(set, LaTeX_Util.SCGRAPHS);
    }

    public static String setUsableRules(final Set<Rule> rules) {
      return LaTeX_Util.setLaTeX(rules,Export_Util.RULES);
    }

    // TODO
    public static String setShowMappings(final Set showMappings) {
      return "ShowMappings";
    }

    public static String setLaTeX(final Collection c) {
          return LaTeX_Util.setLaTeX(c,Export_Util.SIMPLESET);
    }

    public static String setEnumerate(final Collection c) {
      return LaTeX_Util.setLaTeX(c,Export_Util.ENUMERATE);
    }

        public static String setBlockquote(final Collection c) {
          return LaTeX_Util.setLaTeX(c,Export_Util.BLOCKQUOTE);
    }


        public static String setLaTeX(final Collection<?> c, final int type){
        LaTeX_Able o;
        final String [] layout = LaTeX_Util.layouts[type];
        if (c.isEmpty()) {
            return layout[Export_Util.EMPTY_ENTRY];
        }
        final StringBuilder sb = new StringBuilder();
        sb.append(layout[Export_Util.BEGINCOL_ENTRY]+"\n");
        final Iterator<?> i = c.iterator();
        while (i.hasNext()) {
            o = LaTeX_Util.safeLaTeX(i.next());
            String temp =  o.toLaTeX();

            if (type == Export_Util.NUMERATED_RULES) {
                temp = temp.replace('$',' ');
            }
            sb.append(layout[Export_Util.BEGINITEM_ENTRY] + temp);
            if (i.hasNext()) {
                sb.append(layout[Export_Util.SEPERATE_ENTRY]);
            }
        }
        sb.append("\n"+layout[Export_Util.ENDCOL_ENTRY]+"\n");
        return sb.toString();
    }

    @Override
    public String export(final Object o) {
      final LaTeX_Able e = LaTeX_Util.safeLaTeX(o);
      return e.toLaTeX();
    }

    @Override
    public String set(final Collection c, final int type){
      return LaTeX_Util.setLaTeX(c,type);
    }

    @Override
    public String bold(final String s){
      return "\\textbf{"+s+"}";
    }

    @Override
    public String italic(final String s){
      return "\\textit{"+s+"}";
    }

    @Override
    public String linebreak(){
      return "\n\n";
    }

    @Override
    public String cond_linebreak(){
        return ""; //'cause LaTeX does not like too many linebreaks..
    }

    @Override
    public String paragraph(){
      return "\n\n";
    }

        @Override
        public String newline() {
       return "\\medskip \n";
        }

    @Override
    public String index(final List<?> l, final boolean highlight) {
        final StringBuilder sb = new StringBuilder();
        final String placeholder = "$\\rightarrow$";
        final int s = l.size();
        for (int i=0; i<s; i++) {
            if (i == (s-2)) {
                if (highlight) {
                    sb.append(this.bold("\\textbf{"+l.get(i)+"}"+placeholder));
                } else {
                    sb.append("\\textbf{"+l.get(i)+"}"+placeholder);
                }
            } else if (i == (s-1)) {
                if (highlight) {
                    sb.append(this.bold("\\textbf{"+l.get(i)+"}"));
                } else {
                    sb.append("\\textbf{"+l.get(i)+"}");
                }
            } else {
                sb.append(this.bold("\\textbf{"+l.get(i)+"}"+placeholder));
            }
        }
        sb.append(" \\\\ \n");
        return sb.toString();
    }

    @Override
    public String quote(final String s){
      return "\\begin{quote}\n"+s+"\n\\end{quote}\n";
    }

    @Override
    public String fontcolor(final String s, final Color color){
      return s;
    }

    @Override
    public String fontColorCode(final String s, final int color){
      return s;
    }

    @Override
    public String sup(final String s){
      return "\\mbox{$^{"+s+"}$}";
    }

    @Override
    public String sub(final String s){
      return "\\mbox{$_{"+s+"}$}";
    }
    @Override
    public String calligraphic(final String s){
      return "\\cal{"+s+"}";
    }

    @Override
    public String math(final String s){
      return " $"+s+"$ ";
    }

        @Override
        public String hline(){
          return "\n\\hrule\n";
        }

        @Override
        public String tttext(final String text){
          return "\\texttt{"+text+"}";
        }

        @Override
        public String verb(final String text){
          return "\\verb|"+text+"|";
        }

    @Override
    public String succ(){
    return "\\succ{}";
    }

    @Override
    public String succeq(){
    return "\\succeq{}";
    }

    @Override
    public String leftarrow(){
        return "\\mbox{$\\revTo$}";
    }

    @Override
    public String rightarrow(){
    return "\\mbox{$\\to$}";
    }

    @Override
    public String leftrightarrow(){
        return "\\mbox{$\\leftrightarrow$}";
    }

    @Override
    public String colon() {
        return "\\mbox{$:$}";
    }

    @Override
    public String probabilistiChoiceOperator() {
        return "\\mbox{$\\mid\\mid$}";
    }


    public String cite(final String cite){
    return "\\cite{"+cite+"}";
    }

    @Override
    public String indent(final String text) {
    return text;
    }

    /**
     * if object implements toLaTeX then this will be used,
     * else if object implements Exportable, export will be used,
     * otherwise toString will be used for toLaTeX
     */
    private static LaTeX_Able safeLaTeX(final Object o) {
        //System.out.println("------------------------------------");
        //System.out.println("Calling LaTeX export on "+o.getClass());
        //System.out.println(o.toString());
        //System.out.println("------------------------------------");
        if (o instanceof LaTeX_Able) {
            return ((LaTeX_Able) o);
        }
        if (o instanceof Exportable) {
            return new StringLaTeX( ((Exportable) o).export(new LaTeX_Util()), true);
        }
        /**
         * Workaround stuff. The assumption, that Strings are passed
         * unescaped, is widely used. So we exclude Strings from escaping. */
        if (o instanceof String) {
            return new StringLaTeX(o, true);
        }
        return new StringLaTeX(o, false);
    }

    @Override
    public String atSign(){
       return "@";
    }

    @Override
    public String irrSign(){
       return "\\propto{}";
    }

    @Override
    public String jokerSign(){
       return "\\_";
    }

    @Override
    public String appSpace(){
       return "\\;";
    }

    @Override
    public String backslash(){
       return "\\setminus{}";
    }

    @Override
    public String multSign() {
        return "";
    }

    @Override
    public String eqSign() {
        return "=";
    }

    @Override
    public String geSign() {
        return "\\ge";
    }

    @Override
    public String gtSign() {
        return ">";
    }

    @Override
    public String leSign() {
        return "\\le";
    }

    @Override
    public String ltSign() {
        return "<";
    }

    @Override
    public String sigma() {
        return "\\sigma";
    }

    @Override
    public String mu() {
        return "\\mu";
    }

    @Override
    public String pipeSign() {
        return "\\textbar";
    }

    @Override
    public String escape(final String raw) {
        return StringLaTeX.escape(raw);
    }

    @Override
    public Object wrapAsRaw(final Object o) {
        return new StringLaTeX(o, true);
    }

    @Override
    public String haskellIf(final StringBuffer cond,final StringBuffer tc,final StringBuffer fc){
       final StringBuffer o = new StringBuffer();
       o.append("\\hsraise{\\hsraise{\\hsraise{"+this.haskellKeyWord("if")+"\\;}{");
       o.append(cond);
       o.append("}{\\;"+this.haskellKeyWord("then")+"\\;}}{");
       o.append(tc);
       o.append("}{\\;"+this.haskellKeyWord("else")+"\\;}}{");
       o.append(fc);
       o.append("}");
       return o.toString();
    }

    @Override
    public String haskellLet(final List<StringBuffer> locals,final StringBuffer res){
        final StringBuffer o = new StringBuffer();
        o.append("\\begin{array}{ll}\n");
        o.append(this.haskellKeyWord("let"));
        o.append("\\\\\n");
        for (final StringBuffer local : locals){
            o.append("&");
            o.append(local);
            o.append("\\\\\n");
        }
        o.append("\\multicolumn{2}{l}{");
        o.append(this.haskellKeyWord("in"));
        o.append("\\;");
        o.append(res);
        o.append("}\\\\\n");
        o.append("\\end{array}\n");
        return o.toString();
    }

    @Override
    public String haskellWhere(final List<StringBuffer> locals,final StringBuffer res){
        final StringBuffer o = new StringBuffer();
        o.append("\\begin{array}[t]{l@{}l}\n");
        o.append("\\multicolumn{2}{l}{");
        o.append(res);
        o.append("}\\\\\n");
        o.append("\\multicolumn{2}{l}{");
        o.append("\\;\\;");
        o.append(this.haskellKeyWord("where"));
        o.append("}\\\\\n");
        for (final StringBuffer local : locals){
            o.append("\\;\\;\\;&");
            o.append(local);
            o.append("\\\\\n");
        }
        o.append("\\end{array}\n");
        return o.toString();
    }

    @Override
    public String haskellCase(final StringBuffer arg,final List<Pair<StringBuffer,StringBuffer>> cases){
        final StringBuffer o = new StringBuffer();
        o.append("\\hsraise{"+this.haskellKeyWord("case")+"}{"+arg+"}"+this.haskellKeyWord("of")+"\\\\");
        o.append("\\begin{array}{l@{}l@{}l}\n");
        for (final Pair<StringBuffer,StringBuffer> c : cases){
            o.append("\\hspace*{1cm}");
            o.append("&");
            o.append(c.getKey());
            o.append("&");
            o.append(c.getValue());
            o.append("\\\\\n");
        }
        o.append("\\end{array}\n");
        return o.toString();
    }

    @Override
    public String haskellCond(final List<Pair<StringBuffer,StringBuffer>> crs,final String arrow){
        final StringBuffer o = new StringBuffer();
        o.append("\\begin{array}[t]{l@{}l@{}l@{}l}\n");
        for (final Pair<StringBuffer,StringBuffer> c : crs){
            if (c.getKey() != null) {
                o.append("|\\;&");
                o.append("\\hslow{");
                o.append(c.getKey());
                o.append("}");
            } else {
               o.append("&");
            }
            o.append("&\\;");
            o.append(arrow);
            o.append("\\;&\\hslow{");
            o.append(c.getValue());
            o.append("}\\\\\n");
        }
        o.append("\\end{array}\n");
        return o.toString();
    }

    @Override
    public String haskellNoCond(final StringBuffer res,final String arrow){
        final StringBuffer o = new StringBuffer();
        o.append("\\;");
        o.append(arrow);
        o.append("\\;\\hslow{");
        o.append(res);
        o.append("}");
        return o.toString();
    }

    @Override
    public String haskellRules(final StringBuffer name,final List<Pair<StringBuffer,StringBuffer>> rules){
       final StringBuffer o = new StringBuffer();
       o.append("\\begin{array}{l@{}l@{}l}");
       for (final Pair<StringBuffer,StringBuffer> r : rules){
            o.append(name);
            o.append("\\;&");
            o.append(r.getKey());
            o.append("&\\hslow{");
            o.append(r.getValue());
            o.append("}\\\\\n");
       }
       o.append("\\end{array}\n");
       return o.toString();
    }

    @Override
    public String haskellVar(final String text){
       return text;
    }

    @Override
    public String haskellCons(final String text){
       return "\\mbox{\\tt "+text+"}";
    }

    @Override
    public String haskellKeyWord(final String text){
       return "\\mbox{\\tt "+text+"}";
    }

    @Override
    public String idpCCGE() {
        return "\\idpCCGE";
    }

    @Override
    public String idpCCGT() {
        return "\\idpCCGT";
    }

    @Override
    public String idpCCWGT() {
        return "\\idpCCWGT";
    }

    @Override
    public String idpItpfEq() {
        return "\\idpItpfEq";
    }

    @Override
    public String idpItpfTo() {
        return "\\idpItpfTo";
    }

    @Override
    public String idpItpfToPlus() {
        return "\\idpItpfToPlus";
    }

    @Override
    public String idpItpfToTrans() {
        return "\\idpItpfToTrans";
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String body(final String string) {
        return string;
    }

    @Override
    public String tableStart(final int maxColumns) {
        if (aprove.Globals.useAssertions) {
            assert maxColumns > 0;
        }
        final StringBuilder sb = new StringBuilder("\\begin{tabular}{");
        sb.append('l');
        for (int i = 1; i < maxColumns; ++i) {
            sb.append('r');
        }
        sb.append("}\n");
        return sb.toString();
    }

    @Override
    public String tableRow(final Collection<?> c) {
        final StringBuilder sb = new StringBuilder();
        final Iterator<?> iter = c.iterator();
        while (iter.hasNext()) {
            final Object element = iter.next();
            sb.append(this.export(element));
            if (iter.hasNext()) {
                sb.append(" & ");
            }
            else {
                sb.append("\\\\\n");
            }
        }
        return sb.toString();
    }

    @Override
    public String tableEnd() {
        return "\\end{tabular}";
    }


    @Override
    public String table(final List<List<String>> rows) {

        //First, get column number:
        int maxColumnNumber = 0;
        for (final List<String> row : rows) {
            final int columnNumber = row.size();
            if (columnNumber > maxColumnNumber) {
                maxColumnNumber = columnNumber;
            }
        }

        final StringBuilder sb = new StringBuilder();
        sb.append(this.tableStart(maxColumnNumber));
        for (final List<String> row : rows) {
            sb.append(this.tableRow(row));
        }
        sb.append(this.tableEnd());

        return sb.toString();
    }

    /**
     * @return \frac{a}{b}.
     * @param numerator the numerator.
     * @param denominator the denominator.
     */
    @Override
    public String fraction(final String numerator, final String denominator) {
        final StringBuilder sb = new StringBuilder("$\\frac{");
        sb.append(numerator);
        sb.append("}{");
        sb.append(denominator);
        sb.append("}$");
        return sb.toString();
    }

    @Override
    public String preFormatted(final String i) {
        throw new UnsupportedOperationException("preFormatted output not implemented for LaTeX output.");
    }

    @Override
    public String complete() {
        return "\\Longleftarrow{}";
    }

    @Override
    public String equivalent() {
        return "\\Longleftrightarrow{}";
    }

    @Override
    public String sound() {
        return "\\Longrightarrow{}";
    }

    @Override
    public String isElement() {
        return "\\in";
    }

    @Override
    public String Omega() {
        return "\\Omega";
    }

}

/*
 * @author Achim Luecking
 * implements the LaTeX_Able Interface for any type, toString is used for toLaTeX
 */
class StringLaTeX implements LaTeX_Able {

    final Object o;
    final boolean raw;

    public StringLaTeX(final Object o, final boolean raw) {
        this.o = o;
        this.raw = raw;
    }

    /**
     * @param o Object to wrap
     * @param raw Interpret data as raw LaTeX (true) or plain text (false)
     */
    @Override
    public String toLaTeX() {
        if (this.raw) {
            return this.o.toString();
        } else {
            return StringLaTeX.escape(this.o.toString());
        }
    }

    static String escape(final String raw) {
        final int l = raw.length();
        final StringBuffer out = new StringBuffer(l);
        for (int i=0;i<l;i++){
            final char c = raw.charAt(i);
            switch(c){
               case '$' : out.append("\\${}"); break;
               case '#' : out.append("\\#{}"); break;
               case '_' : out.append("\\_{}"); break;
               case '&' : out.append("\\&{}"); break;
               case '{' : out.append("\\{{}"); break;
               case '}' : out.append("\\}{}"); break;
               case '\\': out.append("\\backslash{}"); break;
               case '%' : out.append("\\%{}"); break;
               case '`' : out.append("\\symbol{39}"); break;
               default: out.append(c); break;
            }
        }
        return out.toString();
    }
}
