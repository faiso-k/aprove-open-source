/*
 * Created on 18.03.2003
 */
package aprove.prooftree.Export.Utility;


/*
 * @author thiemann
 * implents the HTML_Able Interface for any type, toString is used for toHTML
 */
class StringHTML implements HTML_Able {

    final Object o;
    final boolean raw;

    /**
     * @param o Object to wrap
     * @param raw Interpret data as raw HTML (true) or plain text (false)
     */
    StringHTML(Object o, boolean raw) {
        this.o = o;
        this.raw = raw;
    }

    @Override
    public String toHTML() {
        if(this.o != null) {
            if (this.raw) {
                return this.o.toString();
            } else {
                return StringHTML.escape(this.o.toString());
            }
        }else{
            return "";
        }
    }

    static String escape(String raw) {
        return raw.replace("&", "&amp;")
                  .replace(">", "&gt;")
                  .replace("<", "&lt;");
    }

}
