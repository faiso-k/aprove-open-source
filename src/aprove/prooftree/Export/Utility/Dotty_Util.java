/**
 * @author prometheus
 * @version $Id$
*/

package aprove.prooftree.Export.Utility;

/**
 * Export_Util class for exporting the node-text in graphs (such as the Graphs
 * in the java-framework)
 * @author prometheus
 */
public class Dotty_Util extends PLAIN_Util {

    @Override
    public String linebreak() {
        return "\\n";
    }

    @Override
    public String newline() {
        return "\\n\\n";
    }

    //TODO prometheus Check whatelse we might want to override!
}
