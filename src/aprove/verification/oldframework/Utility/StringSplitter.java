package aprove.verification.oldframework.Utility;

import java.util.*;

public abstract class StringSplitter {

    /**
     * Splits a string into parts,
     * but not if the seperator occurs inside quotation marks (single and double)
     * @param str string to be split
     * @param sep character separating fields
     * @return List of Strings split according to the separator
     */
    public static List<String> splitNotQuoted(String str, char sep) {
        List<String> res = new LinkedList<String>();
        int level=0;
        StringBuilder strBuilder = new StringBuilder();
        for (char c : str.toCharArray()) {

            if ( (c == '"') || (c == '\'') ) {
                if ( (level == 0) || (level == c) ) {
                    level ^= c;
                }
            }
            if ( (c == sep) && (level == 0) ) {
                res.add(strBuilder.toString());
                strBuilder = new StringBuilder();
            }
            else {
                strBuilder.append(c);
            }
        }
        res.add(strBuilder.toString());
        return res;
    }

}
