package aprove.input.Programs.idp;

import java.util.regex.*;

/**
 * Handles escaping and unescaping of names for IDP/ITRS problems.
 */
public class EscapeHandler {

    /**
     * Match escape sequences.
     */
    final static Pattern escapePattern =
        Pattern.compile("(\\\\\\\\|\\\\\"|\\\\u[0-9a-fA-f]{4})");

    /**
     * Matches names, which are valid even unescaped
     */
    final static Pattern simpleNamePattern =
        Pattern.compile("^[a-zA-Z][_a-zA-Z0-9]*$");

    /**
     * Matches characters, which must be escaped
     */
    final static Pattern rawCharPattern =
        Pattern.compile("[\r\n\"\\\\]");

    public static String escape(String name) {
        Matcher m = EscapeHandler.simpleNamePattern.matcher(name);
        if (m.matches()) {
            return name;
        }

        m = EscapeHandler.rawCharPattern.matcher(name);
        StringBuffer sb = new StringBuffer();
        sb.append('"');
        while(m.find()) {
            String rawString = m.group();
            char rawChar = rawString.charAt(0);
            if (rawChar == '\\') {
                m.appendReplacement(sb, "\\\\\\\\");
            } else if (rawChar == '"') {
                m.appendReplacement(sb, "\\\\\"");
            } else {
                m.appendReplacement(sb, String.format("\\\\u%04x", (int)rawChar));
            }
        }
        m.appendTail(sb);
        sb.append('"');
        return sb.toString();
    }

    public static String unescape(String name) {
        if (!name.startsWith("\""))
         {
            return name; // name is not escaped
        }

        // remove '"'
        name = name.substring(1, name.length()-1);
        Matcher m = EscapeHandler.escapePattern.matcher(name);
        StringBuffer sb = new StringBuffer();
        while (m.find()) {
            String escape = m.group();
            if (escape.equals("\\\\")) {
                m.appendReplacement(sb, "\\\\");
            } else if (escape.equals("\\\"")) {
                m.appendReplacement(sb, "\"");
            } else if (escape.startsWith("\\u")) {
                int charCode = Integer.parseInt(escape.substring(2), 16);
                m.appendReplacement(sb, Character.toString((char) charCode));
            } else {
                /* this is a programming error (not an user error), as
                 * we should handle all escapes in escapePattern exhaustively.
                 */
                throw new RuntimeException(
                        "Unexpected Escape sequence \""+escape +"\"");
            }
        }
        m.appendTail(sb);
        return sb.toString();
    }

}
