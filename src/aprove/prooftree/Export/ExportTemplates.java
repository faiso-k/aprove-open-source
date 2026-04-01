package aprove.prooftree.Export;

/**
 * Class holding constant (string) templates needed when exporting proof trees.
 * @author Marc Brockschmidt
 */
public class ExportTemplates {
    protected final static String FRAME_HEAD_START =
        "<!DOCTYPE HTML PUBLIC \"-//W3C//DTD HTML 4.01 Frameset//EN\"\n"
        +"\"http:/www.w3.org/TR/html4/frameset.dtd\">\n<html>\n<head>\n<title>";


    protected final static String PROOF_HEAD_START =
        "<!DOCTYPE HTML PUBLIC \"-//W3C//DTD HTML 4.01 Transitional//EN\"\n"
        + "    \"http://www.w3.org/TR/html4/loose.dtd\">\n"
        + "<html>\n<head>\n"
        + "    <meta http-equiv=\"Content-Type\" content=\"text/html;charset=utf-8\" >";

    protected final static String RENDERDOT_SCRIPT = "<script type=\"text/javascript\" "
        + "src=\"http://aprove.informatik.rwth-aachen.de/renderdot/renderdot.js.php\"></script>";

    protected final static String HEAD_END = "</title>\n</head>\n";
    protected final static String HEAD_OPEN = "<head>\n";
    protected final static String HEAD_CLOSE = "</head>\n";
    protected final static String BODY_OPEN = "<body>\n";
    protected final static String BODY_CLOSE = "</body>\n";
    protected final static String HTML_OPEN = "<html>\n";
    protected final static String HTML_CLOSE = "</html>\n";
    protected final static String BREAK = "<BR>";

    protected final static String PRE_OPEN = "<pre>";
    protected final static String PRE_CLOSE = "</pre>";

    protected final static String SEP = System.getProperty("os.name").equals("Windows") ? "\\" : "/";

    protected final static String EDGE = "&#8627;";

    protected final static String STYLESHEET =
        "<style type=\"text/css\">"
        + "@media screen {\n"
        + "    div.embedding_pane {\n"
        + "      position: relative;\n"
        + "      width: 950px;\n"
        + "      height: 750px;\n"
        + "      border: 0;\n"
        + "      padding: 0;\n"
        + "      margin: 0;\n"
        + "    }\n"
        + "    div.navigation_pane, div.proof_pane {\n"
        + "      border: 0;\n"
        + "      margin: 0;\n"
        + "      padding: 0;\n"
        + "      height: 100%;\n"
        + "      overflow: auto;\n"
        + "      position: absolute;\n"
        + "    }\n"
        + "    div.navigation_pane {\n"
        + "      left: 0;\n"
        + "      width: 25%;\n"
        + "      background-color: #eee;\n"
        + "    }\n"
        + "    div.proof_pane {\n"
        + "      right: 0;\n"
        + "      width: 75%;\n"
        + "    }\n"
        + "    div.navigation {\n"
        + "      margin: 1ex;\n"
        + "    }\n"
        + "    div.proof, div.obligation {\n"
        + "      border: 1px solid black;\n"
        + "      margin: 1em;\n"
        + "      padding: 0.5ex;\n"
        + "    }\n"
        + "}\n"
        + "@media print {\n"
        + "    div.proof, div.obligation, div.navigation_pane {\n"
        + "      border-top: 2pt solid black;\n"
        + "      margin: 1em;\n"
        + "      padding: 0.5ex;\n"
        + "    }\n"
        + "    div.navigation_pane {\n"
        + "      border: 0;\n"
        + "    }\n"
        + "}\n"
        + ".color_red {\n"
        + "  color:#C00000;\n"
        + "}\n"
        + ".color_green {\n"
        + "  color:#00C000;\n"
        + "}\n"
        + ".color_yellow {\n"
        + "  color:#C0C000;\n"
        + "}\n"
        + ".color_black {\n"
        + "  color:#000000;\n"
        + "}\n"
        + "blockquote {\n"
        + "  margin-right: 0;\n"
        + "}\n"
        + "</style>\n";

    protected final static String STYLE_FULLSCREEN =
        "<style type=\"text/css\">"
        + "@media screen {\n"
        + "    div.embedding_pane, html, body {\n"
        + "      position: relative;\n"
        + "      width: 100%;\n"
        + "      height: 100%;\n"
        + "      border: 0;\n"
        + "      padding: 0;\n"
        + "      margin: 0;\n"
        + "    }\n"
        + "}\n"
        + "</style>\n";
}
