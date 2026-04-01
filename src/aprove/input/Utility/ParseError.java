package aprove.input.Utility;


public class ParseError {
    final public static int HINT = 10;
    final public static int WARNING = 20;
    final public static int VARIABLE_CONDITION_VIOLATED = 21;
    final public static int ERROR = 30;

    protected String filename = null;
    protected int level = ParseError.ERROR;
    protected int line = 0;
    protected int column = 0;
    protected String message = null;
    protected String token = null;

    public ParseError() {
    }

    public ParseError(int l) {
    this.level = l;
    }

    public ParseError(int l, String fn, int li, int co, String msg, String tkn) {
    this.level = l;
    this.filename = fn;
    this.line = li;
    this.column = co;
    this.message = msg;
    this.token = tkn;
    }

    public void setMessage(String s) {
    this.message = s;
    }

    public String getMessage() {
    return this.message;
    }

    public int getLevel() {
    return this.level;
    }

    public void setFileName(String s) {
    this.filename = s;
    }

    public String getFileName() {
    return this.filename;
    }

    public void setColumn(int i) {
    this.column = i;
    }

    public int getColumn() {
    return this.column;
    }

    public void setLine(int i) {
    this.line = i;
    }

    public int getLine() {
    return this.line;
    }

    public void setPosition(int l, int c) {
    this.line = l;
    this.column = c;
    }

    public void setToken(String s) {
    this.token = s;
    }

    public String getToken() {
    return this.token;
    }

    @Override
    public String toString() {
    String s = "";
    switch (this.level) {
        case HINT:
        s += "HINT";
        break;
        case WARNING:
        s += "WARNING";
        break;
        case ERROR:
        s += "ERROR";
        break;
        default:
        s += "SOMETHING";
    }
    if (this.line != 0) {
        if (this.column != 0) {
        s += " at ["+this.line+","+this.column+"]";
        }
        else {
        s += " at line "+this.line;
        }
    }
    else {
        if (this.column != 0) {
        s += " at column "+this.column;
        }
    }
    if (this.filename != null) {
        s += " in file ''"+this.filename+"''";
    }
    if (this.token != null) {
        s += " ''"+this.token+"''";
    }
    s += ": "+this.message;
    return s;
    }
}
