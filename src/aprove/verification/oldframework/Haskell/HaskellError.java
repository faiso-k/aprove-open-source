package aprove.verification.oldframework.Haskell;

import aprove.input.Generated.haskell.node.*;

/**
 * @author Stephan Swiderski
 * @version $Id$
 *
 * HaskellError is a RuntimeException for all errors occuring in the Haskell framework.
 */
public class HaskellError extends RuntimeException {
    Token tok;
    String message;

    public static Object lastObject;
    public static boolean output;

    public HaskellError(Token tok,String message){
        this.tok = tok;
    this.message = message;
    }

    public Token getToken(){
        return this.tok;
    }

    @Override
    public String getMessage(){
        return this.message;
    }

    /**
     * throws a HaskellError and use the token of the given HaskellObjeck as errorpoint
     */
    public static void output(HaskellObject ho, String message){
        Token tok = null;
        if (ho != null) {
             tok = ho.getToken();
        }
        HaskellError.output(tok,message);
    }

    /**
     * throws a HaskellError and use the token to refer to a line in the code
     */
    public static void output(Token tok, String message){
        String pos = tok != null ? "\""+tok.getText().replace("\0", "{start term}")+"\" at ["+tok.getLine()+","+tok.getPos()+"] : " : "";
        HaskellError he = new HaskellError(tok,message);

        System.out.println(pos + message);

        HaskellSym.showe(HaskellError.lastObject);
        he.printStackTrace();
        throw he;
    }

    /**
     * println for Debug
     */
    public static void println(String m){
        if (HaskellError.output){
       System.out.println(m);
    }

    }

}