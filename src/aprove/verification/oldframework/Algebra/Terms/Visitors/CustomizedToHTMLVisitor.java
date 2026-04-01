package aprove.verification.oldframework.Algebra.Terms.Visitors;

import java.util.*;

import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Syntax.*;

/** Converts a Term into html allowing more control over the HTML tags than the
 * usual {@link ToHTMLVisitor} (most likely on the cost of beeing slower).
 *
 * To create a html visitor of your own it should be sufficent to extend
 * this visitor and overload some of the *Prefix or *Postfix methods to set
 * html tags that will be inserted before/after the corresponsing symbol/argument
 *
 * You may use the in* and out* methods as well.
 * @author Christian Kaeunicke
 * @version $Id$
 */
public class CustomizedToHTMLVisitor implements FineGrainedTermVisitor {
    public static String defaultColor = "#000000";
    public static String defaultVariableSymbolColor = "#CC8888";
    public static String defaultContructorSymbolColor = "#666600";
    public static String defaultTupleSymbolColor = "#006666";
    public static String defaultDefFunctionSymbolColor = "#000088";

    protected int lastFixity = SyntacticFunctionSymbol.NOTINFIX;
    protected Position pos; //counts from 0

    public CustomizedToHTMLVisitor() {
    this.pos = Position.create();
    };

    /*******************************************************************
     *                                                                 *
     * START --- methods that are intended to be overloaded --- START  *
     *                                                                 *
     *******************************************************************/

    /** this method is called whenever a variable symbol is about to be printed.
     * The string returned by this method will be put in front of the symbol itself.
     * This is the right place to place some FONT declarations.
     */
    public String variableSymbolPrefix(AlgebraVariable v) {
    return "<FONT COLOR=" + CustomizedToHTMLVisitor.defaultVariableSymbolColor + "><I>";
    }

    /** same as {@link #variableSymbolPrefix(AlgebraVariable)}, but the string returned by this function
     * will be put after the symbol. This makes this function the right place to close
     * any tags opened by the variableSymbolPrefix function.
     */
    public String variableSymbolPostfix(AlgebraVariable v) {
    return "</I></FONT>";
    };

    /** same as {@link #variableSymbolPrefix(AlgebraVariable)}, but for constructorApp symbols. */
    public String constructorAppSymbolPrefix(ConstructorApp c) {
        if (c.getSymbol() instanceof TupleSymbol) {
            return "<FONT COLOR=" + CustomizedToHTMLVisitor.defaultTupleSymbolColor + ">";
        } else {
            return "<FONT COLOR=" + CustomizedToHTMLVisitor.defaultContructorSymbolColor +  ">";
    }
    }

    /** same as {@link #variableSymbolPostfix(AlgebraVariable)}, but for constructorApp symbols. */
    public String constructorAppSymbolPostfix(ConstructorApp c) {
    return "</FONT>";
    };

    /** same as {@link #variableSymbolPrefix(AlgebraVariable)}, but for defFunctionApp symbols. */
    public String defFunctionAppSymbolPrefix(DefFunctionApp d) {
    return "<FONT COLOR=" + CustomizedToHTMLVisitor.defaultDefFunctionSymbolColor + ">";
    }

    /** same as {@link #variableSymbolPostfix(AlgebraVariable)}, but for defFunctionApp symbols. */
    public String defFunctionAppSymbolPostfix(DefFunctionApp d) {
    return "</FONT>";
    };

    /** this method is called once for every argument while processing a constructorApp
     * term. The string returned by this method will be printed before the argument gets
     * processed (after the comma or open round parenthesis). This is the right place to
     * place some FONT ... declarations meant to be valid for the whole argument and
     * all it's child terms.
     *
     * See {@link ToHighlightModeInfosInHTMLVisitor} for an example how to use it.
     */
    public String constructorAppArgumentPrefix(ConstructorApp c, int argumentPosition) {
    return "";
    }

    /** same as {@link #constructorAppArgumentPrefix(ConstructorApp, int)}, but the string returned by this function
     * will be put after the argument (and in front of the next comma or close round paranthesis.
     * This makes this function the right place to close any tags opened by the
     * constructorAppArgumentPrefix function.
     */
    public String constructorAppArgumentPostfix(ConstructorApp c, int argumentPosition) {
    return "";
    };

    /** same as {@link #constructorAppArgumentPrefix(ConstructorApp, int)}, but for arguments in DefFunctionApps */
    public String defFunctionAppArgumentPrefix(DefFunctionApp d, int argumentPosition) {
    return "";
    }

    /** same as {@link #constructorAppArgumentPostfix(ConstructorApp, int)}, but for arguments in DefFunctionApps */
    public String defFunctionAppArgumentPostfix(DefFunctionApp d, int argumentPosition) {
    return "";
    };

    /** default implementation of a "In-" function. Overload this method if something has
     * to be done every time an arbitrary term is enterd.
     */
    public String defaultIn(AlgebraTerm t) {
        return "";
    }

    /** same as {@link #defaultIn(AlgebraTerm)}, but called whenever a term if left */
    public String defaultOut(AlgebraTerm t) {
        return "";
    }

    /** this function is the first function that gets called when processing of a variable term
     * starts. Overload it, if you need anything done at this point.
     */
    public String inVariable(AlgebraVariable v) {
        return this.defaultIn(v);
    }

    /** same as {@link #inVariable(AlgebraVariable)}, but called as the last step in processing a variable. */
    public String outVariable(AlgebraVariable v) {
        return this.defaultOut(v);
    }

    /** same as {@link #inVariable(AlgebraVariable)}, but for constructorApps */
    public String inConstructorApp(ConstructorApp cterm) {
        return this.defaultIn(cterm);
    }

    /** same as {@link #outVariable(AlgebraVariable)}, but for constructorApps */
    public String outConstructorApp(ConstructorApp cterm) {
        return this.defaultOut(cterm);
    }

    /** same as {@link #inVariable(AlgebraVariable)}, but for defFunctionApps */
    public String inDefFunctionApp(DefFunctionApp fterm) {
        return this.defaultIn(fterm);
    }

    /** same as {@link #outVariable(AlgebraVariable)}, but for defFunctionApps */
    public String outDefFunctionApp(DefFunctionApp fterm) {
        return this.defaultOut(fterm);
    }

    /*******************************************************************
     *                                                                 *
     *  END  --- methods that are intended to be overloaded ---  END   *
     *                                                                 *
     *******************************************************************/

    /** helper method. */
    protected String functionAppSymbolPrefix(AlgebraFunctionApplication f) {
    if (f instanceof ConstructorApp) {
        return this.constructorAppSymbolPrefix((ConstructorApp) f);
    } else {
        return this.defFunctionAppSymbolPrefix ((DefFunctionApp) f);
    }
    };

    /** helper method. */
    protected String functionAppArgumentPrefix(AlgebraFunctionApplication f, int argumentPosition) {
    if (f instanceof ConstructorApp) {
        return this.constructorAppArgumentPrefix((ConstructorApp) f, argumentPosition);
    } else {
        return this.defFunctionAppArgumentPrefix ((DefFunctionApp) f, argumentPosition);
    }
    };

    /** helper method. */
    protected String functionAppSymbolPostfix(AlgebraFunctionApplication f) {
    if (f instanceof ConstructorApp) {
        return this.constructorAppSymbolPostfix((ConstructorApp) f);
    } else {
        return this.defFunctionAppSymbolPostfix ((DefFunctionApp) f);
    }
    };

    /** helper method. */
    protected String functionAppArgumentPostfix(AlgebraFunctionApplication f, int argumentPosition) {
    if (f instanceof ConstructorApp) {
        return this.constructorAppArgumentPostfix((ConstructorApp) f, argumentPosition);
    } else {
        return this.defFunctionAppArgumentPostfix ((DefFunctionApp) f, argumentPosition);
    }
    };

    @Override
    public Object caseVariable(AlgebraVariable v) {
        String forReturn = this.inVariable(v);
        forReturn += this.variableSymbolPrefix(v) + ToHTMLVisitor.escape(v.getName()) + this.variableSymbolPostfix(v);
        forReturn += this.outVariable(v);
    return forReturn;
    }

    @Override
    public Object caseDefFunctionApp(DefFunctionApp d) {
    String forReturn = this.inDefFunctionApp(d);
    forReturn += this.handleFunctionApp(d);
    forReturn += this.outDefFunctionApp(d);
    return forReturn;
    }

    @Override
    public Object caseConstructorApp(ConstructorApp c) {
    String forReturn = this.inConstructorApp(c);
    forReturn += this.handleFunctionApp(c);
    forReturn += this.outConstructorApp(c);
    return forReturn;
    }

    protected Object handleFunctionApp(AlgebraFunctionApplication f) {
        SyntacticFunctionSymbol fsym =  (SyntacticFunctionSymbol)f.getSymbol();
    StringBuffer forReturn = new StringBuffer();
    if (fsym.isInfix()) {
        boolean needsBraces = this.lastFixity != SyntacticFunctionSymbol.NOTINFIX;
        this.lastFixity = fsym.getFixity();

        if (needsBraces) {
            forReturn.append("(");
        }

        String argumentPrefix = this.functionAppArgumentPrefix(f, 0);
        String argumentPostfix = this.functionAppArgumentPostfix(f, 0);
        this.pos.add(0);
        forReturn.append(argumentPrefix + (String) f.getArgument(0).apply(this) + argumentPostfix);
        this.pos = this.pos.pred();

        forReturn.append(" " + this.functionAppSymbolPrefix(f) + ToHTMLVisitor.escape(fsym.getName()) + this.functionAppSymbolPostfix(f) + " ");

        this.lastFixity = fsym.getFixity(); // set again cause changes in recursive calls

        argumentPrefix = this.functionAppArgumentPrefix(f, 1);
        argumentPostfix = this.functionAppArgumentPostfix(f, 1);
        this.pos.add(1);
        forReturn.append(argumentPrefix + (String) f.getArgument(1).apply(this) + argumentPostfix);
        this.pos = this.pos.pred();

        if (needsBraces) {
            forReturn.append(")");
        }
    } else {
        forReturn.append(this.functionAppSymbolPrefix(f) + ToHTMLVisitor.escape(fsym.getName()) + this.functionAppSymbolPostfix(f));
        List<AlgebraTerm> args = f.getArguments();
        if (fsym.getArity() > 0) {
        forReturn.append("(");
        ListIterator iterator = args.listIterator();
        while (iterator.hasNext()) {
            // apply this visitor to arguments
            AlgebraTerm t =  (AlgebraTerm) iterator.next();
            int argPos = iterator.previousIndex();
            this.lastFixity = SyntacticFunctionSymbol.NOTINFIX;

            String argumentPrefix = this.functionAppArgumentPrefix(f, argPos);
            String argumentPostfix = this.functionAppArgumentPostfix(f, argPos);
            this.pos.add(argPos);
            String argumentString = (String) t.apply(this);
            this.pos = this.pos.pred();

            forReturn.append(argumentPrefix + argumentString + argumentPostfix);
            if (iterator.hasNext()) {
                forReturn.append(", ");
            }
        }
        forReturn.append(")");
        }
    }
        return forReturn.toString();
    }


    @Override
    public Object caseMetaFunctionApplication(MetaFunctionApplication metaFunctionApplication) {
        return null;
    }

    public static String apply(AlgebraTerm t) {
        return (String) t.apply(new CustomizedToHTMLVisitor());
    }
}
