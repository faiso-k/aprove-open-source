package aprove.verification.oldframework.Algebra.Terms.Visitors;

import java.util.*;

import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Syntax.*;

/** Converts a Term into a String.
 * @author Burak Emir
 * @version $Id$
 */
public class ToHASKELLVisitor implements CoarseGrainedTermVisitor {

    public static final String[] KEYWORDS = {
        "map",
        "concat",
        "filter",
        "head",
        "last",
        "tail",
        "init",
        "null",
        "length",
        "foldl",
        "foldl1",
        "scanl",
        "scanl1",
        "foldr",
        "foldr1",
        "scanr",
        "scanr1",
        "iterate",
        "repeat",
        "replicate",
        "cycle",
        "take",
        "drop",
        "splitAt",
        "takeWhile",
        "dropWhile",
        "span",
        "break",
        "lines",
        "words",
        "unlines",
        "unwords",
        "reverse",
        "and",
        "or",
        "any",
        "all",
        "elem",
        "notElem",
        "lookup",
        "sum",
        "product",
        "maximum",
        "minimum",
        "concatMap",
        "zip",
        "zip3",
        "zipWith",
        "zipWith3",
        "unzip",
        "unzip3",
        "ReadS",
        "ShowS",
        "Read",
        "readsPrec",
        "readList",
        "Show",
        "show",
        "showsPrec",
        "showList",
        "reads",
        "shows",
        "read",
        "lex",
        "showChar",
        "showString",
        "readParen",
        "showParen",
        "FilePath",
        "IOError",
        "ioError",
        "userError",
        "catch",
        "putChar",
        "putStr",
        "putStrLn",
        "print",
        "getChar",
        "getLine",
        "getContents",
        "interact",
        "readFile",
        "writeFile",
        "appendFile",
        "readIO",
        "readLn",
        "Ix",
        "range",
        "index",
        "inRange",
        "rangeSize",
        "isAscii",
        "isControl",
        "isPrint",
        "isSpace",
        "isUpper",
        "isLower",
        "isAlpha",
        "isDigit",
        "isOctDigit",
        "isHexDigit",
        "isAlphaNum",
        "digitToInt",
        "intToDigit",
        "toUpper",
        "toLower",
        "ord",
        "chr",
        "readLitChar",
        "showLitChar",
        "lexLitChar",
        "showSigned",
        "showInt",
        "readSigned",
        "readInt",
        "readDec",
        "readOct",
        "readHex",
        "readFloat",
        "readDigits",
        "Ratio",
        "Rational",
        "numerator",
        "denominator",
        "approxRational",
        "IO",
        "IOResult",
        "primExitWith",
        "Addr",
        "Bool",
        "True",
        "False",
        "Maybe",
        "Nothing",
        "Just",
        "Either",
        "Left",
        "Right",
        "Ordering",
        "LT",
        "EQ",
        "GT",
        "Char",
        "String",
        "Int",
        "Integer",
        "Float",
        "Double",
        "IO",
        "Rec",
        "EmptyRec",
        "EmptyRow",
        "Eq",
        "Ord",
        "compare",
        "max",
        "min",
        "Enum",
        "succ",
        "pred",
        "toEnum",
        "fromEnum",
        "enumFrom",
        "enumFromThen",
        "enumFromTo",
        "enumFromThenTo",
        "Bounded",
        "minBound",
        "maxBound",
        "Num",
        "negate",
        "abs",
        "signum",
        "fromInteger",
        "fromInt",
        "Real",
        "toRational",
        "Integral",
        "quot",
        "rem",
        "div",
        "mod",
        "quotRem",
        "divMod",
        "even",
        "odd",
        "toInteger",
        "toInt",
        "Fractional",
        "recip",
        "fromRational",
        "fromDouble",
        "Floating",
        "pi",
        "exp",
        "log",
        "sqrt",
        "logBase",
        "sin",
        "cos",
        "tan",
        "asin",
        "acos",
        "atan",
        "sinh",
        "cosh",
        "tanh",
        "asinh",
        "acosh",
        "atanh",
        "RealFrac",
        "properFraction",
        "truncate",
        "round",
        "ceiling",
        "floor",
        "floatRadix",
        "floatDigits",
        "floatRange",
        "decodeFloat",
        "encodeFloat",
        "exponent",
        "significand",
        "scaleFloat",
        "isNaN",
        "isInfinite",
        "isDenomalized",
        "isIEEE",
        "isNegativeZero",
        "atan2",
        "Monad",
        "return",
        "fail",
        "Functor",
        "fmap",
        "mapM",
        "mapM_",
        "sequence",
        "sequence_",
        "maybe",
        "either",
        "not",
        "otherwise",
        "subtract",
        "even",
        "odd",
        "gcd",
        "lcm",
        "fromIntegral",
        "realToFrac",
        "fst",
        "snd",
        "curry",
        "uncurry",
        "id",
        "const",
        "flip",
        "until",
        "asTypeOf",
        "error",
        "undefined",
        "seq",
        "class",
        "where",
        "infixl",
        "infixr",
        "data",
        "type",
        "let",
        "module",
        "import",
        "deriving",
        "do",
        "case",
        "if",
        "then",
        "else",
    };

    public static Set<String> keywords = null;

    private static boolean numeric(String s) {
        for (int i = 0; i < s.length(); i++) {
            if (Character.getType(s.charAt(i)) != Character.DECIMAL_DIGIT_NUMBER) {
                return false;
            }
        }
        return true;
    }

    public static String escape(Symbol sym) {
        if (ToHASKELLVisitor.keywords == null) {
            ToHASKELLVisitor.keywords = new LinkedHashSet<String>();
            for (int i = 0; i < ToHASKELLVisitor.KEYWORDS.length; i++) {
                ToHASKELLVisitor.keywords.add(ToHASKELLVisitor.KEYWORDS[i]);
            }
        }
        String name = sym.getName();
        if (sym instanceof ConstructorSymbol) {
            String new_name = Character.toUpperCase(name.charAt(0))+name.substring(1, name.length());
            if (ToHASKELLVisitor.keywords.contains(new_name) || ToHASKELLVisitor.numeric(name)) {
                return "C"+name;
            }
            return new_name;
        } else if (sym instanceof DefFunctionSymbol) {
            String new_name = Character.toLowerCase(name.charAt(0))+name.substring(1, name.length());
            if (ToHASKELLVisitor.keywords.contains(new_name) || ToHASKELLVisitor.numeric(name)) {
                return "d"+name;
            }
            return new_name;
        } else if (sym instanceof VariableSymbol) {
            String new_name = Character.toLowerCase(name.charAt(0))+name.substring(1, name.length());
            if (ToHASKELLVisitor.keywords.contains(new_name) || ToHASKELLVisitor.numeric(name)) {
                return "v"+name;
            }
            return new_name;
        }
        return name;
    }

    @Override
    public Object caseVariable(AlgebraVariable v) {
        return ToHASKELLVisitor.escape(v.getSymbol());
    }

    @Override
    public Object caseFunctionApp(AlgebraFunctionApplication f) {
        List<AlgebraTerm> args = f.getArguments();
        SyntacticFunctionSymbol fsym =  (SyntacticFunctionSymbol)f.getSymbol();
        StringBuffer res;
        if (fsym.getArity() == 0) {
            return ToHASKELLVisitor.escape(fsym);
        } else {
            res = new StringBuffer();
            res.append("("+ToHASKELLVisitor.escape(fsym));
            Iterator i = args.iterator();
            while (i.hasNext()) {
                // apply this visitor to arguments
                AlgebraTerm t =  (AlgebraTerm)i.next();
                String temp = (String)t.apply(this);
                res.append(" "+temp);
            }
            res.append(")");
        }
        return res.toString();
    }

    public static String apply(AlgebraTerm t) {
        return (String)t.apply(new ToHASKELLVisitor());
    }

}
