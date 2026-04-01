package aprove.input.Programs.llvm.problems;

import aprove.input.Programs.llvm.parseStructures.exceptions.*;
import aprove.input.Programs.llvm.utils.*;
import aprove.prooftree.Export.Utility.*;
import aprove.verification.oldframework.Input.*;
import immutables.*;

/**
 * Specifies the start state (by a function name and argument types) to be analyzed for an LLVM program.
 * @author CryingShadow, ffrohn
 */
public class LLVMQuery implements Immutable, Exportable {

    /**
     * The character sequence terminating a block comment in C.
     */
    private static final String C_CLOSING_BLOCK_COMMENT = "*/";

    /**
     * The character sequence starting a line comment in C.
     */
    private static final String C_COMMENT = "//";

    /**
     * The character sequence starting a block comment in C.
     */
    private static final String C_OPENING_BLOCK_COMMENT = "/*";

    /**
     * The character starting a line comment in LLVM.
     */
    private static final String LLVM_COMMENT = ";";

    /**
     * The keyword starting a memory safety query for LLVM or C programs.
     */
    private static final String MEMSAFETY_KEYWORD = "safety:";

    /**
     * The keyword starting a termination query for LLVM or C programs.
     */
    private static final String TERMINATION_KEYWORD = "query:";

    /**
     * @param query The query String (usually the first line of the program file or a special parameter String).
     * @return The parsed LLVMQuery containing the function to call, it's argument types, and the analysis goal.
     * @throws LLVMParseException If some error occurs during parsing.
     */
    @SuppressWarnings("unused")
    public static LLVMQuery parseQuery(String query) throws LLVMParseException {
        String trimmed = query.trim();
        if (!LLVMQuery.queryMightBeValid(trimmed)) {
            if (LLVMDebuggingFlags.SV_COMP_MODE || LLVMDebuggingFlags.TERMCOMP_MODE) {
                return new LLVMQuery("main", new LLVMQueryInputType[0], HandlingMode.Termination);
            } else {
                throw new LLVMParseException("First line must contain the starting query as a comment!");
            }
        }
        String toParse = LLVMQuery.removeComments(trimmed);
        HandlingMode handlingMode = LLVMQuery.parseHandlingMode(toParse);
        toParse = LLVMQuery.removeHandlingMode(toParse, handlingMode);
        int open = toParse.indexOf('(');
        String function = toParse.substring(0, open);
        String arguments = toParse.substring(open + 1);
        int lastChar = arguments.length() - 1;
        if (arguments.charAt(lastChar) != ')') {
            throw new LLVMParseException("Starting query must end with a closing paranthesis!");
        }
        String justArguments = arguments.substring(0, lastChar);
        if ("".equals(justArguments)) {
            return new LLVMQuery(function, new LLVMQueryInputType[0], handlingMode);
        } else {
            String[] args = justArguments.split(",");
            LLVMQueryInputType[] argTypes = new LLVMQueryInputType[args.length];
            for (int i = 0; i < args.length; i++) {
                argTypes[i] = LLVMQuery.parseQueryInputType(args[i]);
            }
            return new LLVMQuery(function, argTypes, handlingMode);
        }
    }

    /**
     * @param query The query String.
     * @return The parsed handling mode specified by the query.
     * @throws LLVMParseException If the handling mode specified by the query is unknown.
     */
    private static HandlingMode parseHandlingMode(String query) throws LLVMParseException {
        if (query.startsWith(LLVMQuery.TERMINATION_KEYWORD)) {
            return HandlingMode.Termination;
        } else if (query.startsWith(LLVMQuery.MEMSAFETY_KEYWORD)) {
            return HandlingMode.MemorySafety;
        } else {
            throw new LLVMParseException("Unknown handling mode in query!");
        }
    }

    /**
     * @param arg The argument String.
     * @return The QueryInputType parsed from the argument String.
     * @throws LLVMParseException If the argument String does not match the format for an argument String.
     */
    private static LLVMQueryInputType parseQueryInputType(String arg) throws LLVMParseException {
        for (LLVMIntAnnotation a : LLVMIntAnnotation.values()) {
            if (a.getRepresentation().equals(arg)) {
                return LLVMQueryInputType.createIntType(a);
            }
        }
        if (LLVMQueryInputType.STRING.equals(arg)) {
            return LLVMQueryInputType.createStringType();
        } else if (LLVMQueryInputType.ALLOCATION.equals(arg)) {
            return LLVMQueryInputType.createAllocationType(0, false);
        } else if (arg.startsWith(LLVMQueryInputType.ALLOCATION + "(") && arg.endsWith(")")) {
            String param = arg.substring(6, arg.length() - 1);
            if (param.startsWith("#")) {
                // allocation of at least the size of another argument
                try {
                    return LLVMQueryInputType.createAllocationType(Integer.parseInt(param.substring(1)), true);
                } catch (NumberFormatException e) {
                    throw new LLVMParseException("Cannot parse argument number in allocation!");
                }
            } else {
                // allocation of at least a given constant size
                try {
                    return LLVMQueryInputType.createAllocationType(Integer.parseInt(param), false);
                } catch (NumberFormatException e) {
                    // allocation of a named area - other arguments may be in the same area
                    return LLVMQueryInputType.createNamedAllocationType(param);
                }
            }
        } else if (arg.startsWith(LLVMQueryInputType.STRING + "(") && arg.endsWith(")")) {
            // TODO String with extra allocated area after terminating zero of size specified within paranthesis
            String param = arg.substring(7, arg.length() - 1);
            if (param.startsWith("#")) {
                // String with at least the size of another argument of allocated space after terminating 0
                try {
                    return LLVMQueryInputType.createStringType(Integer.parseInt(param.substring(1)), true);
                } catch (NumberFormatException e) {
                    throw new LLVMParseException("Cannot parse argument number in String!");
                }
            } else {
                // String with at least a constant size of allocated space after terminating 0
                try {
                    return LLVMQueryInputType.createStringType(Integer.parseInt(param), false);
                } catch (NumberFormatException e) {
                    throw new LLVMParseException("Cannot parse constant number in String!");
                }
            }
        } else if (arg.endsWith("]")) {
            // array type
            int lastOpenBracket = arg.lastIndexOf('[');
            if (lastOpenBracket < 3) {
                throw new LLVMParseException("Unsupported input type!");
            }
            String arrayTypeString = arg.substring(0, lastOpenBracket);
            String sizeString = arg.substring(lastOpenBracket + 1, arg.length() - 1);
            if (sizeString.equals("")) {
                return LLVMQueryInputType.createArrayType(LLVMQuery.parseQueryInputType(arrayTypeString));
            } else if (sizeString.startsWith("#")) {
                // array of at least the size of another argument
                try {
                    return
                        LLVMQueryInputType.createArrayType(
                            LLVMQuery.parseQueryInputType(arrayTypeString),
                            Integer.parseInt(sizeString.substring(1)),
                            true
                        );
                } catch (NumberFormatException e) {
                    throw new LLVMParseException("Cannot parse argument number in array!");
                }
            } else {
                // array of at least a given constant size
                try {
                    return
                        LLVMQueryInputType.createArrayType(
                            LLVMQuery.parseQueryInputType(arrayTypeString),
                            Integer.parseInt(sizeString),
                            false
                        );
                } catch (NumberFormatException e) {
                    throw new LLVMParseException("Cannot parse argument number in array!");
                }
            }
        }
        // TODO add more cases
        throw new LLVMParseException("Unsupported input type!");
    }

    /**
     * @param query A String possibly holding a query.
     * @return True if the String is long enough to contain a query and it starts with one of the query keywords.
     */
    private static boolean queryMightBeValid(String query) {
        // the shortest possible query has length 12 ("; query: f()")
        return
            query != null && query.length() >= 12
            && (query.contains(LLVMQuery.TERMINATION_KEYWORD) || query.contains(LLVMQuery.MEMSAFETY_KEYWORD));
    }

    /**
     * @param query The query String.
     * @return The query String without leading (and possibly trailing) comment markers.
     */
    private static String removeComments(String query) {
        if (query.startsWith(LLVMQuery.LLVM_COMMENT)) {
            return query.substring(LLVMQuery.LLVM_COMMENT.length()).trim();
        } else if (query.startsWith(LLVMQuery.C_COMMENT)) {
            return query.substring(LLVMQuery.C_COMMENT.length()).trim();
        } else if (query.startsWith(LLVMQuery.C_OPENING_BLOCK_COMMENT)) {
            assert (query.endsWith(LLVMQuery.C_CLOSING_BLOCK_COMMENT)) : "Block comment is not terminated!";
            return
                query.substring(
                    LLVMQuery.C_OPENING_BLOCK_COMMENT.length(),
                    query.length() - LLVMQuery.C_CLOSING_BLOCK_COMMENT.length()
                ).trim();
        } else {
            return query;
        }
    }

    /**
     * @param query The query String (without comment markers).
     * @param handlingMode The handling mode to remove from the beginning of the query String.
     * @return The remaining query String after the handling mode has been removed. In effect, this method just removes
     *         as many characters from the beginning of the query String as the specified handling mode indicates and
     *         then trims the resulting String.
     */
    private static String removeHandlingMode(String query, HandlingMode handlingMode) {
        switch (handlingMode) {
            case Termination:
                return query.substring(LLVMQuery.TERMINATION_KEYWORD.length()).trim();
            case MemorySafety:
                return query.substring(LLVMQuery.MEMSAFETY_KEYWORD.length()).trim();
            default:
                throw new IllegalStateException("Someone found a new analysis goal for LLVM programs...");
        }
    }

    /**
     * The types of the arguments of the starting function.
     */
    private final LLVMQueryInputType[] arguments;

    /**
     * The function to call in the starting state.
     */
    private final String functionName;

    /**
     * The handling mode (termination or memory safety) specified by this query.
     */
    private final HandlingMode handlingMode;

    /**
     * @param name The function to call in the start state.
     * @param args The types of the arguments of the start function.
     * @param handlingMode The analysis goal (termination or memory safety) for this query.
     */
    public LLVMQuery(String name, LLVMQueryInputType[] args, HandlingMode handlingMode) {
        this.functionName = name;
        this.arguments = args;
        this.handlingMode = handlingMode;
    }

    /* (non-Javadoc)
     * @see aprove.prooftree.Export.Utility.Exportable#export(aprove.prooftree.Export.Utility.Export_Util)
     */
    @Override
    public String export(Export_Util o) {
        StringBuilder res = new StringBuilder("Analyze ");
        res.append(this.getHandlingMode().export(o));
        res.append(" of all function calls matching the pattern:");
        res.append(o.linebreak());
        res.append(this.getFunction());
        res.append("(");
        boolean first = true;
        for (LLVMQueryInputType t : this.arguments) {
            if (first) {
                first = false;
            } else {
                res.append(", ");
            }
            res.append(t.export(o));
        }
        res.append(")");
        return res.toString();
    }

    /**
     * @return The function to call in the starting state.
     */
    public String getFunction() {
        return this.functionName;
    }

    /**
     * @return The analysis goal (termination or memory safety) for this query.
     */
    public HandlingMode getHandlingMode() {
        return this.handlingMode;
    }

    /**
     * @param index The index of the argument.
     * @return The type of the specified argument.
     */
    public LLVMQueryInputType getType(final int index) {
        return this.arguments[index];
    }

    /**
     * @return True iff this query is the default query for analyzing main() for termination.
     */
    public boolean isMain() {
        return
            this.functionName.equals("main")
            && this.arguments.length == 0
            && this.handlingMode == HandlingMode.Termination;
    }

}
