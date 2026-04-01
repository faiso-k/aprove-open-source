package aprove.strategies.Parameters;

import java.io.*;
import java.util.logging.*;

import org.antlr.runtime.*;

import aprove.input.Generated.Strategy.*;
import aprove.input.Programs.Strategy.*;
import aprove.strategies.UserStrategies.*;

public class StrategyTranslator {
    private static final Logger log = Logger.getLogger("aprove.input.Strategy.Parser");

    private static StrategyProgram stddef = null;

    private synchronized static StrategyProgram getStdDef() {
        if (StrategyTranslator.stddef == null) {
            StrategyParser parser =
                StrategyTranslator.buildParser(StrategyTranslator.inputForModule("aprove.Modules.std"));
            RawModule strategy;
            try {
                strategy = parser.strategy();
            } catch (RecognitionException e) {
                throw new StrategyParseException(e, parser);
            }
            StrategyBuilder builder = new StrategyBuilder(strategy);
            StrategyTranslator.stddef = builder.buildProgram();
            if (StrategyTranslator.hasProblems(parser)) {
                StrategyTranslator.stddef.parseError();
            }
        }
        return StrategyTranslator.stddef;
    }

    private static ANTLRStringStream inputForModule(String moduleName) {
        InputStream stream = ModulePath.moduleAsStream(moduleName);
        ANTLRStringStream input;
        try {
            input = new ANTLRInputStream(stream);
            input.name = "module " + moduleName;
        } catch (IOException e) {
            throw new StrategyParseException(e);
        }
        return input;
    }

    public static StrategyProgram strategyFromModule(String moduleName) {
        return StrategyTranslator.strategy(StrategyTranslator.inputForModule(moduleName));
    }

    public static StrategyProgram strategy(File stratFile) {
        CharStream input;
        try {
            input = new ANTLRFileStream(stratFile.getPath());
        } catch (IOException e) {
            throw new StrategyParseException(e);
        }
        return StrategyTranslator.strategy(input);
    }

    public static StrategyProgram strategy(String strategy) {
        ANTLRStringStream input = new ANTLRStringStream(strategy);
        input.name = "<string input>";
        return StrategyTranslator.strategy(input);
    }

    public static StrategyProgram strategy(Reader reader, String name) {
        ANTLRStringStream input;
        try {
            input = new ANTLRReaderStream(reader);
        } catch (IOException e) {
            throw new StrategyParseException(e);
        }
        input.name = name;
        return StrategyTranslator.strategy(input);
    }

    public static UserStrategy strategyFragment(String fragment) {
        ANTLRStringStream input = new ANTLRStringStream(fragment);
        input.name = "<string input>";
        StrategyParser parser = StrategyTranslator.buildParser(input);
        StrategyExpression expression;
        try {
            expression = parser.expression();
        } catch (RecognitionException e) {
            throw new StrategyParseException(e, parser);
        }
        if (StrategyTranslator.hasProblems(parser)) {
            throw new IllegalArgumentException("Error parsing strategy fragment (see log)");
        }
        return StrategyBuilder.exprToUser(expression);
    }

    public static ParamValue value(String someValue) {
        ANTLRStringStream input = new ANTLRStringStream(someValue);
        input.name = "<string input>";
        StrategyParser parser = StrategyTranslator.buildParser(input);
        Value value;
        try {
            value = parser.value();
        } catch (RecognitionException e) {
            throw new StrategyParseException(e, parser);
        }
        if (StrategyTranslator.hasProblems(parser)) {
            throw new IllegalArgumentException("Error parsing strategy fragment (see log)");
        }
        return StrategyBuilder.freeze(value);
    }

    /**
     * Returns a StrategyProgram containing just the definition from std.strategy
     */
    public static StrategyProgram standardProgram() {
        return StrategyTranslator.getStdDef();
    }

    private static StrategyProgram strategy(CharStream input) {
        StrategyParser parser = StrategyTranslator.buildParser(input);
        RawModule strategy;
        try {
            strategy = parser.strategy();
        } catch (RecognitionException e) {
            throw new StrategyParseException(e, parser);
        }
        StrategyBuilder builder = new StrategyBuilder(strategy);
        StrategyProgram result = builder.buildProgramWithDefaults(StrategyTranslator.getStdDef());
        if (StrategyTranslator.hasProblems(parser)) {
            result.parseError();
        }
        return result;
    }

    private static StrategyParser buildParser(CharStream input) {
        StrategyLexer lexer = new StrategyLexer(input);
        CommonTokenStream tokens = new CommonTokenStream(lexer);
        StrategyParser parser = new StrategyParser(tokens);
        return parser;
    }

    private static boolean hasProblems(StrategyParser parser) {
        Token nextToken = parser.getTokenStream().LT(1);
        if (nextToken.getType() != Token.EOF) {
            StrategyTranslator.log.severe("Unhandled input in strategy parser for "+parser.getSourceName()+":\n" +
                    "  Parsing stopped in line " + nextToken.getLine() +
                    " before " + parser.getTokenErrorDisplay(nextToken));
            return true;
        }

        return false;
    }
}
