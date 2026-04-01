package aprove.input;

import java.io.*;
import java.util.*;
import java.util.logging.*;

import aprove.*;
import aprove.strategies.Parameters.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.BasicStructures.Rule;
import aprove.verification.dpframework.DPConstraints.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.dpframework.TRSProblem.*;
import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Input.*;
import aprove.verification.oldframework.Logic.Formulas.*;
import aprove.verification.oldframework.Rewriting.*;
import immutables.*;

/**
 * Collection of static methods for parsing strings and files. Derived from
 * AProVE_TestCase of Testing package fame.
 * @author Peter Schneider-Kamp
 * @version $Id$
 */

public class EasyInput {

    private static final Logger log = Logger.getLogger("aprove.input.EasyInput");

    /**
     * Loads a sorted (C)TRS from a file.
     */
    final static public Program loadSTRS(final String srcfile) {
        final ProgramTranslator trans =
            new aprove.input.Programs.strs.Translator();
        try {
            final BufferedReader buffer =
                new BufferedReader(new FileReader(srcfile));
            buffer.mark(1024 * 1024);
            trans.translate(buffer);
            trans.throwOnError();
        } catch (final Exception e) {
            throw new RuntimeException("could not load from '" + srcfile
                + "'\n" + e.getMessage());
        }
        return trans.getProgram();
    }

    /**
     * Parses a sorted (C)TRS from a string.
     */
    final static public Program parseSTRS(final String program) {
        final ProgramTranslator trans =
            new aprove.input.Programs.strs.Translator();
        try {
            trans.translate(program);
            trans.throwOnError();
        } catch (final Exception e) {
            throw new RuntimeException("could not parse '" + program + "'\n"
                + e.getMessage());
        }
        return trans.getProgram();
    }

    /**
     * Loads a fp program from a file.
     */
    final static public Program loadFP(final String srcfile) {
        final ProgramTranslator trans =
            new aprove.input.Programs.fp.Translator();
        try {
            final BufferedReader buffer =
                new BufferedReader(new FileReader(srcfile));
            buffer.mark(1024 * 1024);
            trans.translate(buffer);
            trans.throwOnError();
        } catch (final Exception e) {
            throw new RuntimeException("could not load from '" + srcfile
                + "'\n" + e.getMessage());
        }
        return trans.getProgram();
    }

    /**
     * Parses a fp program from a string.
     */
    final static public Program parseFP(final String program) {
        final ProgramTranslator trans =
            new aprove.input.Programs.fp.Translator();
        try {
            trans.translate(program);
            trans.throwOnError();
        } catch (final Exception e) {
            throw new RuntimeException("could not parse '" + program + "'\n"
                + e.getMessage());
        }
        return trans.getProgram();
    }

    /**
     * Loads a srs program from a file.
     */
    final static public Program loadSRS(final String srcfile) {
        final ProgramTranslator trans =
            new aprove.input.Programs.srs.Translator();
        try {
            trans.translate(new File(srcfile));
            trans.throwOnError();
        } catch (final Exception e) {
            e.printStackTrace();
            throw new RuntimeException("could not load from '" + srcfile
                + "'\n" + e.getMessage());
        }
        return trans.getProgram();
    }

    /**
     * Parses a srs program from a string.
     */
    final static public Program parseSRS(final String program) {
        final ProgramTranslator trans =
            new aprove.input.Programs.srs.Translator();
        try {
            trans.translate(program);
            trans.throwOnError();
        } catch (final Exception e) {
            throw new RuntimeException("could not parse '" + program + "'\n"
                + e.getMessage());
        }
        return trans.getProgram();
    }

    /**
     * Loads a tes program from a file.
     */
    final static public Program loadTES(final String srcfile) {
        final ProgramTranslator trans =
            new aprove.input.Programs.tes.Translator();
        try {
            trans.translate(new File(srcfile));
            trans.throwOnError();
        } catch (final Exception e) {
            e.printStackTrace();
            throw new RuntimeException("could not load from '" + srcfile
                + "'\n" + e.getMessage());
        }
        return trans.getProgram();
    }

    /**
     * Parses a tes program from a string.
     */
    final static public Program parseTES(final String program) {
        final ProgramTranslator trans =
            new aprove.input.Programs.tes.Translator();
        try {
            trans.translate(program);
            trans.throwOnError();
        } catch (final Exception e) {
            throw new RuntimeException("could not parse '" + program + "'\n"
                + e.getMessage());
        }
        return trans.getProgram();
    }

    /**
     * Loads a ttt program from a file.
     */
    final static public Program loadTTT(final String srcfile) {
        final ProgramTranslator trans =
            new aprove.input.Programs.ttt.Translator();
        try {
            trans.translate(new File(srcfile));
            trans.throwOnError();
        } catch (final Exception e) {
            e.printStackTrace();
            throw new RuntimeException("could not load from '" + srcfile
                + "'\n" + e.getMessage());
        }
        return trans.getProgram();
    }

    /**
     * Parses a ttt program from a string.
     */
    final static public Program parseTTT(final String program) {
        final ProgramTranslator trans =
            new aprove.input.Programs.ttt.Translator();
        try {
            trans.translate(program);
            trans.throwOnError();
        } catch (final Exception e) {
            throw new RuntimeException("could not parse '" + program + "'\n"
                + e.getMessage());
        }
        return trans.getProgram();
    }

    /**
     * Loads a IPAD program from a file.
     */
    final static public Program loadIPAD(final String srcfile) {
        final ProgramTranslator trans =
            new aprove.input.Programs.ipad.Translator();
        try {
            trans.translate(new File(srcfile));
            trans.throwOnError();
        } catch (final Exception e) {
            e.printStackTrace();
            throw new RuntimeException("could not load from '" + srcfile
                + "'\n" + e.getMessage());
        }
        return trans.getProgram();
    }

    /**
     * Parses a IPAD program from a string.
     */
    final static public Program parseIPAD(final String program) {
        final ProgramTranslator trans =
            new aprove.input.Programs.ipad.Translator();
        try {
            trans.translate(program);
            trans.throwOnError();
        } catch (final Exception e) {
            throw new RuntimeException("could not parse '" + program + "'\n"
                + e.getMessage());
        }
        return trans.getProgram();
    }

    /**
     * Loads a XSRS program from a file.
     */
    final static public Program loadXSRS(final String srcfile) {
        final ProgramTranslator trans =
            new aprove.input.Programs.xsrs.Translator();
        try {
            trans.translate(new File(srcfile));
            trans.throwOnError();
        } catch (final Exception e) {
            e.printStackTrace();
            throw new RuntimeException("could not load from '" + srcfile
                + "'\n" + e.getMessage());
        }
        return trans.getProgram();
    }

    /**
     * Parses a XSRS program from a string.
     */
    final static public Program parseXSRS(final String program) {
        final ProgramTranslator trans =
            new aprove.input.Programs.xsrs.Translator();
        try {
            trans.translate(program);
            trans.throwOnError();
        } catch (final Exception e) {
            throw new RuntimeException("could not parse '" + program + "'\n"
                + e.getMessage());
        }
        return trans.getProgram();
    }

    /**
     * Loads a formula from a file.
     */
    final static public Formula loadPL(final Program p, final String srcfile) {
        final FormulaTranslator trans =
            new aprove.input.Formulas.pl.Translator();
        trans.setContext(p);
        try {
            trans.translate(new File(srcfile));
        } catch (final Exception e) {
            throw new RuntimeException("could not load from '" + srcfile
                + "'\n" + e.getMessage());
        }
        return null; //trans.getFormula();
    }

    /**
     * Parses a formula from a string.
     */
    final static public Formula parsePL(final Program p, final String formula) {
        final FormulaTranslator trans =
            new aprove.input.Formulas.pl.Translator();
        trans.setContext(p);
        try {
            trans.translate(formula);
        } catch (final Exception e) {
            throw new RuntimeException("could not parse '" + formula + "'\n"
                + e.getMessage());
        }
        return trans.getFormula();
    }

    /**
     * Loads a term from a file.
     */
    final static public AlgebraTerm loadTERM(final Program p, final String srcfile) {
        final TermTranslator trans =
            new aprove.input.Terms.term.Translator();
        trans.setContext(p);
        try {
            trans.translate(new File(srcfile));
        } catch (final Exception e) {
            throw new RuntimeException("could not load from '" + srcfile
                + "'\n" + e.getMessage());
        }
        return trans.getTerm();
    }

    /**
     * Parses a term from a string.
     */
    final static public AlgebraTerm parseTERM(final Program p, final String term) {
        final TermTranslator trans =
            new aprove.input.Terms.term.Translator();
        trans.setContext(p);
        try {
            trans.translate(term);
        } catch (final Exception e) {
            throw new RuntimeException("could not parse '" + term + "'\n"
                + e.getMessage());
        }
        return trans.getTerm();
    }

    /**
     * Parses strategies from a string
     */
    final static public StrategyProgram parseStrategy(final String strategyString) {
        return StrategyTranslator.strategy(strategyString);
    }

    /**
     * Parses strategies from a stream
     */
    final static public StrategyProgram parseStrategy(final Input strategyInput) {
        return StrategyTranslator.strategy(strategyInput.getContent(), strategyInput.getName());
    }

    /**
     * Parses strategies from a file
     */
    final static public StrategyProgram loadStrategy(final String sourceFile) {
        return StrategyTranslator.strategy(new File(sourceFile));
    }

    /**
     * Parses strategy module from aprove.predefinedstrategies
     * @param ModuleName
     */
    final static public StrategyProgram loadStrategyModule(final String moduleName) {
        return StrategyTranslator.strategyFromModule(moduleName);
    }

    private static final Object interpretAsConstraint(final aprove.verification.dpframework.BasicStructures.TRSTerm t) {
        if (t.isVariable()) {
            return t;
        } else {
            final aprove.verification.dpframework.BasicStructures.TRSFunctionApplication fa =
                (aprove.verification.dpframework.BasicStructures.TRSFunctionApplication) t;
            if (fa.getRootSymbol().getName().equals("&")) {
                final List<aprove.verification.dpframework.DPConstraints.Constraint> cs =
                    new LinkedList<aprove.verification.dpframework.DPConstraints.Constraint>();
                for (final aprove.verification.dpframework.BasicStructures.TRSTerm ta : fa.getArguments()) {
                    cs.add((aprove.verification.dpframework.DPConstraints.Constraint) EasyInput.interpretAsConstraint(ta));
                }
                return aprove.verification.dpframework.DPConstraints.ConstraintSet.flatCreate(cs);
            } else if (fa.getRootSymbol().getName().equals("imp")) {
                return aprove.verification.dpframework.DPConstraints.Implication.create(
                    fa.getArgument(0).getVariables(),
                    (aprove.verification.dpframework.DPConstraints.ConstraintSet) EasyInput.interpretAsConstraint(fa.getArgument(1)),
                    (aprove.verification.dpframework.DPConstraints.Constraint) EasyInput.interpretAsConstraint(fa.getArgument(2)),
                    null);

            } else if (fa.getRootSymbol().getName().equals("?")) {
                return aprove.verification.dpframework.DPConstraints.Predicate.create(
                    fa.getArgument(0), fa.getArgument(1),
                    Predicate.Kind.AbstractRelation, null, null, null);
            } else if (fa.getRootSymbol().getName().equals(">")) {
                return aprove.verification.dpframework.DPConstraints.ReducesTo.create(
                    fa.getArgument(0), fa.getArgument(1), null, new Count(),
                    null);
            }
        }
        return t;
    }

    public static final aprove.verification.dpframework.DPConstraints.Constraint parseConstraint(final Map<String, aprove.verification.dpframework.BasicStructures.TRSVariable> vars,
        final String constr) {
        return (aprove.verification.dpframework.DPConstraints.Constraint) EasyInput.interpretAsConstraint(EasyInput.getTerm(
            vars, constr));
    }

    public static final Map<String, aprove.verification.dpframework.BasicStructures.TRSVariable> parseVariables(final String varsString) {
        final Map<String, aprove.verification.dpframework.BasicStructures.TRSVariable> vars =
            new LinkedHashMap<>();
        final StringTokenizer st = new StringTokenizer(varsString, ",");
        while (st.hasMoreTokens()) {
            final String varString = st.nextToken().trim();
            vars.put(varString, aprove.verification.dpframework.BasicStructures.TRSTerm.createVariable(varString));
        }
        return vars;
    }

    /**
     * Creates a new term out of the given variables and a string representation
     * of the term.
     * @param varsString should be a String with variable names divided by comma
     * (e.g.: x,y,z), (blanks are trimmed)
     * @param termString should be the normal String representation of a term
     * (e.g.: f(x,g(y,a)))
     */
    public static final TRSTerm parseTerm(String varsString, String termString) {
        return EasyInput.getTerm(EasyInput.parseVariables(varsString), termString);
    }

    private static final TRSTerm getTerm(Map<String, aprove.verification.dpframework.BasicStructures.TRSVariable> vars, String termString) {
        termString = termString.trim();
        final int indexOfParen = termString.indexOf("(");
        if (indexOfParen < 0) {
            final aprove.verification.dpframework.BasicStructures.TRSVariable x = vars.get(termString);
            if (x != null) {
                return x;
            } else {
                return TRSTerm.createConstant(termString);
            }
        }
        final String fsString = termString.substring(0, indexOfParen);
        final String argsString =
            termString.substring(indexOfParen + 1, termString.length() - 1);

        final ArrayList<aprove.verification.dpframework.BasicStructures.TRSTerm> args =
            new ArrayList<aprove.verification.dpframework.BasicStructures.TRSTerm>();
        int pc = 0;
        StringBuilder sb = new StringBuilder("");
        for (final char ch : argsString.toCharArray()) {
            if (ch == ',' && pc == 0) {
                args.add(EasyInput.getTerm(vars, sb.toString()));
                sb = new StringBuilder("");
            } else if (ch == '(') {
                sb.append(ch);
                pc++;
            } else if (ch == ')') {
                sb.append(ch);
                pc--;
            } else {
                sb.append(ch);
            }
        }
        if (pc != 0) {
            if (Globals.useAssertions) {
                assert (false) : "The string does not close all brackets! "
                    + argsString.toString();
            } else {
                throw new RuntimeException(
                    "The string does not close all brackets!"
                    + argsString.toString());
            }
        }
        if (sb.length() > 0) {
            args.add(EasyInput.getTerm(vars, sb.toString()));
        }
        final aprove.verification.oldframework.BasicStructures.FunctionSymbol fs =
            aprove.verification.oldframework.BasicStructures.FunctionSymbol.create(fsString,
                args.size());
        final aprove.verification.dpframework.BasicStructures.TRSFunctionApplication fa =
            aprove.verification.dpframework.BasicStructures.TRSTerm.createFunctionApplication(
                fs, ImmutableCreator.create(args));
        return fa;
    }

    /**
     * Creates a new term out of the given string. Symbols with brackets (
     * <code>f(x,y)</code>) represent a function, symbols without brackets
     * represent variables. Constants can be written as functions without
     * parameters.
     * @param termString should be the normal String representation of a term
     * (e.g.: f(x,g(y,a)))
     */
    public static final aprove.verification.dpframework.BasicStructures.TRSTerm parseTerm(String termString) {
        termString = termString.trim();
        final int indexOfParen = termString.indexOf("(");
        final Set<aprove.verification.dpframework.BasicStructures.TRSVariable> vars =
            new LinkedHashSet<aprove.verification.dpframework.BasicStructures.TRSVariable>();

        if (indexOfParen < 0) {
            final aprove.verification.dpframework.BasicStructures.TRSVariable x =
                aprove.verification.dpframework.BasicStructures.TRSTerm.createVariable(termString.trim());
            vars.add(x);
            return x;
        }
        final String fsString = termString.substring(0, indexOfParen);
        final String argsString;
        if (termString.length() > indexOfParen + 1) {
            argsString = termString.substring(indexOfParen + 1, termString.length() - 1);
        } else {
            argsString = "";
        }

        final ArrayList<aprove.verification.dpframework.BasicStructures.TRSTerm> args =
            new ArrayList<aprove.verification.dpframework.BasicStructures.TRSTerm>();
        int pc = 0;
        StringBuilder sb = new StringBuilder("");
        for (final char ch : argsString.toCharArray()) {
            if (ch == ',' && pc == 0) {
                args.add(EasyInput.parseTerm(sb.toString()));
                sb = new StringBuilder("");
            } else if (ch == '(') {
                sb.append(ch);
                pc++;
            } else if (ch == ')') {
                sb.append(ch);
                pc--;
            } else {
                sb.append(ch);
            }
        }
        if (sb.length() > 0) {
            args.add(EasyInput.parseTerm(sb.toString()));
        }
        final aprove.verification.oldframework.BasicStructures.FunctionSymbol fs =
            aprove.verification.oldframework.BasicStructures.FunctionSymbol.create(fsString,
                args.size());
        final aprove.verification.dpframework.BasicStructures.TRSFunctionApplication fa =
            aprove.verification.dpframework.BasicStructures.TRSTerm.createFunctionApplication(
                fs, ImmutableCreator.create(args));
        return fa;
    }

    public static final Rule parseRule(final String lhsStr, final String rhsStr) {
        final aprove.verification.dpframework.BasicStructures.TRSTerm lhs = EasyInput.parseTerm(lhsStr);
        final aprove.verification.dpframework.BasicStructures.TRSTerm rhs = EasyInput.parseTerm(rhsStr);
        return Rule.create((TRSFunctionApplication)lhs, rhs);
    }

    /**
     * Loads an ITRSProblem from a file.
     */
    public static final ITRSProblem loadITRS(final String srcfile) {
        final aprove.input.Programs.itrs.Translator trans = new aprove.input.Programs.itrs.Translator();
        try {
            trans.translate(new File(srcfile));
            trans.throwOnError();
        } catch (final Exception e) {
            e.printStackTrace();
            throw new RuntimeException("could not load from '" + srcfile
                + "'\n" + e.getMessage());
        }
        final ITRSProblem result = (ITRSProblem) trans.getState();
        return result;
    }

    /**
     * Loads a QTRSProblem from a file.
     */
    public static final QTRSProblem loadQTRS(final String srcfile) {
        final aprove.input.Programs.newTrs.Translator trans = new aprove.input.Programs.newTrs.Translator();
        try {
            trans.translate(new File(srcfile));
            trans.throwOnError();
        } catch (final Exception e) {
            e.printStackTrace();
            throw new RuntimeException("could not load from '" + srcfile
                + "'\n" + e.getMessage());
        }
        final QTRSProblem result = (QTRSProblem) trans.getState();
        return result;
    }
}
