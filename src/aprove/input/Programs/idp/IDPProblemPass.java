package aprove.input.Programs.idp;

import java.util.*;

import aprove.input.Generated.idp.analysis.*;
import aprove.input.Generated.idp.node.*;
import aprove.input.Utility.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.dpframework.IDPProblem.PfFunctions.*;
import aprove.verification.dpframework.IDPProblem.PfFunctions.PredefinedFunction.*;
import aprove.verification.dpframework.IDPProblem.PfFunctions.domains.*;
import aprove.verification.dpframework.IDPProblem.utility.*;
import aprove.verification.oldframework.BasicStructures.*;
import immutables.*;

/**
 * Generates an IDPProblem from an abstract syntax tree.
 *
 * See {@link Translator} and SableCC documentation for usage of this class.
 * The in*- and out*-Methods are just public for technical reasons and of
 * no interest for usage of this class.
 *
 * Besides the inherited methods, there are just two interesting public methods:
 * <code>getErrors</code> and <code>getIDPProblem()</code>
 *
 * Note that children of the "rule" rule are not parsed here but in the
 * {@link ExpressionParser} class.
 *
 * @author noschinski
 */
public class IDPProblemPass extends DepthFirstAdapter {

    protected static enum Section {Pairs, Rules}

    /**
     * The default suffix for integers
     */
    final protected String default_int_suffix = DomainFactory.INTEGERS.getSuffix();

    /**
     * The set of the variables occurring in this IDP.
     */
    final protected ImmutableSet<String> vars;

    /**
     * The resulting IDPProblem
     */
    private volatile IDPProblem idpProblem;

    /**
     * Language which should be accepted by the parser.
     */
    final protected ParserLanguage language;

    /* ------------- PARSING STATE VARIABLES -------------
     * The following variables maintain the parser state. */

    /**
     * List of errors which occurred during parsing.
     */
    final protected List<ParseError> errors;

    /**
     * Rules constructed from one "rules" production rule (see idp.grammar)
     * (I.e. this can be from a RULES section as well from a PAIRS section)
     */
    protected Set<IGeneralizedRule> curRules;

    /**
     * Set of rules (from RULES sections).
     */
    final protected Set<IGeneralizedRule> rRules;
    protected RuleAnalysis<GeneralizedRule> rAnalysis;

    /**
     * List of errors which occurred during parsing.
     */
    final protected Map<ImmutablePair<Func,List<? extends Domain>>, FunctionSymbol> predefinedMapping;

    /**
     * Set of q terms
     */
    protected IQTermSet q;
    protected boolean innermost = true;

    /**
     * Set of dependency pairs (from PAIRS sections).
     */
    final protected Set<IGeneralizedRule> pRules;
    protected RuleAnalysis<GeneralizedRule> pAnalysis;

    /*
     * Complexity annotations.
     */
    protected boolean complexityGoal = false;
    protected static enum StartTermType { Full, ConstructorBased, Automaton, FunctionSymbols };
    protected StartTermType startterm = StartTermType.Full;

    private final LinkedHashSet<String> startSymbols = new LinkedHashSet<>();
    private boolean inFunctionsymbolsStartterm = false;

    /* ------------- CODE ------------- */

    /** Creates a new IDPProblemPass visitor.
     *
     * @param vars Variables occurring in this IDP. This set can be
     *     generated using the class <code>CollectVarsPass</code>.
     */
    public IDPProblemPass(final ParserLanguage mode, final Set<String> vars) {
        this.vars = ImmutableCreator.create(vars);
        this.errors = new LinkedList<ParseError>();
        this.predefinedMapping = new LinkedHashMap<ImmutablePair<Func,List<? extends Domain>>, FunctionSymbol>();
        this.idpProblem = null;
        this.pRules = new LinkedHashSet<IGeneralizedRule>();
        this.rRules = new LinkedHashSet<IGeneralizedRule>();
        this.language = mode;
    }

    /**
     * Returns the parsed {@link IDPProblem}.
     * @return Null, iff an parse error occurred.
     */
    public IDPProblem getIDPProblem() {
        if (this.idpProblem == null) {
            synchronized (this) {
                this.prepareIDP();
                if (this.idpProblem == null) {
                    try {
                        this.idpProblem =
                            IDPProblem.create(
                                new IDPRuleAnalysis(this.rAnalysis, this.pAnalysis, this.q, null),
                                true,
                                null);
                    } catch (final AbortionException e) {
                        e.printStackTrace();
                    }
                }
            }
        }
        return this.idpProblem;
    }

    /**
     * @return The rule analysis for the R rules
     */
    public RuleAnalysis<GeneralizedRule> getRAnalysis() {
        if (this.rAnalysis == null) {
            synchronized (this) {
                this.prepareIDP();
            }
        }
        return this.rAnalysis;
    }

    /**
     * @return The Q term set
     */
    public IQTermSet getQ() {
        if (this.q == null) {
            synchronized (this) {
                this.prepareIDP();
            }
        }
        return this.q;
    }

    /**
     * @return The rule analysis for the P rules
     */
    public RuleAnalysis<GeneralizedRule> getPAnalysis() {
        if (this.pAnalysis == null) {
            synchronized (this) {
                this.prepareIDP();
            }
        }
        return this.pAnalysis;
    }

    /**
     * @return The rules (with conditions) from the R section of the input
     */
    public Set<IGeneralizedRule> getRRules() {
        return this.rRules;
    }

    /**
     * Returns a list of parse errors.
     */
    public List<ParseError> getErrors() {
        return this.errors;
    }

    /**
     * Parse goal
     */
    @Override
    public void inAComplexityGoal(AComplexityGoal node) {
        this.complexityGoal = true;
    };

    @Override
    public void inATerminationGoal(ATerminationGoal node) {
        this.complexityGoal = false;
    };

    /**
     * Parse start-term
     */
    @Override
    public void inAFullStartterm(AFullStartterm node) {
        this.startterm = StartTermType.Full;
    };

    @Override
    public void inAConstructorbasedStartterm(AConstructorbasedStartterm node) {
        this.startterm = StartTermType.ConstructorBased;
    };

    @Override
    public void inAAutomatonStartterm(AAutomatonStartterm node) {
        this.startterm = StartTermType.Automaton;
    };

    @Override
    public void inAFunctionsymbolsStartterm(AFunctionsymbolsStartterm node) {
        this.inFunctionsymbolsStartterm  = true;
        this.startterm = StartTermType.FunctionSymbols;
    }

    @Override
    public void outAFunctionsymbolsStartterm(AFunctionsymbolsStartterm node) {
        this.inFunctionsymbolsStartterm = false;
    }


    /**
     * Set current rule set to PAIRS.
     *
     * <p>On entering a PAIRS section, set the <code>curRules</code>
     * set to <code>pRules</code>, so the rules in this section are
     * added to the pairs set.
     */
    @Override
    public void inAPairs(final APairs node) {
        if (this.language == ParserLanguage.ITRS || this.language == ParserLanguage.CINT) {
            final ParseError pe = new ParseError(ParseError.ERROR);
            pe.setMessage("PAIRS section not allowed in ITRS and CINT mode!");
            this.errors.add(pe);
        }
        this.curRules = this.pRules;
    }

    /**
     * Set current rule set to RULES.
     *
     * <p>On entering a RULES section, set the <code>curRules</code>
     * set to <code>rRules</code>, so the rules in this section are
     * added to the rules set.
     */
    @Override
    public void inARules(final ARules node) {
        this.curRules = this.rRules;
    }

    /**
     * Parse a conditional rule.
     */
    @Override
    public void caseACondRule(final ACondRule node) {
        if (this.language != ParserLanguage.ITRS && this.language != ParserLanguage.CINT) {
            final ParseError pe = new ParseError(ParseError.ERROR);
            pe.setMessage("Conditional rules are only allowed in ITRS and CINT mode!");
            this.errors.add(pe);
        }
        final ExpressionParser ep = this.getExpressionParser();
        final TRSTerm lhs = ep.parse(node.getLhs());
        final TRSTerm rhs = ep.parse(node.getRhs());
        final TRSTerm cond = ep.parse(node.getCond());
        final IGeneralizedRule r = this.createIRule(lhs, rhs, cond);
        this.curRules.add(r);
    }

    /**
     * Parse a unconditional rule.
     */
    @Override
    public void caseAUncondRule(final AUncondRule node) {
        final ExpressionParser ep = this.getExpressionParser();
        final TRSTerm lhs = ep.parse(node.getLhs());
        final TRSTerm rhs = ep.parse(node.getRhs());
        final IGeneralizedRule r = this.createIRule(lhs, rhs, null);
        this.curRules.add(r);
    }

    /**
     * Tree walk was successful -> create the IDPProblem
     */
    @Override
    public void outStart(final Start node) {
    }

    private void prepareIDP() {
        if (!this.errors.isEmpty()) {
            return;
        }

        final Set<GeneralizedRule> rRules = IGeneralizedRule.removeConditions(this.rRules);
        final Set<GeneralizedRule> pRules = IGeneralizedRule.removeConditions(this.pRules);

        Collection<String> usedNames = CollectionUtils.getNames(CollectionUtils.getFunctionSymbols(rRules));
        usedNames.addAll(CollectionUtils.getNames(CollectionUtils.getFunctionSymbols(pRules)));
        Map<FunctionSymbol, PredefinedFunction<? extends Domain>> mapping =
            new LinkedHashMap<FunctionSymbol, PredefinedFunction<? extends Domain>>();
        for (Map.Entry<ImmutablePair<Func, List<? extends Domain>>, FunctionSymbol> entry : this.predefinedMapping
            .entrySet())
        {
            ImmutablePair<Func, List<? extends Domain>> key = entry.getKey();
            mapping
                .put(entry.getValue(), PredefinedSemanticsFactory.getFunction(key.x, ImmutableCreator.create(key.y)));
        }

        final IDPPredefinedMap predefinedMap = new IDPPredefinedMap(ImmutableCreator.create(mapping), usedNames);
        this.rAnalysis = new RuleAnalysis<GeneralizedRule>(ImmutableCreator.create(rRules), predefinedMap);
        this.pAnalysis = new RuleAnalysis<GeneralizedRule>(ImmutableCreator.create(pRules), predefinedMap);
        // FIXME where do we get Q from?
        this.q = new IQTermSet(new QTermSet(this.rAnalysis.getLeftHandSides()), predefinedMap);
        // q = new IQTermSet(new QTermSet(Collections.<FunctionApplication>emptySet()));
    }

    /* ------------- INTERNAL FUNCTIONS ------------- */

    /**
     * Create an IGeneralizedRule while enforcing restrictions.
     *
     * <p>This method makes sure, that the generated IGeneralizedRule fulfills the
     * variable restriction whenever we are not in the innermost case
     * (all variables on the rhs occur also on the lhs).</p>
     *
     * <p>If this restriction is not fulfilled, it logs an error and
     * returns null.</p>
     *
     * @return Null in case of an error.
     */
    protected IGeneralizedRule createIRule(final TRSTerm _lhs, final TRSTerm rhs,
            final TRSTerm cond) {
        /* The lhs was not parsed. This means, there was an semantic error. As such,
         * it was already logged to this.errors */
        if (_lhs == null) {
            return null;
        }

        TRSFunctionApplication lhs;

        try {
            lhs = (TRSFunctionApplication) _lhs;
        } catch(final ClassCastException e) {
            final ParseError pe = new ParseError(ParseError.ERROR);
            final String errMsg = "The lhs of the rule " + _lhs + " -> " +
            rhs +" is not a function application!";
            pe.setMessage(errMsg);
            this.errors.add(pe);
            return null;
        }

        // check if every variable in the rhs or condition is contained in the lhs
        if (! this.innermost) {
            final Set<TRSVariable> vars = rhs.getVariables();
            if (cond != null) {
                vars.addAll(cond.getVariables());
            }
            vars.removeAll(lhs.getVariables());
            if (!vars.isEmpty()) {
                final ParseError pe = new ParseError(ParseError.ERROR);
                final StringBuilder s = new StringBuilder();
                s.append("The condition/rhs of the rule ");
                s.append(lhs);
                s.append(" -> ");
                s.append(rhs);
                s.append(" :|: ");
                s.append(cond);
                s.append(" contains the variables ");
                s.append(vars);
                s.append(" which are not in the lhs!");
                pe.setMessage(s.toString());
                this.errors.add(pe);
                return null;
            }
        }

        /*try {*/
        return IGeneralizedRule.create(lhs, rhs, cond);
        /*} catch (NoIboTermException e) {
            String errMsg = "The Condition " + cond + "could not be converted"
                    + " to an ImmutableBoolOp<Predicate> (because of the"
                    + "subterm " +e.getSubterm() +". This should not"
                    + " be possible.";
            throw new RuntimeException(errMsg, e);
        } */
    }

    private ExpressionParser getExpressionParser() {
        return
        new ExpressionParser(this.vars, this.default_int_suffix, this.errors, this.predefinedMapping);
    }


    @Override
    public void inAVar(AVar node) {
        if (this.inFunctionsymbolsStartterm) {
            this.startSymbols.add(node.getName().getText());
        }
    }

    public LinkedHashSet<String> getStartsymbols() {
        return this.startSymbols;
    }
}
