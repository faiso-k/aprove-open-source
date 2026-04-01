package aprove.verification.oldframework.BooleanSemanticLabelling;

import java.math.*;
import java.util.*;
import java.util.logging.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Export.Utility.Export_Util.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPProblem.Processors.QDPSemanticPOLOLabellingProcessor.*;
import aprove.verification.oldframework.Algebra.Orders.Utility.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.Formulae.*;
import aprove.verification.oldframework.PropositionalLogic.TheoryPropositions.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * Very similar to BSLTermInterpretor, but also encodes the search for a
 * labelling function and a polynomial order solving the resulting constraints.
 * @author Patrick Kabasci
 * @version $Id$
 */
public class BSLAutoSearchTermInterpretor {


    // (so far hack) Do we really do labelling, or only ordering by propositional order?
    private final boolean orderOnly = false;

    private static Logger log = Logger.getLogger("aprove.verification.oldframework.Algebra.BooleanSemanticLabelling.BSLAutoSearchTermInterpretor");

    /**
     * docu-guess (noschinski): Stores the variables which decide whether the
     * i-th component of the j-th argument of a function symbol is filtered.
     * Retrieve those via:
     *
     * <code>filter.get(functionSymbol).get(new Pair(i,j))</code>
     *
     * (For model search)
     */
    Map<FunctionSymbol, Map<Triple<Integer, Integer, Integer>, Formula<Diophantine>>> filter = new LinkedHashMap<FunctionSymbol, Map<Triple<Integer, Integer, Integer>, Formula<Diophantine>>>();

    /**
     * docu-guess (noschinski): Stores the variable which decides whether the
     * i-th component of the j-th argument of a function symbol is negated.
     *
     * (For model search)
     */
    Map<FunctionSymbol, Map<Triple<Integer, Integer, Integer>, Formula<Diophantine>>> nots = new LinkedHashMap<FunctionSymbol, Map<Triple<Integer, Integer, Integer>, Formula<Diophantine>>>();

    /**
     * docu-guess (noschinski): Stores the variable which decides whether the
     * i-th component of a function symbol is to be computed with some
     * element from FunctionPool.
     *
     * (For model search)
     */
    Map<FunctionSymbol, Map<Pair<Integer, FunctionPool>, Formula<Diophantine>>> pool = new LinkedHashMap<FunctionSymbol, Map<Pair<Integer, FunctionPool>,Formula<Diophantine>>>();

    // f, targetArgumentDimensionIndex, argumentIndex, sourceArgumentDimensionIndex
    /**
     * docu-guess (noschinski): like filter, but for labelling search
     */
    Map<FunctionSymbol, Map<Triple<Integer, Integer, Integer>, Formula<Diophantine>>> labfilter = new LinkedHashMap<FunctionSymbol, Map<Triple<Integer, Integer, Integer>, Formula<Diophantine>>>();
    /**
     * docu-guess (noschinski): like nots, but for labelling search
     */
    Map<FunctionSymbol, Map<Triple<Integer, Integer, Integer>, Formula<Diophantine>>> labnots = new LinkedHashMap<FunctionSymbol, Map<Triple<Integer, Integer, Integer>, Formula<Diophantine>>>();
    /**
     * docu-guess (noschinski): like pool, but for labelling search
     */
    Map<FunctionSymbol, Map<Pair<Integer, FunctionPool>, Formula<Diophantine>>> labpool = new LinkedHashMap<FunctionSymbol, Map<Pair<Integer, FunctionPool>,Formula<Diophantine>>>();

    Map<Triple<FunctionSymbol, ArrayList<Boolean>, Integer>, SimplePolynomial> abstractInterpretation = new LinkedHashMap<Triple<FunctionSymbol, ArrayList<Boolean>, Integer>, SimplePolynomial>();

    Map<Rule, Formula<Diophantine>> isStrictMap = new LinkedHashMap<Rule, Formula<Diophantine>>();

    Map<TRSVariable, VarPolynomial> variables = new LinkedHashMap<TRSVariable, VarPolynomial>();

    // Debug:
    Map<Triple<TRSTerm, Integer, Map<TRSVariable, ArrayList<Boolean>>>, Formula<Diophantine>> termValues = new LinkedHashMap<Triple<TRSTerm, Integer, Map<TRSVariable,ArrayList<Boolean>>>, Formula<Diophantine>>();

    /**
     * SIDE EFFECTS
     * This contains all the relevant variables for the proof at first. Note
     * that this is mutable: After SAT-Search it will only contain the
     * variables which are set according to our model. Always use the provided methods to specialize this after searching, and dispose it afterwards.
     */
    public Set<Formula<Diophantine>> interestingVars = new LinkedHashSet<Formula<Diophantine>>();
    public Map<String, BigInteger> result = new LinkedHashMap<String, BigInteger>();

    private int runningNum = 0;

    private int dimension;
    private final QUASI_MODE quasiState;

    Map<Pair<TRSTerm, Integer>, Formula<Diophantine>> values = new LinkedHashMap<Pair<TRSTerm,Integer>, Formula<Diophantine>>();

    List<Formula<Diophantine>> masterConjuncts = new ArrayList<Formula<Diophantine>>();

    Set<FunctionSymbol> signature;

    private FormulaFactory<Diophantine> ff;

    /**
     * The variable which decides if a model is quasi or not
     */
    private Formula<Diophantine> isQuasi;
    private Set<Rule> rules;
    private Map<String, BigInteger> goalState;


    private boolean specialized = false;

    private boolean requireMonotonicity;

    private enum FunctionPool {
        AND,
        OR,
        XOR//,
        //ONE We'll see whether we want that.
    }

    public BSLAutoSearchTermInterpretor(QUASI_MODE quasiMode) {
        this.quasiState = quasiMode;
    }

    public void specialize(final Set<Rule> rules, final Map<String, BigInteger> goalState) {
        this.goalState = goalState;
        this.rules = rules;
        this.specialized  = true;
    }

    /**
     * docu-guess (noschinski): Dumps current state to log with loglevel FINEST.
     */
    public void dump() {
        if (!BSLAutoSearchTermInterpretor.log.isLoggable(Level.FINEST)) {
            return;
        }

        // are we in quasi-Mode?
        if(this.interestingVars.contains(this.isQuasi)) {
            BSLAutoSearchTermInterpretor.log.log(Level.FINEST,"Quasi-Model found:");
        } else {
            BSLAutoSearchTermInterpretor.log.log(Level.FINEST,"Model found:");
        }

        // first dump the selected functions, filters and notfilters.
        for (final FunctionSymbol f: this.signature) {
            BSLAutoSearchTermInterpretor.log.log(Level.FINEST,"Considering " + f.getName() + "/" + f.getArity() + ":");

            for (int i =0; i < this.dimension; i++) {
                for (int j=0; j < f.getArity(); j++) {
                    for (int k=0; k< this.dimension; k++) {
                        if (this.interestingVars.contains(this.filter.get(f).get(new Triple<Integer, Integer, Integer>(i,j,k)))) {
                            if (this.interestingVars.contains(this.nots.get(f).get(new Triple<Integer, Integer, Integer>(i,j,k)))) {
                                BSLAutoSearchTermInterpretor.log.log(Level.FINEST,"Model: We negate the " + j + "th argument's " + k + "th component in the " + i + "th resulting component.");
                            } else {
                                BSLAutoSearchTermInterpretor.log.log(Level.FINEST,"Model: We regard the " + j + "th argument's " + k + "th component in the " + i + "th resulting component.");

                            }
                        }
                        if (this.interestingVars.contains(this.labfilter.get(f).get(new Triple<Integer, Integer, Integer>(i,j,k)))) {
                            if (this.interestingVars.contains(this.labnots.get(f).get(new Triple<Integer, Integer, Integer>(i,j,k)))) {
                                BSLAutoSearchTermInterpretor.log.log(Level.FINEST,"Label: We negate the " + j + "th argument's " + k + "th component in the " + i + "th resulting component.");
                            } else {
                                BSLAutoSearchTermInterpretor.log.log(Level.FINEST,"Label: We regard the " + j + "th argument's " + k + "th component in the " + i + "th resulting component.");

                            }
                        }

                    }
                }



                if (this.interestingVars.contains(this.pool.get(f).get(new Pair<Integer, FunctionPool>(i, FunctionPool.AND)))) {
                    BSLAutoSearchTermInterpretor.log.log(Level.FINEST,"--Interpreted as and in the " + i + "th component.");
                }
                if (this.interestingVars.contains(this.pool.get(f).get(new Pair<Integer, FunctionPool>(i, FunctionPool.OR)))) {
                    BSLAutoSearchTermInterpretor.log.log(Level.FINEST,"--Interpreted as or in the " + i + "th component.");
                }
                if (this.interestingVars.contains(this.pool.get(f).get(new Pair<Integer, FunctionPool>(i, FunctionPool.XOR)))) {
                    BSLAutoSearchTermInterpretor.log.log(Level.FINEST,"--Interpreted as xor in the " + i + "th component.");
                }

                if (this.interestingVars.contains(this.labpool.get(f).get(new Pair<Integer, FunctionPool>(i, FunctionPool.AND)))) {
                    BSLAutoSearchTermInterpretor.log.log(Level.FINEST,"--Labelled as and in the " + i + "th component.");
                }
                if (this.interestingVars.contains(this.labpool.get(f).get(new Pair<Integer, FunctionPool>(i, FunctionPool.OR)))) {
                    BSLAutoSearchTermInterpretor.log.log(Level.FINEST,"--Labelled as or in the " + i + "th component.");
                }
                if (this.interestingVars.contains(this.labpool.get(f).get(new Pair<Integer, FunctionPool>(i, FunctionPool.XOR)))) {
                    BSLAutoSearchTermInterpretor.log.log(Level.FINEST,"--Labelled as xor in the " + i + "th component.");
                }


            }



        }




    }


    public boolean solves(final Rule r) {
        return this.interestingVars.contains(this.isStrictMap.get(r));
    }


    public Formula<Diophantine> getSATFormula() {
        final List<Formula<Diophantine>> dArgs = new ArrayList<Formula<Diophantine>>();
        for (final Formula<Diophantine> f: this.isStrictMap.values()) {
            dArgs.add(f);
        }
        this.masterConjuncts.add(this.ff.buildOr(dArgs));
        return this.ff.buildAnd(this.masterConjuncts);
    }

    public Formula<Diophantine>[] getValue(final TRSTerm t) {
        final Formula<Diophantine>[] result = new Formula[this.dimension];
        for (int i=0; i < this.dimension; i++) {
            result[i] = this.values.get(new Pair<TRSTerm, Integer>(t,i));
        }
        return result;
    }

    public void init(final FormulaFactory<Diophantine> ff, final int dimension,
            final Set<FunctionSymbol> signature, final Set<TRSVariable> variables,
            final boolean requireMonotonicity) {
        this.ff = ff;
        this.dimension = dimension;
        this.signature = signature;
        this.requireMonotonicity = requireMonotonicity;


        final List<Formula<Diophantine>> cArgs = new ArrayList<Formula<Diophantine>>();

        // Generate quasi
        this.isQuasi = ff.buildVariable();
        this.interestingVars.add(this.isQuasi);

        switch (this.quasiState) {
        case ALLOW:
            break;
        case DISABLE:
            cArgs.add(ff.buildNot(this.isQuasi));
            break;
        case FORCE:
            cArgs.add(this.isQuasi);
        }

        for (final FunctionSymbol f: signature) {
            this.interpretFunctionSymbol(ff, dimension, requireMonotonicity, cArgs,
                    f);
        }

        for (final TRSVariable var: variables) {
            this.variables.put(var, VarPolynomial.createVariable(var.getName()));
        }

        this.masterConjuncts.addAll(cArgs);
        this.masterConjuncts.add(ff.buildNot(this.isQuasi));
    }


    private void interpretFunctionSymbol(final FormulaFactory<Diophantine> ff,
            final int dimension, final boolean requireMonotonicity,
            final List<Formula<Diophantine>> cArgs, final FunctionSymbol f) {
        this.filter.put(f, new LinkedHashMap<Triple<Integer,Integer, Integer>, Formula<Diophantine>>());
        this.nots.put(f, new LinkedHashMap<Triple<Integer,Integer, Integer>, Formula<Diophantine>>());
        this.pool.put(f, new LinkedHashMap<Pair<Integer,FunctionPool>, Formula<Diophantine>>());
        this.labfilter.put(f, new LinkedHashMap<Triple<Integer,Integer, Integer>, Formula<Diophantine>>());
        this.labnots.put(f, new LinkedHashMap<Triple<Integer,Integer, Integer>, Formula<Diophantine>>());
        this.labpool.put(f, new LinkedHashMap<Pair<Integer,FunctionPool>, Formula<Diophantine>>());
        // First, generate pi and nots
        for (int i =0; i < dimension; i++) {
            for (int j=0; j < f.getArity(); j++) {
                for (int k=0; k< dimension; k++) {
                    Formula<Diophantine> fil = ff.buildVariable();
                    this.interestingVars.add(fil);
                    this.filter.get(f).put(new Triple<Integer, Integer, Integer>(i,j,k), fil);

                    Formula<Diophantine> not = ff.buildVariable();
                    this.interestingVars.add(not);
                    this.nots.get(f).put(new Triple<Integer, Integer, Integer>(i,j,k), not);
                    // Not is forbidden if quasi is set.
                    cArgs.add(ff.buildImplication(this.isQuasi, ff.buildNot(not)));
                    if (requireMonotonicity) {
                        cArgs.add(ff.buildNot(not));
                    }

                    fil = ff.buildVariable();
                    this.interestingVars.add(fil);
                    this.labfilter.get(f).put(new Triple<Integer, Integer, Integer>(i,j,k), fil);


                    not = ff.buildVariable();
                    this.interestingVars.add(not);
                    this.labnots.get(f).put(new Triple<Integer, Integer, Integer>(i,j,k), not);
                    // Not is forbidden if quasi is set.
                    cArgs.add(ff.buildImplication(this.isQuasi, ff.buildNot(not)));


                }
            }

            // Now prepare the interpretation pool. Note that only exactly one is allowed.
            // Though one can lift that if quasi is not set (but contradicts our intuition)
            Formula<Diophantine> andVar = ff.buildVariable();
            Formula<Diophantine> orVar = ff.buildVariable();
            Formula<Diophantine> xorVar = ff.buildVariable();
            if (requireMonotonicity) {
                cArgs.add(ff.buildNot(xorVar));
            }

            this.interestingVars.add(andVar);
            this.interestingVars.add(orVar);
            this.interestingVars.add(xorVar);

            final Formula[] fpool = {andVar, orVar, xorVar};

            this.pool.get(f).put(new Pair<Integer, FunctionPool>(i, FunctionPool.AND), andVar);
            this.pool.get(f).put(new Pair<Integer, FunctionPool>(i, FunctionPool.OR), orVar);
            this.pool.get(f).put(new Pair<Integer, FunctionPool>(i, FunctionPool.XOR), xorVar);


            cArgs.add(new SATPatterns<Diophantine>(ff).encodeExactlyOne(fpool));
            // Quasi-Models do not allow XOR.
            cArgs.add(ff.buildImplication(this.isQuasi, ff.buildNot(xorVar)));

            // Debug: Uncomment to disable XOR
            // cArgs.add(ff.buildNot(xorVar));


            andVar = ff.buildVariable();
            orVar = ff.buildVariable();
            xorVar = ff.buildVariable();
            this.interestingVars.add(andVar);
            this.interestingVars.add(orVar);
            this.interestingVars.add(xorVar);
            fpool[0] = andVar; fpool[1] = orVar; fpool[2] = xorVar;

            this.labpool.get(f).put(new Pair<Integer, FunctionPool>(i, FunctionPool.AND), andVar);
            this.labpool.get(f).put(new Pair<Integer, FunctionPool>(i, FunctionPool.OR), orVar);
            this.labpool.get(f).put(new Pair<Integer, FunctionPool>(i, FunctionPool.XOR), xorVar);
            cArgs.add(new SATPatterns<Diophantine>(ff).encodeExactlyOne(fpool));
            // Quasi-Models do not allow XOR.
            cArgs.add(ff.buildImplication(this.isQuasi, ff.buildNot(xorVar)));


        }

        // Now, generate abstract interpretations for all symbols.
        // First, generate representors.
        final Set<ArrayList<Boolean>> representors = this.generateRepresentors(dimension);

        // and finally the abstract coefficients.
        for (final ArrayList<Boolean> rep: representors) {
            // Note the less-or-equal. Arguments are one-based, the zero is the constant.
            for (int i=0; i <= f.getArity(); i++) {
                SimplePolynomial coeff;
                // Do we require Monotonicity? If so, we simply set the constant to one. Later we will evaluate whether allowing further ranges yields any improvement.
                if (this.requireMonotonicity &&  i > 0) {
                    coeff = SimplePolynomial.ONE;
                } else {
                    coeff = SimplePolynomial.create(f.getName() + "_" + f.getArity() + "-" + rep.toString() + "/" + i);
                }
                this.abstractInterpretation.put(new Triple<FunctionSymbol, ArrayList<Boolean>, Integer>(f, rep, i), coeff);

            }
        }

        if (this.quasiState != QUASI_MODE.DISABLE) {
            this.addDecreasingRulesForQuasi(ff, f, representors);
        }
    }

    /**
     * Quasi introduces decreasing rules of the form f^ l1(x,y,z) > f^l2(x,y,z)
     * f.a. l1 > l2. We introduce them here.
     */
    private void addDecreasingRulesForQuasi(final FormulaFactory<Diophantine> ff,
            final FunctionSymbol f, final Set<ArrayList<Boolean>> representors) {
        final Poset<ArrayList<Boolean>> po = Poset.create(representors);

        // Fill the mapping relation. Currently we use component-wise orderings, with certain restrictions lexicographic orders should also be possible.
        for (final ArrayList<Boolean> repres: representors) {
            for (int i = 0; i < repres.size(); i++) {
                if (repres.get(i) == false) {
                    final ArrayList<Boolean> represhigher = new ArrayList<Boolean>(repres.size());
                    for (int j=0; j < repres.size(); j++) {
                        represhigher.add(repres.get(j));
                    }
                    represhigher.set(i, true);
                    try {
                        po.setGreater(represhigher, repres);
                    } catch (final Exception ex) {
                        if (Globals.useAssertions) {
                            assert false;
                        }

                    }

                }
            }
        }

        // now set the constraints.
        for (final Pair<ArrayList<Boolean>, ArrayList<Boolean>> p: po.getStrictPairs()) {
            for (int i=0; i <= f.getArity(); i++) {
                final SimplePolynomial coeffG = this.abstractInterpretation.get(new Triple<FunctionSymbol, ArrayList<Boolean>, Integer>(f, p.x, i));
                final SimplePolynomial coeffS = this.abstractInterpretation.get(new Triple<FunctionSymbol, ArrayList<Boolean>, Integer>(f, p.y, i));
                this.masterConjuncts.add(ff.buildTheoryAtom(Diophantine.create(coeffG.minus(coeffS), ConstraintType.GE)));
            }
        }
    }

    public Pair<Formula<Diophantine>[], VarPolynomial> interpretTerm(final TRSTerm t, final Map<TRSVariable, ArrayList<Boolean>> mapping) {
        // TODO: Optimize, i.e. cache etc.
        VarPolynomial polresult;
        final Formula<Diophantine>[] result = new Formula[this.dimension];

        // For variables, get mapping.
        if (t instanceof TRSVariable) {
            for (int i=0; i< this.dimension; i++) {
                result[i] = this.ff.buildConstant(mapping.get(t).get(i));
            }
            polresult = this.variables.get((t));

        } else {
            final TRSFunctionApplication functionApplication = (TRSFunctionApplication)t;
            // Function application
            final Formula<Diophantine>[][][] arguments = new Formula[this.dimension][(functionApplication).getRootSymbol().getArity()][];
            final Formula<Diophantine>[][][] labarguments = new Formula[this.dimension][(functionApplication).getRootSymbol().getArity()][this.dimension];
            final Formula<Diophantine>[][][] andarguments = new Formula[this.dimension][(functionApplication).getRootSymbol().getArity()][this.dimension];
            final Formula<Diophantine>[][][] andlabarguments = new Formula[this.dimension][(functionApplication).getRootSymbol().getArity()][this.dimension];

            final FunctionSymbol f = functionApplication.getRootSymbol();
            final VarPolynomial[] polynomials = new VarPolynomial[f.getArity()];
            // Interpret arguments
            for (int i=0; i < f.getArity(); i++) {
                final Pair<Formula<Diophantine>[], VarPolynomial> ret = this.interpretTerm(functionApplication.getArgument(i), mapping);
                arguments[0][i] = ret.x;

                for (int j = 1; j < this.dimension; j++) {
                    arguments[j][i] = new Formula[this.dimension];
                }

                polynomials[i] = ret.y;

                for (int j=0; j < this.dimension; j++) {
                    for (int k=0; k <  this.dimension; k++) {
                        arguments[j][i][k] = arguments[0][i][k];
                        andlabarguments[j][i][k] = arguments[0][i][k];
                        andarguments[j][i][k] = arguments[0][i][k];
                        labarguments[j][i][k] = arguments[0][i][k];
                    }
                }




                for (int j=0; j < this.dimension; j++) {
                    // First, build the helper vars. These are the pi_i (|i| xor not_i) formulae.
                    // To do that, we simply re-map arguments[i], and labarguments.
                    for (int k=0; k < this.dimension; k++) {
                        arguments[j][i][k] = this.ff.buildAnd(
                                // The filter for the current argument
                                this.filter.get(f).get(new Triple<Integer, Integer, Integer>(j,i, k)),
                                // The not mask for the current argument
                                this.ff.buildXor(arguments[j][i][k], this.nots.get(f).get(new Triple<Integer, Integer, Integer>(j,i, k)))
                                // and the actual interpretation
                                );
                        labarguments[j][i][k] = this.ff.buildAnd(
                                // The filter for the current argument
                                this.labfilter.get(f).get(new Triple<Integer, Integer, Integer>(j,i, k)),
                                // The not mask for the current argument
                                this.ff.buildXor(labarguments[j][i][k], this.labnots.get(f).get(new Triple<Integer, Integer, Integer>(j,i, k)))
                                // and the actual interpretation
                                );
                        andarguments[j][i][k] = this.ff.buildOr(
                                // The filter for the current argument
                                this.ff.buildNot(this.filter.get(f).get(new Triple<Integer, Integer, Integer>(j,i, k))),
                                // The not mask for the current argument
                                this.ff.buildXor(andarguments[j][i][k], this.nots.get(f).get(new Triple<Integer, Integer, Integer>(j,i, k)))
                                // and the actual interpretation
                                );
                        andlabarguments[j][i][k] = this.ff.buildOr(
                                // The filter for the current argument
                                this.ff.buildNot(this.labfilter.get(f).get(new Triple<Integer, Integer, Integer>(j,i, k))),
                                // The not mask for the current argument
                                this.ff.buildXor(andlabarguments[j][i][k], this.labnots.get(f).get(new Triple<Integer, Integer, Integer>(j,i, k)))
                                // and the actual interpretation
                                );
                    }
                }
            }

            final Formula<Diophantine>[] label = new Formula[this.dimension];


            // For each result entry, generate the formula interpretation.
            // Also, generate the labelling function.
            for (int j=0; j < this.dimension; j++) {
                // The interpretation is basically a big or over our function pool.
                List<Formula<Diophantine>> cArgs = new ArrayList<Formula<Diophantine>>();
                List<Formula<Diophantine>> poolArgs = new ArrayList<Formula<Diophantine>>();
                List<Formula<Diophantine>> andpoolArgs = new ArrayList<Formula<Diophantine>>();

                for (int k=0; k < this.dimension; k++) {
                    for (int i=0; i < f.getArity(); i++) {
                        poolArgs.add(arguments[j][i][k]);
                    }
                }
                // We need that because 1 is the neutral of and
                for (int k=0; k < this.dimension;k++) {
                    for (int i=0; i < f.getArity(); i++) {
                        andpoolArgs.add(andarguments[j][i][k]);
                    }
                }


                // AND
                cArgs.add(this.ff.buildAnd(this.pool.get(f).get(new Pair<Integer, FunctionPool>(j, FunctionPool.AND)), this.ff.buildAnd(andpoolArgs)));

                // OR
                cArgs.add(this.ff.buildAnd(this.pool.get(f).get(new Pair<Integer, FunctionPool>(j, FunctionPool.OR)), this.ff.buildOr(poolArgs)));

                // XOR
                cArgs.add(this.ff.buildAnd(this.pool.get(f).get(new Pair<Integer, FunctionPool>(j, FunctionPool.XOR)), this.ff.buildXor(poolArgs)));

                result[j] = this.ff.buildOr(cArgs);

                // and so is the labelling. Hoever we now use the values passed to us in a different way...

                cArgs = new ArrayList<Formula<Diophantine>>();
                poolArgs = new ArrayList<Formula<Diophantine>>();
                andpoolArgs = new ArrayList<Formula<Diophantine>>();

                for (int k=0; k < this.dimension; k++) {
                    for (int i=0; i < f.getArity(); i++) {
                        poolArgs.add(labarguments[j][i][k]);
                    }
                }
                // We need that because 1 is the neutral of and
                for (int k=0; k < this.dimension; k++) {
                    for (int i=0; i < f.getArity(); i++) {
                        andpoolArgs.add(andlabarguments[j][i][k]);
                    }
                }


                // AND
                cArgs.add(this.ff.buildAnd(this.labpool.get(f).get(new Pair<Integer, FunctionPool>(j, FunctionPool.AND)), this.ff.buildAnd(andpoolArgs)));

                // OR
                cArgs.add(this.ff.buildAnd(this.labpool.get(f).get(new Pair<Integer, FunctionPool>(j, FunctionPool.OR)), this.ff.buildOr(poolArgs)));

                // XOR
                cArgs.add(this.ff.buildAnd(this.labpool.get(f).get(new Pair<Integer, FunctionPool>(j, FunctionPool.XOR)), this.ff.buildXor(poolArgs)));

                label[j] = this.ff.buildOr(cArgs);


            }

            // Now interpret this term as a polynomial
            final SimplePolynomial[] coefficients = new SimplePolynomial[f.getArity()];
            //SimplePolynomial constant = SimplePolynomial.create("tmp_interpretTerm_" + runningNum++ );
            final SimplePolynomial constant = SimplePolynomial.create(t + "_c::" + this.runningNum++ );

            polresult = VarPolynomial.create(constant);
            for (int i=0; i< f.getArity(); i++) {
//                coefficients[i] = SimplePolynomial.create("tmp_interpretTerm_" + runningNum++ );
                coefficients[i] = SimplePolynomial.create(t + "_" + i + "::" + this.runningNum++ );

                polresult = polresult.plus(VarPolynomial.create(coefficients[i]).times(polynomials[i]));
            }


            // and tie the coefficients to the respective label.
            for (final ArrayList<Boolean> lab: this.generateRepresentors(this.dimension)) {
                final List<Formula<Diophantine>> cArgs = new ArrayList<Formula<Diophantine>>();
                for (int i=0; i < this.dimension; i++) {
                    cArgs.add(this.ff.buildIff(label[i], this.ff.buildConstant(lab.get(i))));
                }

                final List<Formula<Diophantine>> eqConstr = new ArrayList<Formula<Diophantine>>();
                for (int i=0; i < f.getArity(); i++) {
                    eqConstr.add(this.ff.buildTheoryAtom(Diophantine.create(coefficients[i], this.abstractInterpretation.get(new Triple<FunctionSymbol, ArrayList<Boolean>, Integer>(f, lab, i+1)), ConstraintType.EQ)));
                }
                eqConstr.add(this.ff.buildTheoryAtom(Diophantine.create(constant, this.abstractInterpretation.get(new Triple<FunctionSymbol, ArrayList<Boolean>, Integer>(f, lab, 0)), ConstraintType.EQ)));

                this.masterConjuncts.add(this.ff.buildImplication(this.ff.buildAnd(cArgs), this.ff.buildAnd(eqConstr)));
                //masterConjuncts.add(ff.buildAnd(eqConstr));
                //masterConjuncts.add(ff.buildOr(ff.buildNot(ff.buildAnd(cArgs)), ff.buildAnd(cArgs)));
            }



        }


        for (int i = 0; i < this.dimension; i++) {
            this.values.put(new Pair<TRSTerm, Integer>(t, i), result[i]);
        }

        final Formula<Diophantine>[] v= new Formula[this.dimension];
        for (int i=0;i < this.dimension; i++) {
            v[i] = this.ff.buildVariable();
            this.masterConjuncts.add(this.ff.buildIff(result[i], v[i]));
            this.interestingVars.add(v[i]);
            this.termValues.put( new Triple<TRSTerm, Integer, Map<TRSVariable, ArrayList<Boolean>>>( t, i, mapping), v[i]);
        }

        return new Pair<Formula<Diophantine>[], VarPolynomial > (result, polresult);
    }

    /**
     * docu-guess (noschinski): Returns a set containing all variable mappings
     * to the domain of <code>dimension</code>-dimensional boolean vectors.
     */
    private Set<ArrayList<Boolean>> generateRepresentors(final int dimension) {
        final Set<ArrayList<Boolean>> resSet = new LinkedHashSet<ArrayList<Boolean>>();
        for (int i=0; i < AProVEMath.power(2,dimension); i++) {
            final ArrayList<Boolean> arr = new ArrayList<Boolean>(dimension);
            for (int j=0; j < dimension; j++) {
                arr.add((2*i & (2 << j)) != 0);
             }
            resSet.add(arr);
        }
        return resSet;
    }

    /**
     * docu-guess (noschinski): Generates all mappings from variables (from
     * <code>var</code>) to boolean lists of length <code>dimension</code>.
     */
    private void fillMappings(final Set<Map<TRSVariable, ArrayList<Boolean>>> mapping, final Set<TRSVariable> vars)  {


        final Set<ArrayList<Boolean>> repres = this.generateRepresentors(this.dimension);

        if (vars.size() == 0) {
            // Ground term. As a hack, label it by the empty mapping.
            mapping.add(new LinkedHashMap<TRSVariable, ArrayList<Boolean>>());
            return;
        }

        Iterator<TRSVariable> iter =  vars.iterator();
        final TRSVariable myVar = iter.next();
        iter.remove();
        iter = null;

        final Set<Map<TRSVariable, ArrayList<Boolean>>> subMapping = new LinkedHashSet<Map<TRSVariable,ArrayList<Boolean>>>();

        if (vars.size() != 0) {
            this.fillMappings(subMapping, vars);
        } else {
            subMapping.add(new LinkedHashMap<TRSVariable, ArrayList<Boolean>>());
        }

        for (final ArrayList<Boolean> rep: repres) {
            for (final Map<TRSVariable, ArrayList<Boolean>> subMap: subMapping) {
                final Map<TRSVariable, ArrayList<Boolean>> newMap = new LinkedHashMap<TRSVariable, ArrayList<Boolean>>();
                newMap.putAll(subMap);
                newMap.put(myVar, rep);
                mapping.add(newMap);
            }
        }

    }

    Map<SimplePolyConstraint, Rule> strictSPCs = new LinkedHashMap<SimplePolyConstraint, Rule>();



    public void interpretRule(final Rule r, final boolean trackStrict) {


        // First we extract all the variables in the rule.
        // Then, for each possible representation of the variables, we will encode [l]=[r].

        Set<TRSVariable> vars = r.getVariables();
        final Set<Map<TRSVariable, ArrayList<Boolean>>> mappings = new LinkedHashSet<Map<TRSVariable,ArrayList<Boolean>>>();
        this.fillMappings(mappings, vars);

        // Note that hereafter vars is empty again, denote that by
        vars = null;

        final Formula<Diophantine> strictVar = this.ff.buildVariable();
        if (trackStrict) {
            this.interestingVars.add(strictVar);
            this.isStrictMap.put(r, strictVar);
        }

        final List<Formula<Diophantine>> cArgs = new ArrayList<Formula<Diophantine>>();
        for (final Map<TRSVariable, ArrayList<Boolean>> mapping: mappings) {
            final Pair<Formula<Diophantine>[], VarPolynomial> retL =
                this.interpretTerm(r.getLeft(), mapping);
            final Pair<Formula<Diophantine>[], VarPolynomial> retR =
                this.interpretTerm(r.getRight(), mapping);
            final Formula<Diophantine>[] leftInter = retL.x;
            final Formula<Diophantine>[] rightInter = retR.x;
            final Formula<Diophantine> boolGT = this.ff.buildVariable();


            // For a start, use a monotonic order. Would >=lex also be ok for
            // quasi-models?
            for (int i=0; i<this.dimension; i++) {
                //cArgs.add(ff.buildIff(leftInter[i], rightInter[i]));
                cArgs.add(this.ff.buildImplication(rightInter[i], leftInter[i]));
                cArgs.add(this.ff.buildImplication(this.ff.buildAnd(leftInter[i], this.ff.buildNot(rightInter[i])), this.ff.buildAnd(this.isQuasi, boolGT)));
                cArgs.add(this.ff.buildImplication(boolGT, this.ff.buildAnd(leftInter[i], this.ff.buildNot(rightInter[i]))));
                BSLAutoSearchTermInterpretor.log.log(Level.FINEST, "Rule " + r.toString() + " Component " + Integer.toString(i) + "\n");
                BSLAutoSearchTermInterpretor.log.log(Level.FINEST, leftInter[i].toString() + "\n");
                BSLAutoSearchTermInterpretor.log.log(Level.FINEST, " !  =   ! \n");
                BSLAutoSearchTermInterpretor.log.log(Level.FINEST, rightInter[i].toString() + "\n");
            }


            // Also encode the polynomial constraint - unless we are in order-only mode
            if (!this.orderOnly) {
                final VarPolyConstraint vpc = new VarPolyConstraint(retL.y.minus(retR.y), ConstraintType.GE);
                final Set<SimplePolyConstraint> spcs = vpc.createCoefficientConstraints();
                for (final SimplePolyConstraint spc: spcs) {
                    this.masterConjuncts.add(this.ff.buildTheoryAtom(Diophantine.create(spc)));
                }

                // and if strictness is to be tracked, track it.
                if (trackStrict) {
                    final SimplePolyConstraint spc = vpc.createSearchStrictCoefficientConstraints().y;
                    final TheoryAtom<Diophantine> polyGT = this.ff.buildTheoryAtom(Diophantine.create(spc.getPolynomial().minus(SimplePolynomial.ONE), ConstraintType.GE));
                    this.masterConjuncts.add(this.ff.buildImplication(strictVar, this.ff.buildOr(polyGT, boolGT)));

                    this.strictSPCs.put(spc, r);

                }

            } else {
                this.masterConjuncts.add(this.ff.buildImplication(strictVar, boolGT));
            }

        }

        this.masterConjuncts.addAll(cArgs);
    }

    //DEBUG
    private final Set<Pair<TRSTerm, Map<TRSVariable, ArrayList<Boolean>>>> printSet = new LinkedHashSet<Pair<TRSTerm, Map<TRSVariable, ArrayList<Boolean>>>>();

    // Do we allow elimination of the form t ] s if M(t) > M(s) where M is the model function? (Only valid for quasi-models)
    // Will not affect search, but assertions. Since this is not proven yet, we first look for assertions here.
    private final boolean allowQuasiModelElimination = false;

    boolean getTermValue(final TRSTerm t, final int dimensionIndex, final Map<TRSVariable, ArrayList<Boolean>> mapping) {

        if (t instanceof TRSFunctionApplication) {
            final TRSFunctionApplication fApp = (TRSFunctionApplication) t;



            final ArrayList<Boolean> argList = new ArrayList<Boolean>();
            for (int i=0; i < fApp.getRootSymbol().getArity(); i++) {
                for (int k=0; k < this.dimension; k++) {

                    if (this.interestingVars.contains(this.filter.get(fApp.getRootSymbol()).get(new Triple<Integer, Integer, Integer>(dimensionIndex,i,k)))) {
                        if (this.interestingVars.contains(this.nots.get(fApp.getRootSymbol()).get(new Triple<Integer, Integer, Integer>(dimensionIndex,i,k)))) {
                            argList.add(!this.getTermValue(fApp.getArgument(i), k,
                                mapping));
                        } else {
                            argList.add(this.getTermValue(fApp.getArgument(i), k,
                                mapping));
                        }
                    }
                }
            }
            boolean c;
            if (this.interestingVars.contains(this.pool.get(fApp.getRootSymbol()).get(new Pair<Integer, FunctionPool>(dimensionIndex, FunctionPool.AND)))) {
                c = true;
                for(final boolean b: argList) {
                    c &= b;
                }
            } else if (this.interestingVars.contains(this.pool.get(fApp.getRootSymbol()).get(new Pair<Integer, FunctionPool>(dimensionIndex, FunctionPool.OR)))) {
                c = false;
                for(final boolean b: argList) {
                    c |= b;
                }
            } else if (this.interestingVars.contains(this.pool.get(fApp.getRootSymbol()).get(new Pair<Integer, FunctionPool>(dimensionIndex, FunctionPool.XOR)))) {
                c = false;
                for(final boolean b: argList) {
                    c ^= b;
                }
            } else {
                // This does not have a model!
                BSLAutoSearchTermInterpretor.log.log(Level.SEVERE, "No model assigned to " + t.toString());
                throw new RuntimeException("Model incorrect.");
            }
            if (c != this.interestingVars.contains(this.termValues.get( new Triple<TRSTerm, Integer, Map<TRSVariable, ArrayList<Boolean>>>( t, dimensionIndex, mapping)))) {
                BSLAutoSearchTermInterpretor.log.log(Level.FINEST, "SAT and Checker disagree on value of " + t.toString());
            }
            if (!this.printSet.contains(new Pair<TRSTerm, Map<TRSVariable, ArrayList<Boolean>>>(t, mapping))) {
                BSLAutoSearchTermInterpretor.log.log(Level.FINEST,  t.toString() + ": value :" + c + "[" + dimensionIndex + "]" + mapping.toString() + "\n");
                this.printSet.add(new Pair<TRSTerm, Map<TRSVariable, ArrayList<Boolean>>>(t, mapping));
            }
            return c;
        } else {
            // t instanceof Variable
            if (!this.printSet.contains(new Pair<TRSTerm, Map<TRSVariable, ArrayList<Boolean>>>(t, mapping))) {
                BSLAutoSearchTermInterpretor.log.log(Level.FINEST,  t.toString() + ": value :" + mapping.get(t).get(dimensionIndex) + "[" + dimensionIndex + "]" + mapping.toString() + "\n");
                this.printSet.add(new Pair<TRSTerm, Map<TRSVariable, ArrayList<Boolean>>>(t, mapping));
            }
            return mapping.get(t).get(dimensionIndex);
        }
    }

    boolean getTermLabel(final TRSTerm t, final int dimensionIndex, final Map<TRSVariable, ArrayList<Boolean>> mapping) {

        if (t instanceof TRSFunctionApplication) {
            final TRSFunctionApplication fApp = (TRSFunctionApplication) t;


            final ArrayList<Boolean> argList = new ArrayList<Boolean>();
            for (int i=0; i < fApp.getRootSymbol().getArity(); i++) {
                for (int k=0; k < this.dimension; k++) {
                    if (this.interestingVars.contains(this.labfilter.get(fApp.getRootSymbol()).get(new Triple<Integer, Integer, Integer>(dimensionIndex,i,k)))) {
                        if (this.interestingVars.contains(this.labnots.get(fApp.getRootSymbol()).get(new Triple<Integer, Integer, Integer>(dimensionIndex,i,k)))) {
                            argList.add(!this.getTermValue(fApp.getArgument(i), k,
                                mapping));
                        } else {
                            argList.add(this.getTermValue(fApp.getArgument(i), k,
                                mapping));
                        }
                    }
                }
            }

            boolean c;
            if (this.interestingVars.contains(this.labpool.get(fApp.getRootSymbol()).get(new Pair<Integer, FunctionPool>(dimensionIndex, FunctionPool.AND)))) {
                c = true;
                for(final boolean b: argList) {
                    c &= b;
                }
            } else if (this.interestingVars.contains(this.labpool.get(fApp.getRootSymbol()).get(new Pair<Integer, FunctionPool>(dimensionIndex, FunctionPool.OR)))) {
                c = false;
                for(final boolean b: argList) {
                    c |= b;
                }
            } else if (this.interestingVars.contains(this.labpool.get(fApp.getRootSymbol()).get(new Pair<Integer, FunctionPool>(dimensionIndex, FunctionPool.XOR)))) {
                c = false;
                for(final boolean b: argList) {
                    c ^= b;
                }
            } else {
                // This does not have a model!
                BSLAutoSearchTermInterpretor.log.log(Level.SEVERE, "No label assigned to " + t.toString() + "\n");
                throw new RuntimeException("Model incorrect.");
            }

            BSLAutoSearchTermInterpretor.log.log(Level.FINEST,  t.toString() + ": label :" + c + "[" + dimensionIndex + "]" + mapping.toString() + "\n");

            return c;

        } else {
            // t instanceof Variable
            return mapping.get(t).get(dimensionIndex);
        }
    }


    public VarPolynomial getTermPolynomial(final TRSTerm t, final Map<TRSVariable, ArrayList<Boolean>> mapping) {

        if (t instanceof TRSVariable) {
            return this.variables.get(t);
        } else {
            // t instanceof FunctionApplication
            final TRSFunctionApplication fApp = (TRSFunctionApplication) t;
            final FunctionSymbol f = fApp.getRootSymbol();

            VarPolynomial result = VarPolynomial.ZERO;
            final ArrayList<Boolean> label = this.getTermLabel(t, mapping);
            for (int i=0; i < f.getArity(); i++) {
                result = result.plus( this.getTermPolynomial(fApp.getArgument(i), mapping).times(this.abstractInterpretation.get(new Triple<FunctionSymbol, ArrayList<Boolean>, Integer>(f, label, i+1))));
            }
            result = result.plus(VarPolynomial.create(this.abstractInterpretation.get(new Triple<FunctionSymbol, ArrayList<Boolean>, Integer>(f, label, 0))));
            return result;
        }

    }

    public ArrayList<Boolean> getTermLabel(final TRSTerm t, final Map<TRSVariable, ArrayList<Boolean>> mapping) {
        final ArrayList<Boolean> ret = new ArrayList<Boolean> ();

        for (int i=0; i< this.dimension; i++) {
            ret.add(this.getTermLabel(t, i, mapping));
        }
        return ret;

    }


    public void checkPOLO(final Set<Rule> rules, final Map<String, BigInteger> goalState, final boolean strict) {

        for (final Rule r: rules) {
            final Set<TRSVariable> vars = r.getVariables();
            final Set<Map<TRSVariable, ArrayList<Boolean>>> mappings = new LinkedHashSet<Map<TRSVariable,ArrayList<Boolean>>>();
            this.fillMappings(mappings, vars);
            for (final Map<TRSVariable, ArrayList<Boolean>> mapping: mappings) {


                VarPolynomial res = this.getTermPolynomial(r.getLeft(), mapping).minus(this.getTermPolynomial(r.getRight(), mapping));
                res = res.specialize(goalState);
                VarPolyConstraint vpc = new VarPolyConstraint(res, !strict ? ConstraintType.GE: ConstraintType.GT);
                if (!vpc.isValid()) {
                    // we might still have a deletion by order;
                    // first however check that quasi was allowed, and this mode of elimination (hard-)enabled
                    if (this.quasiState == QUASI_MODE.DISABLE | this.allowQuasiModelElimination) {
                        BSLAutoSearchTermInterpretor.log.log(Level.SEVERE, "POLO solving in SemLab incorrect.");
                        throw new RuntimeException("POLO in SemLab incorrect.");
                    }

                    // still the nonstrict constraint needs to be valid:
                    vpc = new VarPolyConstraint(res, ConstraintType.GE);
                    if (!vpc.isValid()) {
                        BSLAutoSearchTermInterpretor.log.log(Level.SEVERE, "POLO solving in SemLab incorrect.");
                        throw new RuntimeException("POLO in SemLab incorrect.");
                    }

                    // ok, check whether the value is bigger.
                    boolean check = false;
                    for (int i = 0; i < this.dimension; i++) {
                        // is the left side larger (we need that once)?
                        check =
                            check
                                | (this.getTermValue(r.getLeft(), i, mapping) & !(this.getTermValue(
                                    r.getRight(), i, mapping)));
                        // is the right side even larger? May not happen at all.
                        if (!this.getTermValue(r.getLeft(), i, mapping) & (this.getTermValue(r.getRight(), i, mapping) )) {
                            // redundant as this is already detected by checkmodel, but to be safe...
                            BSLAutoSearchTermInterpretor.log.log(Level.SEVERE, "POLO solving in SemLab incorrect.");
                            throw new RuntimeException("POLO in SemLab incorrect.");
                        }
                    }



                }


            }
        }

    }


    public void checkModel(final Set<Rule> rules) {

        this.dump();

        for (final Rule r: rules) {
            final Set<TRSVariable> vars = r.getVariables();
            final Set<Map<TRSVariable, ArrayList<Boolean>>> mappings = new LinkedHashSet<Map<TRSVariable,ArrayList<Boolean>>>();
            this.fillMappings(mappings, vars);
            for (final Map<TRSVariable, ArrayList<Boolean>> mapping: mappings) {
                for (int i=0; i<this.dimension; i++) {
                    if (!this.interestingVars.contains(this.isQuasi)) {
                        // Models only.

                        if (this.getTermValue(r.getLeft(), i, mapping) != this.getTermValue(r.getRight(), i, mapping)) {
                            // We did not find a model!
                            BSLAutoSearchTermInterpretor.log.log(Level.SEVERE, "Wrong model found!");
                            throw new RuntimeException("Model incorrect.");
                        }
                    } else {
                        if (!this.getTermValue(r.getLeft(), i, mapping) & this.getTermValue(r.getRight(), i, mapping)) {
                            // We did not find a quasi-model!
                            BSLAutoSearchTermInterpretor.log.log(Level.SEVERE, "Wrong quasi-model found!");
                            throw new RuntimeException("Model incorrect.");

                        }

                    }
                }

            }
        }

    }


    public TRSTerm getLabelledTerm(final TRSTerm t, final Map<String, BigInteger> goalState, final Map<TRSVariable, ArrayList<Boolean>> mapping) {

        if (t instanceof TRSVariable) {
            String newName;
            newName = "[";
            for (int i = 0; i < this.dimension; i++) {
                newName = newName + (i != 0 ? ";" : "") + (this.getTermValue(t, i, mapping) ? "t": "f");
            }
            newName = newName + "]|" + ((TRSVariable) t).getName();
            return TRSTerm.createVariable(newName);
        } else { // t instanceof FunctionApplication
            final TRSFunctionApplication f = (TRSFunctionApplication) t;
            String newName;
            newName = "[";
            for (int i = 0; i < this.dimension; i++) {
                newName = newName + (i != 0 ? ";" : "") + (this.getTermValue(t, i, mapping) ? "t": "f");
            }
            newName = newName + "]|" + f.getRootSymbol().getName() + "|[";
            for (int i = 0; i < this.dimension; i++) {
                newName = newName + (i != 0 ? ";" : "") + (this.getTermLabel(t, i, mapping) ? "t": "f");
            }
            newName = newName + "]";
            final ImmutableList<? extends TRSTerm> arguments = f.getArguments();
            final ArrayList<TRSTerm> newArgs = new ArrayList<TRSTerm>();
            for (final TRSTerm s: arguments) {
                newArgs.add(this.getLabelledTerm(s, goalState, mapping));
            }
            return
                TRSTerm.createFunctionApplication(
                    FunctionSymbol.create(newName, f.getRootSymbol().getArity()),
                    ImmutableCreator.create(newArgs)
                );
        }
    }


    public Set<Rule> getLabelledSystem(final Set<Rule> rules, final Map<String, BigInteger> goalState) {
        final Set<Rule> result = new LinkedHashSet<Rule>();
        for (final Rule r: rules) {
            final Set<TRSVariable> vars = r.getVariables();
            final Set<Map<TRSVariable, ArrayList<Boolean>>> mappings =
                new LinkedHashSet<Map<TRSVariable,ArrayList<Boolean>>>();
            this.fillMappings(mappings, vars);
            for (final Map<TRSVariable, ArrayList<Boolean>> mapping: mappings) {
                result.add(
                    Rule.create(
                        (TRSFunctionApplication)this.getLabelledTerm(r.getLeft(), goalState, mapping),
                        this.getLabelledTerm(r.getRight(), goalState, mapping)
                    )
                );
            }
        }
        return result;
    }



    public String getProof(final Export_Util o) {
        final StringBuilder proof = new StringBuilder();
        proof.append(o.newline());
        proof.append(o.newline());
        proof.append("We use semantic labelling over boolean tuples of size " + this.dimension + ".");
        proof.append(o.newline());
        proof.append(o.newline());
        proof.append("We used the following " + (this.interestingVars.contains(this.isQuasi) ? "quasi":"") + "model:");
        proof.append(o.newline());

        // first dump the selected functions, filters and notfilters.
        for (final FunctionSymbol f: this.signature) {
            proof.append (f.getName() + o.sub(Integer.toString(f.getArity())) + ": ");

            for (int i =0; i < this.dimension; i++) {

                if (this.interestingVars.contains(this.pool.get(f).get(new Pair<Integer, FunctionPool>(i, FunctionPool.AND)))) {
                    proof.append("component " + (i+1) + ": AND[");
                }
                if (this.interestingVars.contains(this.pool.get(f).get(new Pair<Integer, FunctionPool>(i, FunctionPool.OR)))) {
                    proof.append("component " + (i+1) + ": OR[");
                }
                if (this.interestingVars.contains(this.pool.get(f).get(new Pair<Integer, FunctionPool>(i, FunctionPool.XOR)))) {
                    proof.append("component " + (i+1) + ": XOR[");
                }

                boolean firstEl = true;
                for (int j=0; j < f.getArity(); j++) {
                    for (int k=0; k< this.dimension; k++) {
                        if (this.interestingVars.contains(this.filter.get(f).get(new Triple<Integer, Integer, Integer>(i,j,k)))) {
                            if (!firstEl) {
                                proof.append(", ");
                            }
                            firstEl = false;
                            if (this.interestingVars.contains(this.nots.get(f).get(new Triple<Integer, Integer, Integer>(i,j,k)))) {
                                proof.append ("-");
                            }
                            proof.append("x" + o.sub(Integer.toString(j+1))  + o.sup(Integer.toString(k+1)));
                        }
                    }
                }
                proof.append("]");
                proof.append(o.newline());

            }

        }

        proof.append(o.newline());
        proof.append("Our labelling function was:");
        proof.append(o.newline());

        // first dump the selected functions, filters and notfilters.
        for (final FunctionSymbol f: this.signature) {
            proof.append (f.getName() + o.sub(Integer.toString(f.getArity())) + ":");

            for (int i =0; i < this.dimension; i++) {

                if (this.interestingVars.contains(this.labpool.get(f).get(new Pair<Integer, FunctionPool>(i, FunctionPool.AND)))) {
                    proof.append("component " + (i+1) +": AND[");
                }
                if (this.interestingVars.contains(this.labpool.get(f).get(new Pair<Integer, FunctionPool>(i, FunctionPool.OR)))) {
                    proof.append("component " + (i+1) + ": OR[");
                }
                if (this.interestingVars.contains(this.labpool.get(f).get(new Pair<Integer, FunctionPool>(i, FunctionPool.XOR)))) {
                    proof.append("component " + (i+1) + ": XOR[");
                }

                boolean firstEl = true;
                for (int j=0; j < f.getArity(); j++) {
                    for (int k=0; k< this.dimension; k++) {
                        if (this.interestingVars.contains(this.labfilter.get(f).get(new Triple<Integer, Integer, Integer>(i,j,k)))) {
                            if (!firstEl) {
                                proof.append(", ");
                            }
                            firstEl = false;
                            if (this.interestingVars.contains(this.labnots.get(f).get(new Triple<Integer, Integer, Integer>(i,j,k)))) {
                                proof.append ("-");
                            }
                            proof.append("x" + o.sub(Integer.toString(j+1))  + o.sup(Integer.toString(k+1)));
                        }
                    }
                }
                proof.append("]");
                proof.append(o.newline());

            }

        }

        if (this.specialized) {
            proof.append(o.newline() + o.newline() + "Our labelled system was:" + o.newline());
            for (final Rule r: this.getLabelledSystem(this.rules, this.goalState)){
                proof.append(o.export(r));
                proof.append(o.newline());
            }

        } else  {
            BSLAutoSearchTermInterpretor.log.log(Level.SEVERE, "Tried to output proof of unspecialized BSLAutoSearchTermInterpretor.");
            if (Globals.useAssertions) {
                assert false;
            }
        }


        proof.append(o.newline() + o.newline() +  "Our polynomial interpretation was:" + o.newline()) ;
        // Now output the interpretations for the symbols
        final Set<ArrayList<Boolean>> repres = this.generateRepresentors(this.dimension);
        for (final FunctionSymbol f: this.signature) {
            for(final ArrayList<Boolean> r: repres) {
                proof.append(o.calligraphic("P")+ "(" + f.getName() +o.sup(r.toString()) + ")");
                int arity = f.getArity();
                switch (arity) {
                case 0:
                    proof.append('(');
                    break;
                case 1:
                    proof.append("(" + o.fontcolor("x", Color.RED)
                        + o.sub("1"));
                    break;
                case 2:
                    proof.append("(" + o.fontcolor("x", Color.RED)
                        + o.sub("1") + "," + o.fontcolor("x", Color.RED)
                        + o.sub("2"));
                    break;
                default:
                    proof.append("(" + o.fontcolor("x", Color.RED)
                        + o.sub("1") + ",...,"
                        + o.fontcolor("x", Color.RED)
                        + o.sub(Integer.toString(arity)));
                }
                proof.append(") = ");
                proof.append(o.export(
                         (this.abstractInterpretation.get(
                                 new  Triple<FunctionSymbol, ArrayList<Boolean>, Integer>(f, r, 0)
                         ).specialize(this.result))));

                for (int i=1; i <= arity; i++) {
                    proof.append(" + ");
                    proof.append(o.export(
                            (this.abstractInterpretation.get(
                                    new  Triple<FunctionSymbol, ArrayList<Boolean>, Integer>(f, r, i)
                            ).specialize(this.result))));
                    proof.append(o.multSign());
                    proof.append(o.fontcolor("x", Color.RED)
                        + o.sub(o.export(i)));
                }

                proof.append(o.newline());
            }

        }


        return proof.toString();

    }


}


