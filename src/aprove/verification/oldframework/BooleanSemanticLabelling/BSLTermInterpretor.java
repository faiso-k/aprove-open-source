package aprove.verification.oldframework.BooleanSemanticLabelling;

import java.util.*;

import aprove.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.TheoryPropositions.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 *
 * @author Patrick Kabasci
 * @version $Id$
 */
public class BSLTermInterpretor {

    /**
     * docu-guess (noschinski): Stores the variables which decide whether the
     * i-th component of the j-th argument of a function symbol is filtered.
     * Retrieve those via:
     *
     * <code>filter.get(functionSymbol).get(new Pair(i,j))</code>
     */
    Map<FunctionSymbol, Map<Pair<Integer, Integer>, Formula<None>>> filter =
        new LinkedHashMap<FunctionSymbol, Map<Pair<Integer, Integer>, Formula<None>>>();

    /**
     * docu-guess (noschinski): Stores the variable which decides whether the
     * i-th component of the j-th argument of a function symbol is negated.
     */
    Map<FunctionSymbol, Map<Pair<Integer, Integer>, Formula<None>>> nots =
        new LinkedHashMap<FunctionSymbol, Map<Pair<Integer, Integer>, Formula<None>>>();

    /**
     * docu-guess (noschinski): Stores the variable which decides whether the
     * i-th component of a function symbol is to be computed with some
     * element from FunctionPool.
     */
    Map<FunctionSymbol, Map<Pair<Integer, FunctionPool>, Formula<None>>> pool =
        new LinkedHashMap<FunctionSymbol, Map<Pair<Integer, FunctionPool>,Formula<None>>>();

    /**
     * docu-guess: Contains all variables form <code>filter</code>, <code>nots</code>,
     * <code>pool</code>
     */
    Collection<Formula<None>> variables = new LinkedHashSet<Formula<None>>();

    /**
     * dimension of the boolean vectors
     */
    private int dimension;

    Map<Triple<Map<TRSVariable, List<Boolean>>, TRSTerm, Integer>, Formula<None>> values =
        new LinkedHashMap<Triple<Map<TRSVariable, List<Boolean>>, TRSTerm,Integer>, Formula<None>>();



    private FormulaFactory<None> ff;
    private Formula<None> isQuasi;

    public Formula<None> getQuasiVar() {
        return this.isQuasi;
    }

    public enum FunctionPool {
        AND,
        OR,
        XOR//,
        //ONE We'll see whether we want that.
    }

    public Formula<None>[] getValue(TRSTerm t, Map<TRSVariable, List<Boolean>> mapping) {
        Formula<None>[] result = new Formula[this.dimension];
        for (int i=0; i < this.dimension; i++) {
            result[i] = this.values.get(new Triple<Map<TRSVariable, List<Boolean>>,TRSTerm, Integer>(mapping,t,i));
        }
        return result;
    }


    /**
     * docu-guess (noschinski):
     * @param ff
     * @param dimension
     * @param signature
     * @param irrelevantSignature
     * @param quasiOK
     *          Quasi models are allowed.
     * @param enforceQuasi
     *          Must be a real quasi model. If true, <code>quasiOK</code> must
     *          also be true.
     * @return
     */
    public Formula<None> init(FormulaFactory<None> ff, int dimension, Set<FunctionSymbol> signature, Set<FunctionSymbol> irrelevantSignature, boolean quasiOK, boolean enforceQuasi) {
        if (Globals.useAssertions) {
            assert(quasiOK || !enforceQuasi);
        }
        this.ff = ff;
        this.dimension = dimension;

        // Generate quasi
        this.isQuasi = ff.buildVariable();

        List<Formula<None>> cArgs = new ArrayList<Formula<None>>();

        if (!quasiOK) {
            cArgs.add(ff.buildNot(this.isQuasi));
        } else if (enforceQuasi) {
            cArgs.add(this.isQuasi);
        }


        for (FunctionSymbol f: signature) {
            this.filter.put(f, new LinkedHashMap<Pair<Integer,Integer>, Formula<None>>());
            this.nots.put(f, new LinkedHashMap<Pair<Integer,Integer>, Formula<None>>());
            this.pool.put(f, new LinkedHashMap<Pair<Integer,FunctionPool>, Formula<None>>());
            // First, generate pi and nots
            for (int i =0; i < dimension; i++) {
                for (int j=0; j < f.getArity(); j++) {
                    Formula<None> filterVar = ff.buildVariable();
                    this.filter.get(f).put(new Pair<Integer, Integer>(i,j), filterVar);
                    this.variables.add(filterVar);
                    Formula<None> not = ff.buildVariable();
                    this.nots.get(f).put(new Pair<Integer, Integer>(i,j), not);
                    this.variables.add(not);
                    // Not is forbidden if quasi is set.
                    cArgs.add(ff.buildImplication(this.isQuasi, ff.buildNot(not)));
                }

                // Now prepare the interpretation pool. Note that only exactly one is allowed.
                // Though one can lift that if quasi is not set (but contradicts our intuition)
                Formula<None> andVar = ff.buildVariable();
                Formula<None> orVar = ff.buildVariable();
                Formula<None> xorVar = ff.buildVariable();
                Formula[] fpool = {andVar, orVar, xorVar};

                this.pool.get(f).put(new Pair<Integer, FunctionPool>(i, FunctionPool.AND), andVar);
                this.pool.get(f).put(new Pair<Integer, FunctionPool>(i, FunctionPool.OR), orVar);
                this.pool.get(f).put(new Pair<Integer, FunctionPool>(i, FunctionPool.XOR), xorVar);
                this.variables.add(andVar);
                this.variables.add(orVar);
                this.variables.add(xorVar);


                Formula<None> exactlyOne = new SATPatterns<None>(ff).encodeExactlyOne(fpool);
                cArgs.add(exactlyOne);
                // Quasi-Models do not allow XOR.
                cArgs.add(ff.buildImplication(this.isQuasi, ff.buildNot(xorVar)));

            }
        }

        for (FunctionSymbol f: irrelevantSignature) {
            this.filter.put(f, new LinkedHashMap<Pair<Integer,Integer>, Formula<None>>());
            this.nots.put(f, new LinkedHashMap<Pair<Integer,Integer>, Formula<None>>());
            this.pool.put(f, new LinkedHashMap<Pair<Integer,FunctionPool>, Formula<None>>());
            // First, generate pi and nots
            for (int i =0; i < dimension; i++) {
                for (int j=0; j < f.getArity(); j++) {
                    this.filter.get(f).put(new Pair<Integer, Integer>(i,j), ff.buildConstant(false));
                    Formula<None> not = ff.buildConstant(false);
                    this.nots.get(f).put(new Pair<Integer, Integer>(i,j), not);

                }

                // Now prepare the interpretation pool. Note that only exactly one is allowed.
                // Though one can lift that if quasi is not set (but contradicts our intuition)
                Formula<None> andVar = ff.buildConstant(false);
                Formula<None> orVar = ff.buildConstant(true);
                Formula<None> xorVar = ff.buildConstant(false);

                this.pool.get(f).put(new Pair<Integer, FunctionPool>(i, FunctionPool.AND), andVar);
                this.pool.get(f).put(new Pair<Integer, FunctionPool>(i, FunctionPool.OR), orVar);
                this.pool.get(f).put(new Pair<Integer, FunctionPool>(i, FunctionPool.XOR), xorVar);



                // Quasi-Models do not allow XOR.
                cArgs.add(ff.buildImplication(this.isQuasi, ff.buildNot(xorVar)));

            }
        }



        return ff.buildAnd(cArgs);

    }

    public Formula<None>[] interpretTerm(TRSTerm t, Map<TRSVariable, List<Boolean>> mapping) {
        // TODO: Optimize, i.e. cache etc.

        Formula<None>[] result = new Formula[this.dimension];

        // For variables, get mapping.
        if (t instanceof TRSVariable) {
            for (int i=0; i < this.dimension; i++) {
                result[i] = this.ff.buildConstant(mapping.get(t).get(i));
            }
        } else {
            TRSFunctionApplication functionApplication = (TRSFunctionApplication) t;
            // Function application
            Formula<None>[][] arguments =
                new Formula[functionApplication.getRootSymbol().getArity()][];
            Formula<None>[][] andarguments =
                new Formula[functionApplication.getRootSymbol().getArity()][this.dimension];


            // Interpret arguments
            for (int i=0; i < functionApplication.getRootSymbol().getArity(); i++) {
                arguments[i] = this.interpretTerm(functionApplication.getArgument(i), mapping);
                // First, build the helper vars. These are the pi_i (1 xor not_i) |i| formulae.
                // To do that, we simply re-map arguments[i]
                for (int j = 0; j < this.dimension; j++) {
                    // for AND the formula looks different, because filtering
                    // away some argument means having a 1 instead. So AND() = 1
                    // when all arguments are filtered away.
                    andarguments[i][j] = this.ff.buildOr(
                            // The filter for the current argument
                            this.ff.buildNot(this.filter.get(functionApplication.getRootSymbol()).get(new Pair<Integer, Integer>(j, i))),

                            // The not mask for the current argument
                            // and the actual interpretation
                            this.ff.buildXor(
                                    this.nots.get(functionApplication.getRootSymbol()).get(new Pair<Integer, Integer>(j,i)),
                                    arguments[i][j]
                            )
                    );


                    arguments[i][j] = this.ff.buildAnd(
                            // The filter for the current argument
                            this.filter.get(functionApplication.getRootSymbol()).get(new Pair<Integer, Integer>(j,i)),

                            // The not mask for the current argument
                            // and the actual interpretation
                            this.ff.buildXor(
                                    this.nots.get(functionApplication.getRootSymbol()).get(new Pair<Integer, Integer>(j,i)),
                                    arguments[i][j]
                                    )
                            );
                }
            }


            // For each result entry, generate the formula interpretation
            for (int i=0; i < this.dimension; i++) {
                // The interpretation is basically a big or over our function pool.
                List<Formula<None>> cArgs = new ArrayList<Formula<None>>();
                List<Formula<None>> poolArgs = new ArrayList<Formula<None>>();
                List<Formula<None>> andPoolArgs = new ArrayList<Formula<None>>();

                for (int j = 0; j < this.dimension; j++) {
                    for (int k = 0; k < functionApplication.getRootSymbol().getArity(); k++) {
                        poolArgs.add(arguments[k][j]);
                        andPoolArgs.add(andarguments[k][j]);
                    }
                }

                // AND
                // take care, use andPoolArgs
                cArgs.add(
                        this.ff.buildAnd(
                                this.pool.get(functionApplication.getRootSymbol()).get(new Pair<Integer, FunctionPool>(i, FunctionPool.AND)),
                                this.ff.buildAnd(andPoolArgs)
                                )
                        );

                // OR
                cArgs.add(
                        this.ff.buildAnd(
                                this.pool.get(functionApplication.getRootSymbol()).get(new Pair<Integer, FunctionPool>(i, FunctionPool.OR)),
                                this.ff.buildOr(poolArgs)
                                )
                        );

                // XOR
                cArgs.add(
                        this.ff.buildAnd(
                                this.pool.get(functionApplication.getRootSymbol()).get(new Pair<Integer, FunctionPool>(i, FunctionPool.XOR)),
                                this.ff.buildXor(poolArgs)
                                )
                        );

                result[i] = this.ff.buildOr(cArgs);
            }

        }

        for (int i = 0; i < this.dimension; i++) {
            this.values.put(new Triple<Map<TRSVariable, List<Boolean>>, TRSTerm, Integer>(mapping, t, i), result[i]);
        }

        return result;
    }

    /**
     * docu-guess (noschinski): Returns a set containing all variable mappings
     * to the domain of <code>dimension</code>-dimensional boolean vectors.
     */
    private Set<List<Boolean>> generateRepresentors(int dimension) {
        int imax = AProVEMath.power(2,dimension);
        Set<List<Boolean>> resSet = new LinkedHashSet<List<Boolean>>(imax);
        for (int i=0; i < imax; i++) {
            List<Boolean> arr = new ArrayList<Boolean>(dimension);
            for (int j=0; j < dimension; j++) {
                arr.add(j, (i & AProVEMath.power(2, j)) != 0);
             }
            resSet.add(arr);
        }
        return resSet;
    }

    /**
     * docu-guess (noschinski): Generates all mappings from variables (from
     * <code>var</code>) to boolean lists of length <code>dimension</code>.
     */
    private void fillMappings(Set<Map<TRSVariable, List<Boolean>>> mapping, Set<TRSVariable> vars)  {

        Set<List<Boolean>> repres = this.generateRepresentors(this.dimension);

        Iterator<TRSVariable> iter =  vars.iterator();
        if (iter.hasNext()) {
            TRSVariable myVar = iter.next();
            iter.remove();
            iter = null;

            Set<Map<TRSVariable, List<Boolean>>> subMapping = new LinkedHashSet<Map<TRSVariable, List<Boolean>>>();

            if (vars.size() != 0) {
                this.fillMappings(subMapping, vars);
            } else {
                subMapping.add(new LinkedHashMap<TRSVariable, List<Boolean>>());
            }

            for (List<Boolean> rep : repres) {
                for (Map<TRSVariable, List<Boolean>> subMap: subMapping) {
                    Map<TRSVariable, List<Boolean>> newMap =
                        new LinkedHashMap<TRSVariable, List<Boolean>>(subMap.size() + 1);
                    newMap.putAll(subMap);
                    newMap.put(myVar, rep);
                    mapping.add(newMap);
                }
            }
        }

    }


    /**
     * docu-guess (noschinski): For each interpretation of variables, encode
     * the constraint [l] = [r] or ([l] > [r] and isQuasi)
     */
    public Formula<None> interpretRule(Rule r) {

        // First we extract all the variables in the rule.
        // Then, for each possible representation of the variables, we will encode [l]=[r].

        Set<Map<TRSVariable, List<Boolean>>> mappings = new LinkedHashSet<Map<TRSVariable,List<Boolean>>>();
        this.fillMappings(mappings, r.getVariables());

        List<Formula<None>> cArgs = new ArrayList<Formula<None>>();
        if (mappings.size() == 0) {
            // In the loop below, we need one iteration, even if there is no
            // variable
            mappings.add(null);
        }
        for (Map<TRSVariable, List<Boolean>> mapping : mappings) {
            Formula<None>[] leftInter = this.interpretTerm(r.getLeft(), mapping);
            Formula<None>[] rightInter = this.interpretTerm(r.getRight(), mapping);

            // For a start, use a monotonic order. Would >=lex also be ok for quasi-models?
            for (int i = 0; i < this.dimension; i++) {
                cArgs.add(this.ff.buildImplication(rightInter[i], leftInter[i]));
                cArgs.add(this.ff.buildImplication(this.ff.buildAnd(leftInter[i], this.ff.buildNot(rightInter[i])), this.isQuasi));
            }

        }

        return this.ff.buildAnd(cArgs);
    }


    public Formula<None> getModelFormula(int[] solution) {
        Formula<None> result = this.ff.buildConstant(true);
        for (Formula<None> var : this.variables) {
            int id = var.getId();
            if (solution[id - 1] == id) {
                result = this.ff.buildAnd(result, var);
            } else {
                result = this.ff.buildAnd(result, this.ff.buildNot(var));
            }
        }
        return result;
    }


    public Formula<None> getFunction(FunctionSymbol fs, int i, FunctionPool func) {
        if (this.pool.containsKey(fs)) {
            return this.pool.get(fs).get(new Pair<Integer, FunctionPool>(i, func));
        } else {
            return null;
        }
    }

    public Formula<None> getFilter(FunctionSymbol fs, int i, int j) {
        if (this.filter.containsKey(fs)) {
            return this.filter.get(fs).get(new Pair<Integer, Integer>(i, j));
        } else {
            return null;
        }
    }

    public Formula<None> getNot(FunctionSymbol fs, int i, int j) {
        if (this.nots.containsKey(fs)) {
            return this.nots.get(fs).get(new Pair<Integer, Integer>(i, j));
        } else {
            return null;
        }
    }
}

