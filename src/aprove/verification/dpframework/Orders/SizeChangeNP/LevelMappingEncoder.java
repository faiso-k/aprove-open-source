package aprove.verification.dpframework.Orders.SizeChangeNP;

import java.util.*;
import java.util.Map.Entry;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.Algebra.Polynomials.SatSearch.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.TheoryPropositions.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * Encoder for tagged level mappings for SCNP in the spirit of
 * the TACAS'08 paper by Ben-Amram and Codish.
 *
 * TODO Possible optimizations:
 * - unary encoding for tags
 * - maximum value of a tag <= number of overall /regarded/ args
 *   (can be done in post-processing)
 * - encode Var(pi(l)) \subseteq Var(pi(r)) (requires some some of
 *   QActiveConditions for variable positions)
 * - enforce that regarded(F,i) can *only* become true if it is
 *   actually used to satisfy a comparison
 *
 * @author Carsten Fuhs
 */
public class LevelMappingEncoder {

    // constant that is inherently different to all possible argument positions
    private static final int ROOT_ARG_POS = -1;

    // is this a /plain/ level mapping? then all argument tags are 0.
    private final boolean plain;

    // is this a /plain-rooted/ level mapping? then the root tags are 0.
    private final boolean plainRoot;

    // use the whole tuple term as additional argument
    private final boolean rootArg;

    // use the list of regular arguments
    private final boolean listArgs;

    // maximum value an argument tag can take
    private final int maxArgTag;

    // maximum value a root tag can take
    private final int maxRootTag;

    // will be used internally
    private final FormulaFactory<None> ff;
    private final ArithmeticCircuitFactory arithmeticFactory;
    private final Formula<None> ZERO;
    private final Formula<None> ONE;

    // for the tags of the level mapping
    private final IndefiniteBinarizer<Pair<FunctionSymbol, Integer>> binarizer;


    // unfiltered.get(F).get(i) becomes true
    // iff the i-th argument of F is not filtered away.
    private final Map<FunctionSymbol, List<Formula<None>>> regarded;

    // tags.get(F).x.get(i) is a formula tuple that
    // denotes the (for now binary) encoding of the i-th tag of F
    // (i.e., a natural number).
    // tags.get(F).y is a formula tuple that
    // denotes the (for now binary) encoding of the root tag of F
    // (i.e., a natural number).
    private final Map<FunctionSymbol, Pair<List<List<Formula<None>>>,List<Formula<None>>>> tags;


    public LevelMappingEncoder(boolean plain, boolean plainRoot, boolean rootArg, boolean listArgs, FormulaFactory<None> ff, ArithmeticCircuitFactory arithmeticFactory, Set<? extends GeneralizedRule> P) {
        this.plain = plain;
        this.plainRoot = plainRoot;
        this.rootArg = rootArg;
        this.listArgs = listArgs;
        this.ff = ff;
        this.arithmeticFactory = arithmeticFactory;
        this.ZERO = ff.buildConstant(false);
        this.ONE = ff.buildConstant(true);
        this.binarizer = IndefiniteBinarizer.create(ff);
        this.maxArgTag = this.sumRootArities(P) - 1;
        this.maxRootTag = LevelMappingEncoder.numRootSymbols(P) - 1;
        this.regarded = new LinkedHashMap<FunctionSymbol, List<Formula<None>>>();
        this.tags = new LinkedHashMap<FunctionSymbol, Pair<List<List<Formula<None>>>,List<Formula<None>>>>();
    }

    /**
     * @param f
     * @return whether this level mapping contains information on f
     *  (i.e., whether it has prop. vars for its arg.filter tag or for its tag)
     */
    public boolean knows(FunctionSymbol f) {
        return this.regarded.containsKey(f) || this.tags.containsKey(f);
    }

    /**
     * @param knownTrue
     * @return a LevelMapping that corresponds to exactly the formulae of
     *  knownTrue being interpreted as true
     */
    public LevelMapping decode(Set<Integer> knownTrue) {
        LevelMapping res = new LevelMapping(this.rootArg);
        for (Entry<FunctionSymbol, List<Formula<None>>> e : this.regarded.entrySet()) {
            FunctionSymbol f = e.getKey();
            List<Formula<None>> regardedFormulae = e.getValue();
            int length = regardedFormulae.size();
            boolean[] regardedValues = new boolean[length];
            for (int i = 0; i < length; ++i) {
                Formula<None> fi = regardedFormulae.get(i);
                regardedValues[i] = fi == this.ONE || knownTrue.contains(fi.getId());
            }
            res.putRegarded(f, regardedValues);
        }
        for (Entry<FunctionSymbol, Pair<List<List<Formula<None>>>,List<Formula<None>>>> e : this.tags.entrySet()) {
            FunctionSymbol f = e.getKey();
            List<List<Formula<None>>> tagsFormulae = e.getValue().x;
            int length = tagsFormulae.size();
            int[] argTagValues = new int[length];
            for (int i = 0; i < length; ++i) {
                List<Formula<None>> tagi = tagsFormulae.get(i);
                argTagValues[i] = this.binarizer.nat(tagi, knownTrue);
            }
            int rootTagValue = this.binarizer.nat(e.getValue().y, knownTrue);
            res.putTags(f, argTagValues, rootTagValue);
        }
        return res;
    }


    /**
     * @param F
     * @return a list of formulae whose i-th entry denotes that
     *  F regards its i-th argument (in the present level mapping),
     *  side effect: will create such a list if not yet present
     */
    public List<Formula<None>> getRegardedList(FunctionSymbol F) {
        List<Formula<None>> regardedArgs = this.regarded.get(F);
        if (regardedArgs == null) {
            int n = F.getArity() + (this.rootArg ? 1 : 0);
            regardedArgs = new ArrayList<Formula<None>>(n);
            boolean noList = this.rootArg && !this.listArgs;
            for (int i = n; i > 0; --i) {
                Formula<None> freshVar = noList ? (i == n ? this.ONE : this.ZERO) : this.ff.buildVariable();
                regardedArgs.add(freshVar);
            }
            this.regarded.put(F, regardedArgs);
        }
        return regardedArgs;
    }

    /**
     * @param F
     * @param i - 0 <= i <= F.getArity() - 1
     * @return a formula that expresses that F regards
     *  its i-th argument (in the present level mapping),
     *  side effect: will create such a list of such formulas
     *  if not yet present
     */
    public Formula<None> getRegardedAt(FunctionSymbol F, int i) {
        return this.getRegardedList(F).get(i);
    }

    /**
     * Also creates the tags for all arguments if not yet there.
     *
     * @param F
     * @return the list of tags for F
     */
    public List<List<Formula<None>>> getArgTagList(FunctionSymbol F) {
        return this.getTagList(F).x;
    }

    /**
     * Also creates the tags for all arguments if not yet there.
     *
     * @param F
     * @return the root tag for F
     */
    public List<Formula<None>> getRootTag(FunctionSymbol F) {
        return this.getTagList(F).y;
    }

    /**
     * Also creates the tags for all arguments if not yet there.
     *
     * @param F
     * @return the list of tags for F
     */
    private Pair<List<List<Formula<None>>>,List<Formula<None>>> getTagList(FunctionSymbol F) {
        Pair<List<List<Formula<None>>>,List<Formula<None>>> fTags = this.tags.get(F);
        if (fTags == null) {
            fTags = this.buildTagList(F);
            this.tags.put(F, fTags);
        }
        return fTags;
    }

    /**
     * Also creates the tags for all arguments if not yet there.
     *
     * @param F
     * @param i must be between 0 and F.getArity() - 1
     * @return the tag for the i-th argument of F;
     *  side effect: will create a list of tags for F if not yet present
     */
    public List<Formula<None>> getArgTagAt(FunctionSymbol F, int i) {
        return this.getArgTagList(F).get(i);
    }


    private Pair<List<List<Formula<None>>>,List<Formula<None>>> buildTagList(FunctionSymbol F) {
        int n = F.getArity() + (this.rootArg ? 1 : 0);
        List<List<Formula<None>>> fTags = new ArrayList<List<Formula<None>>>(n);
        for (int i = 0; i < n; ++i) {
            Pair<FunctionSymbol, Integer> Fi =
                new Pair<FunctionSymbol, Integer>(F, i);
            List<Formula<None>> ithTag;
            if (this.plain || this.maxArgTag <= 0) {
                ithTag = java.util.Collections.singletonList(this.ZERO);
            }
            else {
                ithTag = this.binarizer.bin(Fi, this.maxArgTag).getFormulae();
            }
            fTags.add(ithTag);
        }
        Pair<FunctionSymbol, Integer> Froot = new Pair<FunctionSymbol, Integer>(F, LevelMappingEncoder.ROOT_ARG_POS);
        List<Formula<None>> fRootTag;
        if (this.plainRoot || this.maxRootTag <= 0) {
            fRootTag = java.util.Collections.singletonList(this.ZERO);
        } else {
            fRootTag = this.binarizer.bin(Froot, this.maxRootTag).getFormulae();
        }
        return new Pair<List<List<Formula<None>>>,List<Formula<None>>>(fTags,fRootTag);
    }

    /**
     * @param rules - non-null, all RHSs must have a root symbol
     * @return the sum of arities of the set of root symbols of the
     *  LHSs and RHSs of rules; each symbol enters the sum at most once.
     */
    private int sumRootArities(Set<? extends GeneralizedRule> rules) {
        Set<FunctionSymbol> rootSyms = LevelMappingEncoder.getRootSyms(rules);

        // ... and sum up
        int result = 0;
        for (FunctionSymbol f : rootSyms) {
            result += f.getArity() + (this.rootArg ? 1 : 0);
        }
        return result;
    }

    /**
     * @param rules - non-null, all RHSs must have a root symbol
     * @return the cardinality of the set of root symbols of the
     *  LHSs and RHSs of rules.
     */
    private static int numRootSymbols(Set<? extends GeneralizedRule> rules) {
        Set<FunctionSymbol> rootSyms = LevelMappingEncoder.getRootSyms(rules);
        return rootSyms.size();
    }

    private static Set<FunctionSymbol> getRootSyms(Set<? extends GeneralizedRule> rules) {
        Set<FunctionSymbol> rootSyms = new LinkedHashSet<FunctionSymbol>();

        // accumulate all symbols ...
        for (GeneralizedRule rule : rules) {
            FunctionSymbol f = rule.getLeft().getRootSymbol();
            rootSyms.add(f);
            f = ((HasRootSymbol)rule.getRight()).getRootSymbol();
            rootSyms.add(f);
        }

        return rootSyms;
    }

    public Formula<None> encodeRootTag(FunctionSymbol f, FunctionSymbol g, boolean strict) {
        List<Formula<None>> fRootTag = this.getRootTag(f);
        List<Formula<None>> gRootTag = this.getRootTag(g);
        if (strict) {
            return this.arithmeticFactory.buildGTCircuit(fRootTag, gRootTag);
        } else {
            return this.arithmeticFactory.buildGECircuit(fRootTag, gRootTag).x;
        }
    }

    public boolean getPlainRoot() {
        return this.plainRoot;
    }

}
