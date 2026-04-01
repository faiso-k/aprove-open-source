package aprove.verification.dpframework.Orders.Utility.GPOLO.Heuristics;

import java.util.*;

import aprove.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.Orders.Utility.GPOLO.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * The heuristics from Section 3.2.
 *
 * Allow rational interpretations for all symbols if one of the
 * following propositions holds:
 *
 * (1) Destructor:
 *     There is a destructor rule
 *       f(c(x_1, ..., x_n)) -> x_i
 *     in R where c is a constructor and f occurs in a rhs of P.
 *
 * (2) Permutation:
 *     R or P contains a rule
 *       C_1[ f(..., g(...), ...) ]  ->  C_2[ g(..., f(...), ...) ]
 *     for contexts C_1, C_2
 *     f(..., g(...), ...) or g(..., f(...), ...) contains two nested
 *     occurrences of f or g.
 *     Here, f and g may (but need not) be identical.
 *
 * (3) Non-linearity:
 *     R or P contains a rule
 *       l -> C[ c(..., t_1, ..., t_2, ...) ]
 *     where V(t_1) and V(t_2) are *not* disjoint.
 *
 * @author fuhs
 * @version $Id$
 */
public class PaperRat implements RatHeuristic {

    private static final int MAXOCC = 10; // maximal number of positions per function symbol that are regarded for check

    //private Set<FunctionSymbol> destructorsInPRhs;
    private Set<FunctionSymbol> defSyms;
    private Map<FunctionSymbol, boolean[]> superArg;

    private boolean useRat = false;

    @Override
    public boolean allowRat() {
        return this.useRat;
    }

    @Override
    public boolean allowRat(FunctionSymbol f) {
        return this.useRat;
    }

    @Override
    public boolean allowRatCoeff(FunctionSymbol f, int i) {
        return this.useRat;
    }

    @Override
    public boolean allowRatConst(FunctionSymbol f) {
        return this.useRat;
    }

    @Override
    public void setPR(Set<? extends GeneralizedRule> p, Set<? extends GeneralizedRule> r) {
        this.useRat = false;
        this.superArg = new LinkedHashMap<FunctionSymbol, boolean[]>();

        // ad (1)
        this.initDefSyms(r);
        this.initDestructorsInPRhs(r, p);

        // ad (3)
        if (this.useRat) { return; }
        this.addDuplData(r);
        if (this.useRat) { return; }
        this.addDuplData(p);

        // ad (2)
        if (this.useRat) { return; }
        this.initPermutations(r);
        if (this.useRat) { return; }
        this.initPermutations(p);
    }

    private void initDefSyms(Collection<? extends GeneralizedRule> r) {
        this.defSyms = CollectionUtils.getRootSymbols(r);
    }

    /**
     * Ad (1).
     * Requires that this.defSymbols has been initialized.
     *
     * @param r
     * @param p
     */
    private void initDestructorsInPRhs(Collection<? extends GeneralizedRule> r, Collection<? extends GeneralizedRule> p) {
        // reset possibly invalid computed values
        Set<FunctionSymbol> destructors = new LinkedHashSet<FunctionSymbol>();

        // collect the destructors
        for (GeneralizedRule rule : r) {
            TRSTerm rhs = rule.getRight();
            TRSFunctionApplication lhs = rule.getLeft();
            FunctionSymbol f = lhs.getRootSymbol();
            if (f.getArity() == 1 && rhs.isVariable()) {
                TRSTerm lhsArg = lhs.getArgument(0);
                if (! lhsArg.isVariable()) {
                    TRSFunctionApplication innerApp = (TRSFunctionApplication) lhsArg;
                    FunctionSymbol innerRoot = innerApp.getRootSymbol();
                    if (! this.defSyms.contains(innerRoot)) {
                        boolean allArgsVars = true;
                        boolean rhsIsAnArg = false;
                        for (TRSTerm t : innerApp.getArguments()) {
                            if (t.isVariable()) {
                                if (rhs.equals(t)) {
                                    rhsIsAnArg = true;
                                }
                            }
                            else {
                                allArgsVars = false;
                                break;
                            }
                        }
                        if (allArgsVars && rhsIsAnArg) {
                            destructors.add(f);
                        }
                    }
                }
            }
        }

        // now get symbols of rhs of P
        Set<FunctionSymbol> pRhsSyms = new LinkedHashSet<FunctionSymbol>();
        for (GeneralizedRule pRule : p) {
            TRSTerm rhs = pRule.getRight();
            rhs.collectFunctionSymbols(pRhsSyms);
        }

        // keep the intersection
        destructors.retainAll(pRhsSyms);
        //this.destructorsInPRhs = destructors;
        if (! destructors.isEmpty()) {

            // set global yay/nay attribute
            this.useRat = true;
        }
    }

    /**
     * Ad (2).
     *
     * @param rules
     */
    private void initPermutations(Collection<? extends GeneralizedRule> rules) {
        for (GeneralizedRule rule : rules) {
            TRSTerm left = rule.getLeft();
            TRSTerm right = rule.getRight();
            if (PaperRat.hasPermutation(left, right, PaperRat.MAXOCC)) {
                this.useRat = true;
                break; // if we do not care *where* to use rats
            }
        }
    }



    // ad (2)

    private static boolean hasPermutation(TRSTerm left, TRSTerm right, int maxOcc) {
        Map<FunctionSymbol, List<Position>> leftMap = PaperRat.getF2Pos(left, maxOcc);
        Map<FunctionSymbol, List<Position>> rightMap = PaperRat.getF2Pos(right, maxOcc);
        Set<FunctionSymbol> leftNested = new LinkedHashSet<FunctionSymbol>();
        for (Map.Entry<FunctionSymbol, List<Position>> entry : leftMap.entrySet()) {
            FunctionSymbol f = entry.getKey();
            if (!rightMap.containsKey(f)) {
                continue;
            }
            List<Position> poss = entry.getValue();
leftLoop:   for (int i = 0; i < poss.size(); i++) {
                for (int j = i+1; j < poss.size(); j++) {
                    Position posi = poss.get(i);
                    Position posj = poss.get(j);
                    if (!posi.isIndependent(posj)) {
                        leftNested.add(f);
                        break leftLoop;
                    }
                }
            }
        }
        Set<FunctionSymbol> rightNested = new LinkedHashSet<FunctionSymbol>();
        for (Map.Entry<FunctionSymbol, List<Position>> entry : rightMap.entrySet()) {
            FunctionSymbol f = entry.getKey();
            if (!leftMap.containsKey(f)) {
                continue;
            }
            List<Position> poss = entry.getValue();
rightLoop:  for (int i = 0; i < poss.size(); i++) {
                for (int j = i+1; j < poss.size(); j++) {
                    Position posi = poss.get(i);
                    Position posj = poss.get(j);
                    if (!posi.isIndependent(posj)) {
//                        if (leftNested.contains(f)) {
                        if (!leftNested.isEmpty()) {
                            // both nested => f = g case
                            return true;
                        }
                        rightNested.add(f);
                        break rightLoop;
                    }
                }
            }
        }
        // now we know that leftNested and rightNested are disjoint
        for (FunctionSymbol f : leftNested) {
            for (Position pos : leftMap.get(f)) {
                Set<FunctionSymbol> below = PaperRat.getBelow(left, pos);
                if (!below.contains(f)) {
                    continue;
                }
                // now we know that l=C[f(...,D[f(...)],...)]
                below.retainAll(rightMap.keySet());
                for (FunctionSymbol g : below) {
                    if (g.equals(f)) {
                        continue;
                    }
                    // case l=C[f(...,D[f(...)],...,E[g(...)],...)] and r=F[g(...)]
                    // or   l=C[f(...,D[f(...,E[g(...)],...)],...)] and r=F[g(...)]
                    // or   l=C[f(...,D[g(...,E[f(...)],...)],...)] and r=F[g(...)]
                    // need to check if there is g in r below which f occurs
                    for (Position gpos : rightMap.get(g)) {
                        Set<FunctionSymbol> gbelow = PaperRat.getBelow(right, gpos);
                        if (gbelow.contains(f)) {
                            return true;
                        }
                    }
                }
                Set<FunctionSymbol> above = PaperRat.getAbove(left, pos);
                above.retainAll(rightMap.keySet());
                for (FunctionSymbol g : above) {
                    if (g.equals(f)) {
                        continue;
                    }
                    // case l=E[g(...,C[f(...,D[f(...)],...)],...)] and r=F[g(...)]
                    // need to check if there is g in r above which f occurs
                    for (Position gpos : rightMap.get(g)) {
                        Set<FunctionSymbol> gabove = PaperRat.getAbove(right, gpos);
                        if (gabove.contains(f)) {
                            return true;
                        }
                    }
                }
            }
        }
        for (FunctionSymbol f : rightNested) {
            for (Position pos : rightMap.get(f)) {
                Set<FunctionSymbol> below = PaperRat.getBelow(right, pos);
                if (!below.contains(f)) {
                    continue;
                }
                // now we know that r=C[f(...,D[f(...)],...)]
                below.retainAll(leftMap.keySet());
                for (FunctionSymbol g : below) {
                    if (g.equals(f)) {
                        continue;
                    }
                    // case r=C[f(...,D[f(...)],...,E[g(...)],...)] and l=F[g(...)]
                    // or   r=C[f(...,D[f(...,E[g(...)],...)],...)] and l=F[g(...)]
                    // or   r=C[f(...,D[g(...,E[f(...)],...)],...)] and l=F[g(...)]
                    // need to check if there is g in l below which f occurs
                    for (Position gpos : leftMap.get(g)) {
                        Set<FunctionSymbol> gbelow = PaperRat.getBelow(left, gpos);
                        if (gbelow.contains(f)) {
                            return true;
                        }
                    }
                }
                Set<FunctionSymbol> above = PaperRat.getAbove(right, pos);
                above.retainAll(leftMap.keySet());
                for (FunctionSymbol g : above) {
                    if (g.equals(f)) {
                        continue;
                    }
                    // case r=E[g(...,C[f(...,D[f(...)],...)],...)] and l=F[g(...)]
                    // need to check if there is g in l above which f occurs
                    for (Position gpos : leftMap.get(g)) {
                        Set<FunctionSymbol> gabove = PaperRat.getAbove(left, gpos);
                        if (gabove.contains(f)) {
                            return true;
                        }
                    }
                }
            }
        }
        return false;
    }

    private static Set<FunctionSymbol> getAbove(TRSTerm left, Position pos) {
        // IMPLEMENT CACHE
        Set<FunctionSymbol> above = new LinkedHashSet<FunctionSymbol>();
        while (!pos.isEmptyPosition()) {
            pos = pos.shorten(1);
            above.add(((TRSFunctionApplication) left.getSubterm(pos)).getRootSymbol());
        }
        return above;
    }

    private static Set<FunctionSymbol> getBelow(TRSTerm left, Position pos) {
        // IMPLEMENT CACHE
        Set<FunctionSymbol> below = new LinkedHashSet<FunctionSymbol>();
        TRSFunctionApplication subTerm = (TRSFunctionApplication) left.getSubterm(pos);
        for (TRSTerm arg : subTerm.getArguments()) {
            below.addAll(arg.getFunctionSymbols());
        }
        return below;
    }

    private static Map<FunctionSymbol, List<Position>> getF2Pos(TRSTerm term, int maxOcc) {
        Map<FunctionSymbol, List<Position>> f2pos = new LinkedHashMap<FunctionSymbol,List<Position>>();
        for (Pair<Position,TRSTerm> posterm : term.getPositionsWithSubTerms()) {
            TRSTerm subTerm = posterm.y;
            if (subTerm instanceof TRSFunctionApplication) {
                TRSFunctionApplication fApp = (TRSFunctionApplication) subTerm;
                FunctionSymbol f = fApp.getRootSymbol();
                List<Position> poss = f2pos.get(f);
                if (poss == null) {
                    poss = new ArrayList<Position>();
                    f2pos.put(f, poss);
                }
                if (poss.size() <= maxOcc) {
                    poss.add(posterm.x);
                }
            }
        }
        return f2pos;
    }


    // Ad (3).

    private void addDuplData(Collection<? extends GeneralizedRule> rules) {
        for (GeneralizedRule rule : rules) {
            TRSTerm r = rule.getRight();
            Map<TRSVariable, List<Position>> varPositions = r.getVariablePositions();
            for (List<Position> positions : varPositions.values()) {
                final int size = positions.size();
                for (int i1 = 0; i1 < size; ++i1) {
                    Position p1 = positions.get(i1);
                    for (int i2 = i1 + 1; i2 < size; ++i2) {
                        Position p2 = positions.get(i2);
                        Position forkPos = p1.getLongestCommonPrefix(p2);

                        // the following cast is (hopefully) safe because
                        // two different occurrences of a variable in a term
                        // have a longest common prefix position at which
                        // there is a function symbol
                        TRSFunctionApplication fApp = (TRSFunctionApplication) r.getSubterm(forkPos);
                        FunctionSymbol f = fApp.getRootSymbol();

                        // require constructor symbol of arity 2
                        if (f.getArity() == 2 && ! this.defSyms.contains(f)) {
                            // below which args of f did the fork happen?
                            int arg1 = p1.toIntArray()[forkPos.getDepth()];
                            int arg2 = p2.toIntArray()[forkPos.getDepth()];
                            if (Globals.useAssertions) {
                                assert arg1 != arg2;
                                // otherwise forkPos was not the /longest/
                                // common prefix
                            }
                            this.putDuplArg(f, arg1);
                            this.putDuplArg(f, arg2);
                        }
                    }
                }
            }
        }
    }

    private void putDuplArg(FunctionSymbol f, int i) {
        boolean[] positions = this.superArg.get(f);
        if (positions == null) {
            positions = new boolean[f.getArity()];
            Arrays.fill(positions, false);
        }
        positions[i] = true;
        this.superArg.put(f, positions);

        // set global yay/nay attribute
        this.useRat = true;
    }


}
