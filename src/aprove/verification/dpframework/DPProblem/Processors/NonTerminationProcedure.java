package aprove.verification.dpframework.DPProblem.Processors;

import java.math.*;
import java.util.*;
import java.util.concurrent.atomic.*;
import java.util.logging.*;

import aprove.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.dpframework.DPProblem.Processors.*;
import aprove.verification.dpframework.DPProblem.Processors.NonTerminationProcessor.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * <p>
 * (debug output: DEBUG_SPECIALMAN)
 * </p>
 * <p>
 * Implementation of a processor that tries to prove nontermination. It checks
 * if there exists a dependency pair <s,t> where s sigma can be narrowed by the
 * given rules to t' and s and t' semiunify.
 * </p>
 * <p>
 * Used heuristic:
 * <ul>
 * <li>If P united with R is rightlinear and not leftlinear we first narrow to
 * the right, otherwise we narrow to the left.</li>
 * <li>If P united with R is not leftlinear we moreover permit narrowing in
 * variables.</li>
 * </ul>
 * </p>
 * <p>
 * Parameters:
 * <ul>
 * <li>if you use negative numbers for all three limits there will be no limit</li>
 * <li>TotalLimit: number of applications of one rule in the narrowing sequences
 * of both directions</li>
 * <li>LeftLimit: number of applications of one rule in the narrowing sequence
 * to the left</li>
 * <li>RightLimit: number of applications of one rule in the narrowing sequence
 * to the right</li>
 * </ul>
 * </p>
 *
 * @author Matthias Sondermann, Rene Thiemann
 * @version $Id$
 */
 
 /**
     * Class which encapsulates the procedure to check nontermination with narrowing and semiunification.
     *
     * @author Matthias Sondermann
*/
public class NonTerminationProcedure {
    
    public int procNumber = 1;

    public static enum Heuristic {
        NORMAL, // standard heuristic which uses backward or forward narrowing and sometimes performs narrowing into variables
        ONLY_FORWARD_NARROWING // only do forward narrowing where narrowing into variables is NOT allowed (sufficient for outermost transformation)
    }

    private static final Logger log = Logger.getLogger("aprove.verification.dpframework.DPProblem.Processors.NonTerminationProcessor");
    /**
     * maximal number of narrowings with one rule
     */
    private final int totalLimit;
    /**
     * maximal number of narrowings to the left with one rule (to be more precise with rule^{-1})
     */
    private final int leftLimit;
    /**
     * maximal number of narrowings to the right with one rule
     */
    private final int rightLimit;
    /**
     * heuristic which controls whether to narrow into variables, which direction first, ...
     */
    protected final NonTerminationProcessor.Heuristic heuristic;
    
    /**
     * given qdpProblem
     */
    private final QDPProblem qdpProblem;
    /**
     * map from function symbol to rule to avoid stupid unification checks
     */
    Map<FunctionSymbol,ImmutableSet<Rule>> rRuleMap;
    Map<FunctionSymbol,ImmutableSet<Rule>> rReverseRuleMap;
    /**
     * sets which are used for doing closure steps and remembering already checked pairs
     */
    private List<NarrowPair> rulesFromPtoCheck;
    private Set<Pair<TRSTerm,TRSTerm>> rulesFromPalreadyChecked;
    /**
     * the sets of the original trs-rules, the given dependency pairs and the union of them
     */
    private ImmutableSet<Rule> rRules;
    private ImmutableSet<Rule> pRules;
    private ImmutableSet<Rule> rReversedRules;
    private Set<Rule> allRules;
    /**
     * some flags which influence the heuristic or depend on it
     */
    private boolean narrowInVars;
    private boolean rightLinear;
    private boolean leftLinear;
    /**
     * actual total limit which is updated after narrowing in one direction terminated
     */
    private int actualTotalLimit;
    private final boolean qIsNonEmpty;
    /**
     * if we have a SRS it suffices to narrow with matching instead of semiunification
     */
    private final boolean matchingSuffices;
    /**
     * only for counting the number of semiunifications
     */
    private int semiunifNr = 1;
    /**
     * only for doing doClusureAgain
     */
    private NonTerminationProcessor.Direction closureActDir;
    private int closureActLimit = -1;
    private final List<NarrowPair> closureClosure = new ArrayList<NarrowPair>();
    private final Set<Pair<TRSTerm,TRSTerm>> closureDone = new LinkedHashSet<Pair<TRSTerm,TRSTerm>>();
    private Pair<TRSSubstitution,TRSSubstitution> closureSubst = null;
    private final List<TRSTerm> loopTerms = new ArrayList<>();
    
    @ParamsViaArguments({"ProcNumber", "QDPProblem", "TotalLimit","LeftLimit","RightLimit"})
    public NonTerminationProcedure(final int procNumber, final QDPProblem qdpProblem, final int totalLimit, final int leftLimit, final int rightLimit, final NonTerminationProcessor.Heuristic heuristic){
        this.procNumber = procNumber;
        this.qdpProblem = qdpProblem;
        this.rRuleMap = qdpProblem.getRwithQ().getRuleMap();
        this.rReverseRuleMap = qdpProblem.getRwithQ().getReverseRuleMap();
        this.qIsNonEmpty = !qdpProblem.getQ().isEmpty();
        this.totalLimit = totalLimit;
        this.actualTotalLimit = totalLimit;
        this.leftLimit = leftLimit;
        this.rightLimit = rightLimit;
        this.heuristic = heuristic;
        // check if it suffices to narrow with matching and not with semiunification
        this.matchingSuffices = this.qdpProblem.getMaxArity() == 1 ? true : false;
    }

    /**
     * Tries to find a narrow pair which semiunifies.
     */
    public Result processQDPProblem(final Abortion aborter) throws AbortionException{

        // get rules of R and P
        this.rRules = this.qdpProblem.getR();
        this.pRules = this.qdpProblem.getP();

        // fill rReversedRule set
        Set<Rule> dummy = new LinkedHashSet<Rule>();
        for(final Set<Rule> value : this.rReverseRuleMap.values()) {
            dummy.addAll(value);
        }
        this.rReversedRules = ImmutableCreator.create(dummy);
        dummy = null;

        // fill the set this.allRules
        this.allRules = new LinkedHashSet<Rule>();
        this.allRules.addAll(this.rRules);
        this.allRules.addAll(this.pRules);

        // check left and right linearity
        this.leftLinear = aprove.verification.dpframework.BasicStructures.CollectionUtils.isLeftLinear(this.allRules);
        this.rightLinear = aprove.verification.dpframework.BasicStructures.CollectionUtils.isRightLinear(this.allRules);

        // if a pair semiunifies this will be the matcher and the semiunifier
        Pair<TRSSubstitution,TRSSubstitution> subst;

        // initial closure step with dependency pairs
        this.rulesFromPtoCheck = new ArrayList<NarrowPair>();
        this.rulesFromPalreadyChecked = new LinkedHashSet<Pair<TRSTerm,TRSTerm>>();
        // first add all needed pRules to the dp sets
        for(final Rule dp : this.pRules){
            final NarrowPair newPair = new NarrowPair(dp,this.allRules);
            // check dp only if it wasn't already checked earlier
            // (use standard representation to avoid adding two pairs which are equal under variable renaming
            if(!this.rulesFromPalreadyChecked.contains(newPair.getStandardRepresentation())){
                // is the pair semiunifiable?
                subst = this.testPair(newPair, aborter);
                if(subst!=null){
                    // since a semiunifiable pair is found nontermination is proved 
                    //only return the loopTerm, if it hasn't been already returned
                    
                   if(!this.loopTerms.contains(newPair.getKey())) {
                       this.loopTerms.add(newPair.getKey());
                       return ResultFactory.disproved(NonTerminationLoopProof.create(
                                                                                     this.qdpProblem, newPair, subst, NonTerminationProcessor.Direction.NONE,
                                                                                     this.qdpProblem));
                   }
                }
                // add newPair to narrow it later
                this.rulesFromPtoCheck.add(newPair);
                // never add this pair again (and no pair which is equal to this one under variable renaming)
                this.rulesFromPalreadyChecked.add(newPair.getStandardRepresentation());
            }
        }

        // create heuristic order of narrowing directions
        Pair<NonTerminationProcessor.Direction,NonTerminationProcessor.Direction> directionOrder;
        switch (this.heuristic) {
        case ONLY_FORWARD_NARROWING:
            NonTerminationProcessor.log.log(Level.FINE, "Using only_forw_narrowing heuristic in nonterm");
            directionOrder = new Pair<NonTerminationProcessor.Direction,NonTerminationProcessor.Direction>(NonTerminationProcessor.Direction.RIGHT, NonTerminationProcessor.Direction.NONE);
            this.narrowInVars = false;
            break;
        case NORMAL:
            // if P united with R is left-linear: first narrow backwards
            NonTerminationProcessor.log.log(Level.FINE, "Using normal heuristic in nonterm");
            if(this.leftLinear){
                directionOrder = new Pair<NonTerminationProcessor.Direction,NonTerminationProcessor.Direction>(NonTerminationProcessor.Direction.LEFT, NonTerminationProcessor.Direction.RIGHT);
            }
            // if P united with R is right-linear: first narrow forwards
            else if(this.rightLinear){
                directionOrder = new Pair<NonTerminationProcessor.Direction,NonTerminationProcessor.Direction>(NonTerminationProcessor.Direction.RIGHT, NonTerminationProcessor.Direction.LEFT);
            }
            // if P united with R is not left-linear and not right-linear: first narrow backwards and narrow into variables
            else{
                directionOrder = new Pair<NonTerminationProcessor.Direction,NonTerminationProcessor.Direction>(NonTerminationProcessor.Direction.LEFT,NonTerminationProcessor.Direction.RIGHT);
                this.narrowInVars = true;
                // because narrowing in variables is a lot of work
                this.actualTotalLimit = 1;
                if(NonTerminationProcessor.log.isLoggable(Level.INFO)){
                    NonTerminationProcessor.log.log(Level.INFO, "NontermProcedure " + this.procNumber + ": Because P united with R is not leftlinear we narrow at variable positions too.\n Total application limit is set to 1.\n");
                }
            }
            break;
          default:
              throw new RuntimeException("Unknown heuristic specified in non-termination procedure");
        }

        // do closure steps in both directions, first into directionOrder.x and after that into directionOrder.y
        final Pair<NonTerminationProcessor.Direction,Pair<NarrowPair,Pair<TRSSubstitution,TRSSubstitution>>> returnPair = this.doHeuristic(directionOrder,aborter);
        // if a pair was found that semiunifies nontermination is proved
        if(returnPair.y!=null){
            return ResultFactory.disproved(NonTerminationLoopProof.create(
                    this.qdpProblem, returnPair.y.x, returnPair.y.y,
                    returnPair.x, this.qdpProblem));
        }
        // no narrowing could show nontermination
        return ResultFactory.unsuccessful("Application limit was reached and no semiunifying pair was found.");
    }

    /**
     * First do closure procedure into direction <code>dirs.x</code> and then into direction <code>dirs.y</code> if needed.
     */
    private Pair<NonTerminationProcessor.Direction,Pair<NarrowPair,Pair<TRSSubstitution,TRSSubstitution>>> doHeuristic(final Pair<NonTerminationProcessor.Direction,NonTerminationProcessor.Direction> dirs, final Abortion aborter) throws AbortionException{
        Pair<NarrowPair,Pair<TRSSubstitution,TRSSubstitution>> dummyPair = null;

        // narrow to the first direction
        if(NonTerminationProcessor.log.isLoggable(Level.INFO)) {
            NonTerminationProcessor.log.log(Level.INFO, "NontermProcedure " + this.procNumber + ": Try all possible narrowings to the " + dirs.x.toString().toLowerCase() + ".\n");
            NonTerminationProcessor.log.log(Level.INFO, "NontermProcedure " + this.procNumber + ": limits are left = "+ this.leftLimit + ", right = " + this.rightLimit + ", total = " + this.actualTotalLimit+"\n");
        }
        dummyPair = this.doClosure(dirs.x, aborter);
        if(dummyPair!=null){
            if(NonTerminationProcessor.log.isLoggable(Level.INFO) && dirs.y != NonTerminationProcessor.Direction.NONE) {
                NonTerminationProcessor.log.log(Level.INFO, "NontermProcedure " + this.procNumber + ": A semiunifying pair was found so narrowing to the " + dirs.y.toString().toLowerCase() + " is superfluous.\n");
            }
            return new Pair<NonTerminationProcessor.Direction,Pair<NarrowPair,Pair<TRSSubstitution,TRSSubstitution>>>(dirs.x, dummyPair);
        }
        // since the narrowing to the first direction took place the total limit has to be updated
        if(dirs.x==NonTerminationProcessor.Direction.LEFT){
            this.actualTotalLimit -= this.leftLimit;
        } else {
            this.actualTotalLimit -= this.rightLimit;
        }
        if(this.actualTotalLimit <= 0 || dirs.y == NonTerminationProcessor.Direction.NONE){
            // nothing more to do and dummyPair is null
            if(dirs.y != NonTerminationProcessor.Direction.NONE && NonTerminationProcessor.log.isLoggable(Level.INFO)) {
                NonTerminationProcessor.log.log(Level.INFO, "NontermProcedure " + this.procNumber + ": Since the total application limit is reached we do not start narrowing to the " + dirs.y.toString().toLowerCase() + ".\n");
            }
            return new Pair<NonTerminationProcessor.Direction,Pair<NarrowPair,Pair<TRSSubstitution,TRSSubstitution>>>(dirs.y, dummyPair);
        }
        // if narrowing to the first direction failed now narrow to the second direction
        if(NonTerminationProcessor.log.isLoggable(Level.INFO)) {
            NonTerminationProcessor.log.log(Level.INFO,"NontermProcedure " + this.procNumber +  ". Try all possible narrowings to the " + dirs.y.toString().toLowerCase() + "\n");
        }
        dummyPair = this.doClosure(dirs.y, aborter);
        return new Pair<NonTerminationProcessor.Direction,Pair<NarrowPair,Pair<TRSSubstitution,TRSSubstitution>>>(dirs.y, dummyPair);
    }

    /**
     * Do narrowings in direction <code>actDir</code> until a pair which semiunifies is found or the limit is reached.
     */
    private Pair<NarrowPair,Pair<TRSSubstitution,TRSSubstitution>> doClosure(final NonTerminationProcessor.Direction actDir, final Abortion aborter) throws AbortionException{
        this.closureActDir = actDir;
        // set the actual limit depending on the direction
        if(this.closureActDir==NonTerminationProcessor.Direction.RIGHT){
            this.closureActLimit = this.rightLimit;
        }
        else{
            this.closureActLimit = this.leftLimit;
        }

        // some needed stuff
        this.closureClosure.addAll(this.rulesFromPtoCheck);
        this.closureDone.addAll(this.rulesFromPalreadyChecked);
        this.closureSubst = null;

        // do more closure steps as long as new narrow-pairs result out of narrowing.
        // take every element which was added to and never removed from closure list
        while(!this.closureClosure.isEmpty()){
            aborter.checkAbortion();
            // get a custom narrow pair (take wlog the first one)
            final NarrowPair actPair = this.closureClosure.get(0);
            final List<NarrowPair> newNarrowedPairs = new ArrayList<NarrowPair>();
            // try to narrow pair with every rule and get all new narrow pairs
            final Set<NarrowPair> actNarrowedPairs = this.doOneNarrowingStep(actPair, this.closureActDir, this.closureActLimit, aborter);
            // add all new narrow pairs which have not been computed yet
            for(final NarrowPair actNewPair : actNarrowedPairs){
                // check this pair only if it or a pair that is equal to this except by variable renaming was never checked before
                if(!this.closureDone.contains(actNewPair.getStandardRepresentation())){
                    // is the new pair semiunifiable?
                    this.closureSubst = this.testPair(actNewPair, aborter);
                    if(this.closureSubst!=null){
                        loopTerms.add(actNewPair.getKey());
                        // nontermination proved so nothing more is to do
                        return new Pair<NarrowPair,Pair<TRSSubstitution,TRSSubstitution>>(actNewPair,this.closureSubst);
                    }
                    // this pair has to be narrowed later
                    newNarrowedPairs.add(actNewPair);
                    // never add this pair again
                    this.closureDone.add(actNewPair.getStandardRepresentation());
                }
            }
            // add all new narrow pairs to the closure list
            this.closureClosure.addAll(newNarrowedPairs);
            // actPair will never be touched again
            this.closureClosure.remove(actPair);
        }
        // closure list is empty and no semiunification succeded
        // so nontermination could not be proved with this applLimit
        return null;
    }
    
    /**
     * Indicates whether the closure process has been reached.
     *
     * @return {@code true} if the closure limit was set, {@code false} otherwise
     */
    
    public boolean reachedClosure() {
        return this.closureActLimit != -1;
    }
    
    /**
     * Re-executes the closure computation to attempt finding the next loop.
     * If a new loop is found, returns a {@code Result} containing the corresponding proof.
     * May throw an {@code AbortionException} if the operation is aborted externally.
     *
     * @param aborter the abortion mechanism to allow interruption of the computation
     * @return the result containing the new loop proof, if found
     * @throws AbortionException if the computation is aborted
     */

    public Result doClosureAgain(final Abortion aborter) throws AbortionException{
        
        while(!this.closureClosure.isEmpty()){
            aborter.checkAbortion();
            // get a custom narrow pair (take wlog the first one)
            final NarrowPair actPair = this.closureClosure.get(0);
            final List<NarrowPair> newNarrowedPairs = new ArrayList<NarrowPair>();
            // try to narrow pair with every rule and get all new narrow pairs
            final Set<NarrowPair> actNarrowedPairs = this.doOneNarrowingStep(actPair, this.closureActDir, this.closureActLimit, aborter);
            // add all new narrow pairs which have not been computed yet
            for(final NarrowPair actNewPair : actNarrowedPairs){
                // check this pair only if it or a pair that is equal to this except by variable renaming was never checked before
                if(!this.closureDone.contains(actNewPair.getStandardRepresentation())){
                    // is the new pair semiunifiable?
                    this.closureSubst = this.testPair(actNewPair, aborter);
                    if(this.closureSubst!=null){
                        // nontermination proved so nothing more is to do
                        if(!loopTerms.contains(actNewPair.getKey())) {
                            List<Triple<Rule,Position,Trs>> narrowList = actNewPair.getNarrowList();
                            boolean newLoop = true;
                            for (Triple<Rule, Position, Trs> nl : narrowList) {
                                TRSTerm loopTerm = nl.getX().getLeft();
                                if(loopTerms.contains(loopTerm)) {
                                    newLoop = false;
                                }
                            }
                            if(newLoop) {
                                loopTerms.add(actNewPair.getKey());
                                Pair<NarrowPair, Pair<TRSSubstitution, TRSSubstitution>> returnPair = new Pair<NarrowPair,Pair<TRSSubstitution,TRSSubstitution>>(actNewPair,this.closureSubst);
                                return ResultFactory.disproved(NonTerminationLoopProof.create(
                                                                                              this.qdpProblem, returnPair.x, returnPair.y,
                                                                                              this.closureActDir, this.qdpProblem));
                            }
                        }
                    }
                    // this pair has to be narrowed later
                    newNarrowedPairs.add(actNewPair);
                    // never add this pair again
                    this.closureDone.add(actNewPair.getStandardRepresentation());
                }
            }
            // add all new narrow pairs to the closure list
            this.closureClosure.addAll(newNarrowedPairs);
            // actPair will never be touched again
            this.closureClosure.remove(actPair);
        }
        // closure list is empty and no semiunification succeded
        // so nontermination could not be proved with this applLimit
        return null;
    }

    /**
     * Generates every possible narrowing out of the given pair with direction <code>actDir</code>
     * @param narrowingPair original pair which is to narrow
     * @return every possible narrowing of <code>narrowingPair</code>
     */
    private Set<NarrowPair> doOneNarrowingStep(final NarrowPair actPair, final NonTerminationProcessor.Direction actDir, final int dirLimit, final Abortion aborter) throws AbortionException {

        final Set<NarrowPair> newNarrowedPairs = new LinkedHashSet<NarrowPair>();
        final TRSTerm left = actPair.x;
        final TRSTerm right = actPair.y;

        // first get the correct terms depending on the direction
        TRSTerm toBeNarrowed = null;
        TRSTerm notToBeNarrowed = null;
        Set<TRSVariable> termVars = null;
        if(actDir==NonTerminationProcessor.Direction.LEFT){
            toBeNarrowed = left;
            notToBeNarrowed = right;
            termVars = left.getVariables();
        }
        else{
            toBeNarrowed = right;
            notToBeNarrowed = left;
            termVars = right.getVariables();
        }

        // if the actual term is a variable and we do not narrow into variables nothing is to do
        if(toBeNarrowed.isVariable() && !this.narrowInVars){
            return newNarrowedPairs;
        }

        // try to narrow with every rule from P at position epsilon
        for(Rule actPrule : this.pRules){
            // if this rule was used to often continue with next rule
            if(this.actualTotalLimit >= 0 &&
               this.actualTotalLimit <= actPair.getNrOfAppls(actPrule)){
               continue;
            }
            if(dirLimit >= 0 &&
               dirLimit <= actPair.getNrOfAppls(actPrule)){
               continue;
            }

            // variables of rule and subterm have to be disjoint
            actPrule = actPrule.renameVariables(termVars);

            TRSTerm l = null;
            TRSTerm r = null;
            if(actDir==NonTerminationProcessor.Direction.LEFT){
                l = actPrule.getRight();
                r = actPrule.getLeft();
            }
            else{
                l = actPrule.getLeft();
                r = actPrule.getRight();
            }
            // try to unify toBeNarrowed and actual dp
            final TRSSubstitution actMgu = l.getMGU(toBeNarrowed);
            if(actMgu!=null){
                // possible narrowing found so do it!
                // do we have to forbid that because of Q?

                // check if the lhs of the P-term is Q-normal
                if(this.qdpProblem.getQ().canBeRewritten(toBeNarrowed)){
                    if(NonTerminationProcessor.log.isLoggable(Level.FINE)){
                        NonTerminationProcessor.log.log(Level.FINE, "NontermProcedure " + this.procNumber + ": A narrowing could not be done because the redex was not Q-normal\n");
                    }
                    continue;
                }
                final TRSTerm newToBeNarrowed = r.applySubstitution(actMgu);
                final TRSTerm newNotToBeNarrowed = notToBeNarrowed.applySubstitution(actMgu);

                // create new narrowing pair depending on the direction and add it to the return set
                if(actDir==NonTerminationProcessor.Direction.LEFT){
                    final NarrowPair newNarrowingPair = new NarrowPair(newToBeNarrowed,newNotToBeNarrowed,actPair,new Triple<Rule,Position,NonTerminationProcessor.Trs>(actPrule, Position.create(), NonTerminationProcessor.Trs.P), actDir);
                    newNarrowedPairs.add(newNarrowingPair);
                }
                else{
                    final NarrowPair newNarrowingPair = new NarrowPair(newNotToBeNarrowed,newToBeNarrowed,actPair,new Triple<Rule,Position,NonTerminationProcessor.Trs>(actPrule, Position.create(), NonTerminationProcessor.Trs.P), actDir);
                    newNarrowedPairs.add(newNarrowingPair);
                }
            }
        }

        // now try to narrow with every trs rule at every (non variable) position
        // iterate over all subterms of termToNarrow
        final Collection<Pair<Position,TRSTerm>> posWithSubterm = toBeNarrowed.getPositionsWithSubTerms();
        for(final Pair<Position,TRSTerm> actPosTermPair : posWithSubterm){

            // check every trs rule at every (non variable) position
            final Position actPos = actPosTermPair.x;
            final TRSTerm actSubterm = actPosTermPair.y;

            Set<Rule> neededRules =  new LinkedHashSet<Rule>();

            // check if we want to narrow in variables
            if(actSubterm.isVariable()) {
                if(this.narrowInVars) {
                    // every rule is a candidate
                    if(actDir == NonTerminationProcessor.Direction.RIGHT) {
                        neededRules = this.rRules;

                    }
                    else {
                        neededRules = this.rReversedRules;
                    }
                }
                else {
                    // nothing to do
                    continue;
                }
            }
            else {
                // actSubterm is a function application
                // now check every rule for narrowing with a useful root symbol
                if(actDir==NonTerminationProcessor.Direction.RIGHT) {
                    final FunctionSymbol fs = ((TRSFunctionApplication) actSubterm).getRootSymbol();
                    final ImmutableSet<Rule> actRRules = this.rRuleMap.get(fs);
                    if(actRRules != null) {
                        neededRules.addAll(actRRules);
                    }
                }
                else{
                    final FunctionSymbol fs = ((TRSFunctionApplication) actSubterm).getRootSymbol();
                    final ImmutableSet<Rule> actRRevRules = this.rReverseRuleMap.get(fs);
                    if(actRRevRules != null) {
                        neededRules.addAll(actRRevRules);
                    }
                    final Collection<Rule> rulesWithVarRhs = this.qdpProblem.getRwithQ().getCollapsingRules();
                    neededRules.addAll(rulesWithVarRhs);
                }
            }

            for(Rule actRule : neededRules){
                aborter.checkAbortion();
                // if this rule was used to often continue with next rule
                if(this.actualTotalLimit >= 0 &&
                   this.actualTotalLimit <= actPair.getNrOfAppls(actRule)){
                   continue;
                }
                if(dirLimit >= 0 &&
                   dirLimit <= actPair.getNrOfAppls(actRule)){
                   continue;
                }

                //  variables of rule and subterm have to be disjoint
                actRule = actRule.renameVariables(termVars);

                // now get the right terms depending on the direction
                // l standes for the term which is used for unification, r for the other one
                // so don't be confused with the names l and r
                TRSTerm l = null;
                TRSTerm r = null;
                if(actDir==NonTerminationProcessor.Direction.LEFT){
                    l = actRule.getRight();
                    r = actRule.getLeft();
                }
                else{
                    l = actRule.getLeft();
                    r = actRule.getRight();
                }

                // try to unify toBeNarrowed.subTerm and actual rule
                final TRSSubstitution actMgu = l.getMGU(actSubterm);
                if(actMgu!=null){
                    // possible narrowing found so do it!
                    // do we have to forbid that because of Q?

                    // check if every non variable subterm is Q-normal
                    if(this.qdpProblem.getQ().canBeRewrittenBelowRoot(actSubterm)) {
                        if(NonTerminationProcessor.log.isLoggable(Level.FINE)){
                            NonTerminationProcessor.log.log(Level.FINE, "NontermProcedure " + this.procNumber + ": A narrowing could not be done because the non variable subterms of the redex were not Q-normal\n");
                        }
                        continue;
                    }
                    final TRSTerm newToBeNarrowed = toBeNarrowed.replaceAt(actPos,r).applySubstitution(actMgu);
                    final TRSTerm newNotToBeNarrowed = notToBeNarrowed.applySubstitution(actMgu);

                    // create new narrowing pair depending on the direction and add it to the return set
                    if(actDir==NonTerminationProcessor.Direction.LEFT){
                        final NarrowPair newNarrowingPair = new NarrowPair(newToBeNarrowed, newNotToBeNarrowed, actPair, new Triple<Rule,Position,NonTerminationProcessor.Trs>(actRule, actPos, NonTerminationProcessor.Trs.R), actDir);
                        newNarrowedPairs.add(newNarrowingPair);
                    }
                    else{
                        final NarrowPair newNarrowingPair = new NarrowPair(newNotToBeNarrowed, newToBeNarrowed, actPair, new Triple<Rule,Position,NonTerminationProcessor.Trs>(actRule, actPos, NonTerminationProcessor.Trs.R), actDir);
                        newNarrowedPairs.add(newNarrowingPair);
                    }

                }
            }
        }
        return newNarrowedPairs;
    }

    /**
     * Tests a narrowing pair if <code>pair.x</code> and <code>pair.y</code> semiunify.
     * @return true iff the pair semiunifies
     */
    private Pair<TRSSubstitution,TRSSubstitution> testPair(final NarrowPair pair, final Abortion aborter) throws AbortionException {
        Pair<TRSSubstitution,TRSSubstitution> subst = null;

        if(Globals.DEBUG_SPECIALMAN) {
            this.semiunifNr++;
            NonTerminationProcessor.log.log(Level.FINE, "NontermProcedure " + this.procNumber + ": Semiunification " + this.semiunifNr + ": " + pair.x + " and " + pair.y + "\n");
        }
        if(this.matchingSuffices) {
            // in case of a SRS it suffices to check if terms match
            final TRSSubstitution matcher = pair.x.getMatcher(pair.y);
            if(matcher != null) {
                subst = new Pair<TRSSubstitution,TRSSubstitution>(pair.x.getMatcher(pair.y), TRSSubstitution.EMPTY_SUBSTITUTION);
            }
        }
        else {
            subst = pair.x.getSemiSubstitutions(pair.y);
        }
        // check if these terms semiunify
        if(subst!=null){
            if(NonTerminationProcessor.log.isLoggable(Level.FINE)) {
                NonTerminationProcessor.log.log(Level.FINE, "NontermProcedure " + this.procNumber + ": Successfully semiunified " + pair.x + " and " + pair.y + ".\n");
            }
            if(this.qIsNonEmpty) {
                if(Globals.DEBUG_SPECIALMAN) {
                    NonTerminationProcessor.log.log(Level.FINE, "NontermProcedure " + this.procNumber + ": Q has to be checked.\n");
                }
                final NarrowPair checkPair = pair.copy();
                // if we have to check the innermost case we have to check wether all narrowings were innermost steps
                if(!this.testQcondition(checkPair,subst)) {
                   if(NonTerminationProcessor.log.isLoggable(Level.FINE)) {
                       NonTerminationProcessor.log.log(Level.FINE, "NontermProcedure " + this.procNumber + ": But the Q-check failed.\n");
                   }
                   // if not all steps were innermost go on with the closure procedure
                   return null;
                }
                if(NonTerminationProcessor.log.isLoggable(Level.FINE)) {
                    NonTerminationProcessor.log.log(Level.FINE, "NontermProcedure " + this.procNumber +  ": Q-check succeeded.\n");
                }
            } else {
                if(Globals.DEBUG_SPECIALMAN) {
                    NonTerminationProcessor.log.log(Level.FINE, "NontermProcedure " + this.procNumber + ": Q-check trivially satisfied since Q is empty.\n");
                }
            }
            // return matcher and semiUnifier as a pair
            return subst;
        }
        return null;
    }

    /**
     * given a redex problem (t,mu,q), this procedure will add
     * all non-variable subterms of t and {x\mu | x in Vars(t,t mu, t mu^2, ...)}
     * to the redexes set
     * @param t
     * @param mu
     * @param redexes
     */
    private void addToRedexSub(final TRSTerm t, final TRSSubstitution mu, final Set<TRSTerm> redexes) {
        final Set<TRSVariable> vars = t.getVariables();
        TRSTerm tmui = t;
        do {
            tmui = tmui.applySubstitution(mu);
        } while (vars.addAll(tmui.getVariables()));
        // okay, now we know that we will not see new variables any more
        redexes.addAll(t.getNonVariableSubTerms());
        for (final TRSVariable x : vars) {
            redexes.addAll(x.applySubstitution(mu).getNonVariableSubTerms());
        }
    }

    /**
     * Checks wether all rewritings of <code>pair</code> are Q-restricted steps.
     * Let mu be the matcher from the semiunification.
     *
     * @return true iff all steps are innermost steps w.r.t. Q
     */
    private boolean testQcondition(final NarrowPair pair, final Pair<TRSSubstitution,TRSSubstitution> substPair){
        if(NonTerminationProcessor.log.isLoggable(Level.FINE)) {
            NonTerminationProcessor.log.log(Level.FINE , "NontermProcedure " + this.procNumber + ": Start Q-check with " + pair + " and " + substPair + "\n");
        }
        final TRSSubstitution matcher = substPair.x;
        final TRSSubstitution semiunifier = substPair.y;

        /*
         * first get all redexes of the rewriting sequence
         */
        final List<Pair<TRSFunctionApplication,NonTerminationProcessor.Trs>> redexList = this.getUsedRedexes(pair,semiunifier);

        /*
         * then create the set of lhss of matching problems
         */
        final Set<TRSTerm> forMatching = new LinkedHashSet<TRSTerm>();

        for (final Pair<TRSFunctionApplication,NonTerminationProcessor.Trs> termTrs : redexList) {
            final TRSFunctionApplication redex = termTrs.x;
            if (termTrs.y == NonTerminationProcessor.Trs.P) {
                this.addToRedexSub(redex, matcher, forMatching);
            } else {
                for (final TRSTerm redexSub : redex.getArguments()) {
                    this.addToRedexSub(redexSub, matcher, forMatching);
                }
            }
        }

        /*
         * now identify increasing vars to be able to solve matching problems
         */
        final Set<TRSVariable> increasing = new LinkedHashSet<TRSVariable>();
        final Map<TRSVariable,TRSVariable> nonIncreasing = new LinkedHashMap<TRSVariable,TRSVariable>();
        final Map<TRSVariable, ? extends TRSTerm> mu = matcher.toMap();
        for (final Map.Entry<TRSVariable, ? extends TRSTerm> xt : mu.entrySet()) {
            if (xt.getValue().isVariable()) {
                nonIncreasing.put(xt.getKey(),(TRSVariable)xt.getValue());
            } else {
                increasing.add(xt.getKey());
            }
        }
        boolean change = true;
        while (change) {
            change = false;
            final Iterator<Map.Entry<TRSVariable, TRSVariable>> i = nonIncreasing.entrySet().iterator();
            while (i.hasNext()) {
                final Map.Entry<TRSVariable, TRSVariable> xy = i.next();
                if (increasing.contains(xy.getValue())) {
                    increasing.add(xy.getKey());
                    i.remove();
                    change = true;
                }
            }
        }


        /*
         * then transform matching problems into identity problems.
         * for each matching problem that can possibly be solved we generate one identity problem
         * in the set identProblems
         */
        final Comparator<Pair<TRSTerm,TRSTerm>> matchComparator = new Comparator<Pair<TRSTerm,TRSTerm>>() {
            // second argument first (and variables last)
            // => pairs (t,f(..)) will be in front
            @Override
            public int compare(final Pair<TRSTerm, TRSTerm> one, final Pair<TRSTerm, TRSTerm> two) {
                final int cy = one.y.compareTo(two.y);
                if (cy == 0) {
                    return one.x.compareTo(two.x);
                } else {
                    return -cy;
                }
            }
        };


        Queue<Pair<TRSTerm, TRSTerm>> matchingProblem = new PriorityQueue<Pair<TRSTerm,TRSTerm>>(5, matchComparator);
        final Collection<Collection<Set<TRSTerm>>> identProblems = new LinkedHashSet<Collection<Set<TRSTerm>>>();
        for (final TRSTerm qInit : this.qdpProblem.getQ().getTerms()) {
            sLoop: for (final TRSTerm sInit : forMatching) {
                matchingProblem.clear();
                matchingProblem.offer(new Pair<TRSTerm, TRSTerm>(sInit,qInit));
                while (!matchingProblem.isEmpty()) {
                    Pair<TRSTerm,TRSTerm> sq = matchingProblem.peek();
                    final TRSTerm q = sq.y;
                    if (q.isVariable()) {
                        // we are done, so let us build identity problems
                        final Map<TRSVariable,Set<TRSTerm>> ident = new LinkedHashMap<TRSVariable,Set<TRSTerm>>();
                        for (final Pair<TRSTerm, TRSTerm> tx : matchingProblem) {
                            final TRSVariable x = (TRSVariable) tx.y; // this cast must succeed since if there is some pair
                                                          // with non-variable in second component then it
                                                          // should be returned by peek() instead of sq!
                            final TRSTerm t = tx.x;
                            Set<TRSTerm> tsForX = ident.get(x);
                            if (tsForX == null) {
                                tsForX = new LinkedHashSet<TRSTerm>();
                                ident.put(x, tsForX);
                            }
                            tsForX.add(t);
                        }
                        final Collection<Set<TRSTerm>> tsThatMustBecomeIdentical = new LinkedHashSet<Set<TRSTerm>>();
                        for (final Set<TRSTerm> tsForX : ident.values()) {
                            if (tsForX.size() > 1) {
                                tsThatMustBecomeIdentical.add(tsForX);
                            }
                        }
                        if (tsThatMustBecomeIdentical.isEmpty()) {
                            return false; // matching problem solvable
                        }
                        identProblems.add(tsThatMustBecomeIdentical);
                        continue sLoop;
                    } else {
                        // apply some matching rule
                        final TRSTerm s = sq.x;
                        if (s.isVariable()) {
                            if (increasing.contains(s)) {
                                // apply rule (i) (apply mu on all lhss)
                                final Queue<Pair<TRSTerm, TRSTerm>> newMatchProblem = new PriorityQueue<Pair<TRSTerm,TRSTerm>>(matchingProblem.size(), matchComparator);
                                matchingProblem.poll();
                                do {
                                    sq.x = sq.x.applySubstitution(matcher);
                                    newMatchProblem.offer(sq);
                                    sq = matchingProblem.poll();
                                } while (sq != null);
                                matchingProblem = newMatchProblem;
                            } else {
                                // apply rule (ii)
                                continue sLoop;
                            }
                        } else {
                            final TRSFunctionApplication fs = (TRSFunctionApplication) s;
                            final TRSFunctionApplication gq = (TRSFunctionApplication) q;
                            if (fs.getRootSymbol().equals(gq.getRootSymbol())) {
                                // apply rule (iv) (decompose)
                                matchingProblem.poll();
                                final List<? extends TRSTerm> ss = fs.getArguments();
                                final List<? extends TRSTerm> qs = gq.getArguments();
                                int i = 0;
                                for (final TRSTerm si : ss) {
                                    final TRSTerm qi = qs.get(i);
                                    matchingProblem.offer(new Pair<TRSTerm,TRSTerm>(si, qi));
                                    i++;
                                }
                            } else {
                                // apply rule (iii)
                                continue sLoop;
                            }
                        }
                    }
                }
                // solved form is empty matching problem
                // which is trivially solvable
                return false;
            }
        }

        /*
         * if all matching problems failed, do not compute cycle-free mu
         */
        if (identProblems.isEmpty()) {
            return true;
        }

        /*
         * finally solve identity problems
         * (whenever one identProblem in identProblems is solved then a matching problem is solved,
         *  to solve one identProblem for each set of terms tsForX one has to make all terms t mu^n equal,
         *  and by assumption all these sets tsForX have at least two terms)
         */

        /*
         *  step (i) of solving identity problems:
         *  find n >= 1 such that mu^n is acyclic.
         */

        int j = 2;
        BigInteger n = BigInteger.ONE;
        TRSSubstitution resMu = matcher;
        while (!nonIncreasing.isEmpty()) {
            final Iterator<Map.Entry<TRSVariable, TRSVariable>> i = nonIncreasing.entrySet().iterator();
            while (i.hasNext()) {
                final Map.Entry<TRSVariable, TRSVariable> xv = i.next();
                final TRSVariable w = (TRSVariable) xv.getValue().applySubstitution(matcher);
                if (w.equals(xv.getKey())) {
                    i.remove();
                    final BigInteger m = n.multiply(BigInteger.valueOf(j)).divide(n.gcd(BigInteger.valueOf(j))); /* m = lcm(n, j) */
                    if (!n.equals(m)) {
                        int fact = m.divide(n).intValue(); // new factor
                        final TRSSubstitution resMuHelp = resMu;
                        while (fact != 1) {
                            resMu = resMu.compose(resMuHelp);
                            fact--;
                        }
                        n = m;
                    }
                } else if (mu.containsKey(w)) {
                    xv.setValue(w);
                } else {
                    i.remove();
                }
            }
            j++;
        }

        /*
         * now resMu is acyclic
         */

        idLoop: for (final Collection<Set<TRSTerm>> identProblem : identProblems) {
            // first flatten to binary
            final Set<Pair<TRSTerm,TRSTerm>> idProblems = new LinkedHashSet<Pair<TRSTerm,TRSTerm>>();
            for (final Set<TRSTerm> tsForX : identProblem) {
                for (final TRSTerm t1 : tsForX) {
                    for (final TRSTerm t2: tsForX) {
                        if (t1.compareTo(t2) > 0) { // in this way we won't have duplicate pairs
                            idProblems.add(new Pair<TRSTerm,TRSTerm>(t1,t2));
                        }
                    }
                }
            }

            // if all identityProblems in idProblems can be solved, then we have a redex
            for (final Pair<TRSTerm,TRSTerm> idProblem : idProblems) {
                if (!this.identSolvable(resMu, idProblem.x, idProblem.y, increasing)) {
                    // this identProblem not solvable, so let's try next one
                    continue idLoop;
                }
            }

            // all binary id-problems are solvable, so matching and hence redex problem solvalbe
            return false;
        }

        return true;
    }

    /**
     * decides whether the given identity problem is solvable.
     * @param mu has to be a cycle-free substitution!!! Hence, step (i) of the algorithm has to be done before.
     * @param s
     * @param t
     * @param increasing the set of increasing variables of mu
     */
    private boolean identSolvable(final TRSSubstitution mu, TRSTerm s, TRSTerm t, final Set<TRSVariable> increasing) {
        final Set<TRSVariable> dom = mu.getDomain();


        // internal data structure: List< position p, s|_p, t|_p > such that everything above
        //                          the mentioned positions is identical
        Collection<Triple<Position,TRSTerm,TRSTerm>> workingList = new ArrayList<Triple<Position, TRSTerm, TRSTerm>>();
        final Position p = Position.create();
        if (!this.decompose(p, s, t, increasing, dom, workingList)) {
            return false;
        }

        // step (ii)
        final Map<TRSVariable,Collection<Triple<Position, TRSTerm, TRSTerm>>> S = new LinkedHashMap<TRSVariable, Collection<Triple<Position,TRSTerm,TRSTerm>>>();

        while (!workingList.isEmpty()) {
            final Collection<Triple<Position,TRSTerm,TRSTerm>> newWorkingList = new ArrayList<Triple<Position, TRSTerm, TRSTerm>>();
            for (final Triple<Position,TRSTerm,TRSTerm> pst : workingList) {
                s = pst.y;
                t = pst.z;
                if (increasing.contains(s)) {
                    if (!this.addToS(pst, S)) { // step (vii)
                        return false; // step (viii)
                    }
                }
                if (increasing.contains(t)) {
                    if (!this.addToS(new Triple<Position,TRSTerm,TRSTerm>(pst.x, t, s), S)) { // step (vii)
                        return false; // step (viii)
                    }
                }
                // step (ix)
                s = s.applySubstitution(mu);
                t = t.applySubstitution(mu);
                if (!this.decompose(pst.x, s, t, increasing, dom, newWorkingList)) {
                    return false;
                }
            }

            workingList = newWorkingList; // step (x)
        }

        return true;
    }

    /**
     * adds the triple entry to S and returns false iff there is a conflict due to step (vii)
     * @param entry (the left term has to be an increasing variable, and the entry must be at a deepest position)
     * @param S
     */
    private boolean addToS(final Triple<Position,TRSTerm,TRSTerm> entry, final Map<TRSVariable,Collection<Triple<Position, TRSTerm, TRSTerm>>> S) {
        final TRSVariable x = (TRSVariable) entry.y;
        Collection<Triple<Position, TRSTerm, TRSTerm>> xEntries = S.get(x);
        if (xEntries == null) {
            xEntries = new ArrayList<Triple<Position, TRSTerm, TRSTerm>>();
            xEntries.add(entry);
            S.put(x, xEntries);
        } else {
            final TRSTerm u_2 = entry.z;
            final Position p_2 = entry.x;
            for (final Triple<Position, TRSTerm, TRSTerm> otherXEntry : xEntries) {
                if (Globals.useAssertions) {
                    assert(!otherXEntry.equals(entry)) : "I thought that the set S cannot contain duplicates by construction. "+
                                                          "Either this is a bug in the construction of S or my thought was wrong.";
                }
                final TRSTerm u_1 = otherXEntry.z;
                final Position p_1 = otherXEntry.x;
                if (u_1.equals(u_2)) {
                    if (p_1.isPrefixOf(p_2)) {
                        // note that by assertion p_1 cannot be the same as p_2 at this point
                        // hence the check is a proper prefix check.
                        // Moreover, since the newly created entry is at a lowest position,
                        // we do not have to try to exchange p_1 and p_2
                        return false; // step (viii-b)
                    }
                } else {
                    if (!u_1.unifies(u_2)) {
                        return false; // step (viii-a)
                    }
                }
            }

            // no conflict, so add the new entry
            xEntries.add(entry);
        }
        return true;
    }

    /**
     * adds all (p',s|_p',t|_p') to todo such that
     * p' is below p,
     * p' is a deepest shared position,
     * s and t differ at position p'
     * all triples that are added may be solvable (if mu is defined accordingly)
     * (conflicts with (iv),(v),(vi) are detected)
     * @param p
     * @param s
     * @param t
     * @param increasing
     * @param dom
     * @param todo
     * @return false, if a conflict occurred, true otherwise.
     */
    private boolean decompose(final Position p, final TRSTerm s, final TRSTerm t, final Set<TRSVariable> increasing, final Set<TRSVariable> dom, final Collection<Triple<Position,TRSTerm,TRSTerm>> todo) {
        if (s.isVariable()) {
            if (s.equals(t)) {
                return true; // step (iii)
            } else {
                if (t.isVariable()) {
                    if (!dom.contains(s) && !dom.contains(t)) {
                        return false; // step (vi)
                    } else {
                        todo.add(new Triple<Position, TRSTerm, TRSTerm>(p, s, t));
                        return true;
                    }
                } else {
                    if (increasing.contains(s)) {
                        todo.add(new Triple<Position, TRSTerm, TRSTerm>(p, s, t));
                        return true;
                    } else {
                        return false; // step (v)
                    }
                }
            }
        } else {
            if (t.isVariable()) {
                if (increasing.contains(t)) {
                    todo.add(new Triple<Position, TRSTerm, TRSTerm>(p, s, t));
                    return true;
                } else {
                    return false; // step (v) (one can easily replace "notin Dom(mu)" by "not in increasing" in step (v))
                }
            } else {
                final TRSFunctionApplication fs = (TRSFunctionApplication) s;
                final TRSFunctionApplication gt = (TRSFunctionApplication) t;
                if (fs.getRootSymbol().equals(gt.getRootSymbol())) {
                    int i = 0; // step (iii) (on top level + decomposition)
                    final List<? extends TRSTerm> ts = gt.getArguments();
                    for (final TRSTerm si : fs.getArguments()) {
                        final TRSTerm ti = ts.get(i);
                        final Position pi = p.append(i);
                        if (!this.decompose(pi, si, ti, increasing, dom, todo)) {
                            return false;
                        }
                        i++;
                    }
                    return true;
                } else {
                    return false; // step (vi)
                }
            }
        }
    }

    /**
     * Returns the list of all redexes of the rewriting sequence from pair.x to pair.y.
     */
    private List<Pair<TRSFunctionApplication,NonTerminationProcessor.Trs>> getUsedRedexes(final NarrowPair pair, final TRSSubstitution semiunifier){
        final List<Pair<TRSFunctionApplication,NonTerminationProcessor.Trs>> redexList = new LinkedList<Pair<TRSFunctionApplication,NonTerminationProcessor.Trs>>();
        List<Triple<Rule,Position,NonTerminationProcessor.Trs>> narrowList = pair.getNarrowList();

        // if the dp directly semiunifies only the lhs of the dp is to check
        if(narrowList.isEmpty()){
            redexList.add(new Pair<TRSFunctionApplication,NonTerminationProcessor.Trs>(((TRSFunctionApplication)pair.x).applySubstitution(semiunifier), NonTerminationProcessor.Trs.P));
            return redexList;
        }

        final NonTerminationProcessor.Direction dir = pair.narrowDir;
        TRSTerm actTerm = pair.x.applySubstitution(semiunifier);
        // check narrowing direction to know how to narrow
        // forward narrowing: start with rhs of the initial dp and narrow up to pair.y
        if(dir==NonTerminationProcessor.Direction.RIGHT){
            narrowList.add(0, new Triple<Rule,Position,NonTerminationProcessor.Trs>(pair.dp, Position.create(),NonTerminationProcessor.Trs.P));
        }
        // backward narrowing: start with pair.x and narrow up to the lhs of the initial dp
        else if(dir==NonTerminationProcessor.Direction.LEFT){
            // reverse the list to get the forward narrowing steps
            final List<Triple<Rule,Position,NonTerminationProcessor.Trs>> dummyList = new ArrayList<Triple<Rule,Position,NonTerminationProcessor.Trs>>();
            for(final Triple<Rule,Position,NonTerminationProcessor.Trs> rPtriple : narrowList){
                dummyList.add(0, rPtriple);
            }
            narrowList = dummyList;
            narrowList.add(new Triple<Rule,Position,NonTerminationProcessor.Trs>(pair.dp, Position.create(),NonTerminationProcessor.Trs.P));
        }
        // both cases (forward and backward narrowing) are equal now
        TRSSubstitution actMatcher;
        Position actPos;
        Rule actRule;
        TRSTerm actL;
        TRSTerm actR;
        TRSTerm newTerm;
        TRSFunctionApplication actSubterm;
        // check the whole narrowing list
        for(final Triple<Rule,Position,NonTerminationProcessor.Trs> actPair : narrowList){
            actRule = actPair.x;
            actPos = actPair.y;
            // get subterm where the unification succeeded and check if this is an innermost step
            actSubterm = (TRSFunctionApplication) actTerm.getSubterm(actPos);
            redexList.add(new Pair<TRSFunctionApplication,NonTerminationProcessor.Trs>(actSubterm,actPair.z));
            // do the narrowing
            final Set<TRSVariable> vars = actTerm.getVariables();
            actRule = actRule.renameVariables(vars);
            actL = actRule.getLeft();
            actR = actRule.getRight();
            actMatcher = actL.getMatcher(actSubterm);
            newTerm = actTerm.replaceAt(actPos,actR.applySubstitution(actMatcher));
            actTerm = newTerm;
        }
        return redexList;
    }

}


