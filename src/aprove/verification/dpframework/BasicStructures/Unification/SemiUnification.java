package aprove.verification.dpframework.BasicStructures.Unification;

import java.util.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
/**
 * Class which contains the dag-based semiunification algorithm.
 * We only consider uniform semiunification which means that two terms
 * term1 and term2 are given and the question is if there
 * exist two substitutions sigma and tau such that
 *
 * term1 sigma tau = term2 sigma
 *
 * The substitution sigma is called semiunifier and tau matcher.
 * Semiunification is a superset of unification and matching since unification
 * can be simulated by semiunification by fixing the matcher to the empty substitution
 * and matching by fixing the semiunifier to the empty substitution.
 *
 * The algorithm which is used here is based on dags (directed acyclic digraphs) and
 * is the fastest known algorithm for semiunification with a worst case of
 * O(n?? f(n)??) where f is the functional inverse of Ackermann's function.
 * For more details have a look at "Fast Algorithms for Uniform Semi-Unification"
 * by Alberto Oliart and Wayne Snyder.
 *
 * There are still some System.out.printlns in the code which are commented out.
 * The idea of this is that these comments print the same stuff as the original
 * "Mexican" algorithm. So it should be a good idea to abandon this in order to use
 * it as debug information if a bug is found.
 * Furthermore this class contains the original version of the solution extraction
 * which is presented in the mentioned paper. Unfortunately this procedure is buggy so that
 * our own solution extraction is used (-> SemiUnificationSolutionExtraction).
 *
 * @author Matthias Sondermann
 * @version $Id$
 */
public class SemiUnification implements Exportable {

    /**
     * Do these terms semiunify?
     */
    private TRSTerm term1;
    private TRSTerm term2;
    /**
     * Dag which represents the two terms
     */
    private SemiUnificationDag dag;
    /**
     * Helpers for the semiunification algorithm
     */
    private List<SemiUnificationNode> selfLoops;
    private List<TRSVariable> variableOrder;

    // Helpers for solution extraction
    /**
     * New function symbol "phi" which represents the matcher in the semiunification
     */
    private FunctionSymbol phi;
    /**
     * Necessary for generating the semiunifier and the matcher
     */
    private FreshNameGenerator nameGen;

    /**
     * Creates a new semiunification problem of the two given terms
     */
    public SemiUnification(TRSTerm term1, TRSTerm term2) {
        // be sure that both terms are not null
        if(Globals.useAssertions){
            assert(term1 != null && term2 != null);
        }

        this.term1 = term1;
        this.term2 = term2;
        this.dag = new SemiUnificationDag(term1,term2);

        // create variable order which is used in the algorithm
        // the order of the variables is the order in which they appear in term1 and term2
        this.variableOrder = new ArrayList<TRSVariable>();
        for(TRSVariable x : this.term1.getVariables()) {
            if(!this.variableOrder.contains(x)) {
                this.variableOrder.add(x);
            }
        }
        for(TRSVariable x : this.term2.getVariables()) {
            if(!this.variableOrder.contains(x)) {
                this.variableOrder.add(x);
            }
        }
        // set the order in every node
        int counter=1;
        for(TRSVariable var : this.variableOrder) {
            this.dag.termAtNode.get(var).setOrder(counter);
            counter++;
        }
    }

    /**
     * Start of the semiunification algorithm which decides whether the two given
     * terms semiunify or not. This methode returns true if the decision procedure
     * does not fail with a symbol clash and if no bad cycle is found.
     *
     * @return true iff the two given terms semiunify
     */
    public boolean semiUnify(){
        // trivial case
        if(this.term1.equals(this.term2)) {
            return true;
        }

        // get the two roots of the term pair dag
        SemiUnificationNode s = this.dag.termAtNode.get(this.term1);
        SemiUnificationNode t = this.dag.termAtNode.get(this.term2);
        // start with (leftTerm, 1, rightTerm, 0) because phi(leftTerm) has to be equal to rightTerm
        // after applying the semiunifier
        return this.semiUnify(s,1,t,0) && this.cycleCheck(s,t);
    }

    /**
     * Start of the semiunification algorithm which decides whether the two given
     * terms semiunify or not. If they do so, a solution containing the matcher and the
     * semiunifier is extracted.
     *
     * @return <code>pair.x</code>=matcher and <code>pair.y</code>=semiunifier iff the two
     *         terms semiunify, otherwise <code>null</code>
     */
    public Pair<TRSSubstitution,TRSSubstitution> getSubstitutions(){
        // trivial case
        if(this.term1.equals(this.term2)) {
            return new Pair<TRSSubstitution,TRSSubstitution>(TRSSubstitution.EMPTY_SUBSTITUTION, TRSSubstitution.EMPTY_SUBSTITUTION);
        }

        // start extraction only if the terms semiunify
        if(this.semiUnify()){
            // generate sets of variable and function symbol names used for creating phi and fresh variable names
            Set<String> varNames = new LinkedHashSet<String>();
            for(TRSVariable actVar : this.term1.getVariables()){
                varNames.add(actVar.getName());
            }
            for(TRSVariable actVar : this.term2.getVariables()){
                varNames.add(actVar.getName());
            }
            Set<String> funcNames = new LinkedHashSet<String>();
            for(FunctionSymbol actFunc : this.term1.getFunctionSymbols()){
                funcNames.add(actFunc.getName());
            }
            for(FunctionSymbol actFunc : this.term2.getFunctionSymbols()){
                funcNames.add(actFunc.getName());
            }
            Set<String> forbiddenNames = new LinkedHashSet<String>(varNames);
            forbiddenNames.addAll(funcNames);

            // now the phi function symbol is needed to construct the substitutions
            this.phi = PhiTermFunctions.createPhiFunctionSymbol(forbiddenNames);
            // initialise the name generator which is used for generating fresh variable names
            this.nameGen = new FreshNameGenerator(varNames, FreshNameGenerator.VARIABLES);

            // this.simplify() would start the original implementation of the solution extraction. But because of
            // some bugs which lead to nontermination out own algorithm is used.
            // now simplify the links which are given from this.semiUnify()
            // this.simplify();

            // our own implementation
            SemiUnificationSolutionExtraction solex = new SemiUnificationSolutionExtraction(new Pair<TRSTerm,TRSTerm>(this.term1,this.term2),this.getAlgoConstraints(),this.phi,this.nameGen);
            return solex.getSubstitutions();

        }
        // return null if the two terms do not semiunify
        return null;
    }

    /**
     * Checks if t1 and t2 are equivalent and pushes down the equivalence obligation
     */
    private boolean semiUnify(SemiUnificationNode t1, int c1, SemiUnificationNode t2, int c2){
        Pair<Integer,Integer> newWeights = new Pair<Integer,Integer>(1,0);
        int w1 = newWeights.x;
        int w2 = newWeights.y;

        // find representatives of t1 and t2
        LinkTriple tt1 = this.find(t1);
        LinkTriple tt2 = this.find(t2);

        // cache some stuff to avoid applying the getters infinitely often
        SemiUnificationNode tt1Target = tt1.getTarget();
        SemiUnificationNode tt2Target = tt2.getTarget();
        Integer tt1OwnWeight = tt1.getOwnWeight();
        Integer tt2OwnWeight = tt2.getOwnWeight();
        Integer tt1TarWeight = tt1.getTargetWeight();
        Integer tt2TarWeight = tt2.getTargetWeight();

        // check for symbol clash
        if(!tt1Target.isVariableNode() && !tt2Target.isVariableNode()){
            TRSFunctionApplication ftt1Target = (TRSFunctionApplication) tt1Target.getTerm();
            TRSFunctionApplication ftt2Target = (TRSFunctionApplication) tt2Target.getTerm();
            if(!ftt1Target.getRootSymbol().equals(ftt2Target.getRootSymbol())){
                // crash!
                return false;
            }
        }

        // add links for solution extraction
        // t1 is a variable
        if(t1.isVariableNode()){
            if(!t2.isVariableNode()){
                if(t1.getSolExtractList()==null){
                    t1.setSolExtractList(new ArrayList<LinkTriple>());
                }
                t1.getSolExtractList().add(0,new LinkTriple(c1,c2,t2));
            }
            else{
                // if both are variables the link for solution extraction is added depending on the variable order
                if(t1.getOrder() < t2.getOrder()){
                    if(t2.getSolExtractList()==null){
                        t2.setSolExtractList(new ArrayList<LinkTriple>());
                    }
                    t2.getSolExtractList().add(0, new LinkTriple(c2,c1,t1));
                }
                else if(t2.getOrder() < t1.getOrder()){
                    if(t1.getSolExtractList()==null){
                        t1.setSolExtractList(new ArrayList<LinkTriple>());
                    }
                    t1.getSolExtractList().add(0, new LinkTriple(c1,c2,t2));
                }
                // the case that both orders are equal will be checked when self loops are processed
            }
        }
        // t1 is not a variable
        else{
            if(t2.isVariableNode()){
                if(t2.getSolExtractList()==null){
                    t2.setSolExtractList(new ArrayList<LinkTriple>());
                }
                t2.getSolExtractList().add(0, new LinkTriple(c2,c1,t1));
            }
        }
        // if both are function symbols no link is added
        // System.out.println(t1 + "   {" + c1 + "} ---- {" + c2 + "}   " + t2);

        // the two links have the same represantative so calculate new weights
        if(tt1Target==tt2Target){
            List<Pair<Integer,Integer>> actList = new LinkedList<Pair<Integer,Integer>>();
            actList.add(new Pair<Integer,Integer>(tt2TarWeight, tt2OwnWeight));
            actList.add(new Pair<Integer,Integer>(c2,c1));
            actList.add(new Pair<Integer,Integer>(tt1OwnWeight, tt1TarWeight));
            newWeights = this.getWeights(actList);

            if(newWeights.x.equals(newWeights.y)){
                return true;
            }
            else{
                // check self loop case
                if(tt1Target.isSelfLoop()){
                    // if source weigth is lower than target weight swap the weights
                    if(newWeights.x < newWeights.y){
                        int temp = newWeights.x;
                        newWeights.x = newWeights.y;
                        newWeights.y = temp;
                    }
                    tt1Target.getSelfLoopWeights().x = this.greatestCommonDivisor((newWeights.x - newWeights.y) , (tt1Target.getSelfLoopWeights().x - tt1Target.getSelfLoopWeights().y));
                    if(newWeights.y < tt1Target.getSelfLoopWeights().y){
                        tt1Target.getSelfLoopWeights().x = tt1Target.getSelfLoopWeights().x + newWeights.y;
                        tt1Target.getSelfLoopWeights().y = newWeights.y;
                    }
                    else{
                        tt1Target.getSelfLoopWeights().x = tt1Target.getSelfLoopWeights().x + tt1Target.getSelfLoopWeights().y;
                    }
                }
                // check non self loop case and set a self loop on tt1
                else{
                    tt1Target.setSelfLoop(true);
                    if(newWeights.x > newWeights.y){
                        tt1Target.getSelfLoopWeights().x = newWeights.x;
                        tt1Target.getSelfLoopWeights().y = newWeights.y;
                    }
                    else{
                        tt1Target.getSelfLoopWeights().x = newWeights.y;
                        tt1Target.getSelfLoopWeights().y = newWeights.x;
                    }
                    // add self loop to the list which caches them
                    if(this.selfLoops == null){
                        this.selfLoops = new ArrayList<SemiUnificationNode>();
                    }
                    this.selfLoops.add(tt1Target);
                }
                // System.out.println("Adding a self loop on "+tt1.getTarget()+"weights "+ tt1.getTarget().getSelfLoopWeights().x +" and "+ tt1.getTarget().getSelfLoopWeights().y);

                return true;
            }
        }
        // the links have different representatives so unite the two classes
        else{
            if(this.classRep(tt1Target,tt2Target) == 1){
                // the representative of tt1 will be new representative
                List<Pair<Integer,Integer>> actList = new LinkedList<Pair<Integer,Integer>>();
                actList.add(new Pair<Integer,Integer>(tt2TarWeight, tt2OwnWeight));
                actList.add(new Pair<Integer,Integer>(c2,c1));
                actList.add(new Pair<Integer,Integer>(tt1OwnWeight, tt1TarWeight));
                newWeights = this.getWeights(actList);
                w1 = newWeights.y;
                w2 = newWeights.x;

                // arange the new class which is the union of the two classes with tt1Target as new representative
                tt2Target.setClassRep(new LinkTriple(w1,w2,tt1Target));
                tt1Target.setSize(tt1.getTarget().getSize() + tt2Target.getSize());
                // System.out.println("Adding link    \n    " + tt2.getTarget() + " {" + w2 + "} -----> {" + w1 + "} " + tt1.getTarget());

                t2.setClassRep(new LinkTriple(c2,c1,t1));
                t1.setSize(t1.getSize() + t2.getSize());
            }
            else{
                // the representative of tt2 will be new representative
                List<Pair<Integer,Integer>> actList = new LinkedList<Pair<Integer,Integer>>();
                actList.add(new Pair<Integer,Integer>(tt1TarWeight, tt1OwnWeight));
                actList.add(new Pair<Integer,Integer>(c1,c2));
                actList.add(new Pair<Integer,Integer>(tt2OwnWeight, tt2TarWeight));
                newWeights = this.getWeights(actList);
                w1 = newWeights.x;
                w2 = newWeights.y;

                // arange the new class which is the union of the two classes with tt1Target as new representative
                tt1Target.setClassRep(new LinkTriple(w1,w2,tt2Target));
                tt2Target.setSize(tt1.getTarget().getSize() + tt2Target.getSize());
                // System.out.println("Adding link\n    " + tt1.getTarget() + " {" + w1 + "} -----> {" + w2 + "} " + tt2.getTarget());
            }

            // Add link for solution extraction. (Only if tt1 is not t1 or if tt2 is not t2 and one of tt1 and tt2 is a variable
            if((tt1Target!=t1) || (tt2Target!=t2)){
                // tt1.target is a variable
                if(tt1Target.isVariableNode()){
                    if(!tt2Target.isVariableNode()){
                        if(tt1Target.getSolExtractList()==null){
                            tt1Target.setSolExtractList(new ArrayList<LinkTriple>());
                        }
                        tt1Target.getSolExtractList().add(0, new LinkTriple(w1,w2,tt2.getTarget()));
                    }
                    else{
                        if(tt1Target.getOrder() < tt2Target.getOrder()){
                            if(tt2Target.getSolExtractList()==null){
                                tt2Target.setSolExtractList(new ArrayList<LinkTriple>());
                            }
                            tt2Target.getSolExtractList().add(0, new LinkTriple(w2,w1,tt1.getTarget()));
                        }
                        if(tt2Target.getOrder() < tt1Target.getOrder()){
                            if(tt1Target.getSolExtractList()==null){
                                tt1Target.setSolExtractList(new ArrayList<LinkTriple>());
                            }
                            tt1Target.getSolExtractList().add(0, new LinkTriple(w1,w2,tt2.getTarget()));
                        }
                    }
                }
                // tt1.target is not a variable
                else{
                    if(tt2.getTarget().isVariableNode()){
                        if(tt2.getTarget().getSolExtractList()==null){
                            tt2.getTarget().setSolExtractList(new ArrayList<LinkTriple>());
                        }
                        tt2.getTarget().getSolExtractList().add(0, new LinkTriple(w2,w1,tt1.getTarget()));
                    }
                }
            }
        }
        // check if there is no symbol clash at every child
        return this.semiUnifyPushDown(tt1Target,w1,tt2Target,w2);
    }

    /**
     * Pushes down the equivalence obligation to the children of the representatives of tt1 and tt2.
     * @return
     */
    private boolean semiUnifyPushDown(SemiUnificationNode t1, int w1, SemiUnificationNode t2, int w2){
        if(t1.getChildren().size()==0 || t2.getChildren().size()==0){
            return true;
        }
        for(int i=0; i < t1.getChildren().size(); i++){
            // return false if any semiUnify on two children returns false
            if(!this.semiUnify(t1.getChild(i), w1, t2.getChild(i), w2)){
                return false;
            }
        }
        return true;
    }

    /**
     * Finds and returns the class representative of node <code>t</code>.
     * As an add-on every link of a node which is visited during the find-procedure
     * which does not point at a class representative is moved to it.
     */
    private LinkTriple find(SemiUnificationNode t){
        if(t.getClassRep() == null){
            LinkTriple l = new LinkTriple(0,0,t);
            return l;
        }
        else{
            if(t.getClassRep().getTarget().getClassRep() == null){
                return t.getClassRep();
            }
            else{
                LinkTriple t1 = this.find(t.getClassRep().getTarget());
                Pair<Integer,Integer> p1 = new Pair<Integer,Integer>(t.getClassRep().getOwnWeight(), t.getClassRep().getTargetWeight());
                List<Pair<Integer,Integer>> weights = new LinkedList<Pair<Integer,Integer>>();
                weights.add(p1);
                weights.add(new Pair<Integer, Integer>(t1.getOwnWeight(), t1.getTargetWeight()));
                Pair<Integer,Integer> newWeights = this.getWeights((weights));

                t.getClassRep().setOwnWeight(newWeights.x);
                t.getClassRep().setTargetWeight(newWeights.y);
                t.getClassRep().setTarget(t1.getTarget());

                return t.getClassRep();
            }
        }
    }

    /**
     * Calculates the weights of the new link directly to the representative.
     * Have a look at the procedure semiUnify() to see how the list is filled.
     */
    private Pair<Integer,Integer> getWeights(List<Pair<Integer,Integer>> list){
        Pair<Integer,Integer> dummyPair = new Pair<Integer,Integer>(0,0);
        Pair<Integer,Integer> returnPair = new Pair<Integer,Integer>(0,0);

        if(list==null){
            return returnPair;
        }
        if(list.size()==1){
            return list.get(0);
        }
        int w1 = list.get(0).x;
        int w2 = list.get(0).y;
        // remove the first element from the list and calculate the weights of the rest recursively
        list.remove(0);
        dummyPair = this.getWeights(list);
        // add the weights from the rest to the computed values of the actual first element
        returnPair.x = Math.max(w1 , (w1 - w2) + dummyPair.x);
        returnPair.y = returnPair.x - (((w1 - w2) + dummyPair.x) - dummyPair.y);
        return returnPair;
    }

    /**
     * Checks which one of <code>t1</code> and <code>t2</code> will be representative
     * @return 1 iff t1 will be the representative, 2 otherwise
     */
    private int classRep(SemiUnificationNode t1, SemiUnificationNode t2){
        if(t1.isVariableNode() && t2.isVariableNode()){
            if(t1.getSize() >= 1){
                return 1;
            }
            else{
                return 2;
            }
        }
        if(t1.isFunctionNode() && t2.isFunctionNode()){
            if(t1.getSize() >= 2){
                return 1;
            }
            else{
                return 2;
            }
        }
        else{
            if(t1.isVariableNode()){
                return 2;
            }
            if(t2.isVariableNode()){
                return 1;
            }
        }
        return 0;
    }

    /**
     * Checks the dag for bad cycles.
     * @return true iff no bad cycle was found, false otherwise
     */
    private boolean cycleCheck(SemiUnificationNode t1, SemiUnificationNode t2){
        if(this.selfLoops != null){
            for(SemiUnificationNode node : this.selfLoops){
                if(!node.isProcessed()){
                    if(!this.pushLoop(node)){
                        return false;
                    }
                    else{
                        node.setProcessed(true);
                    }
                }
            }
        }

        for(SemiUnificationNode node : this.dag.variableNodes){
            if(!node.isProcessed()){
                if(!this.cycleVar(node,0)){
                    // bad cycle was found
                    return false;
                }
                else{
                    node.setProcessed(true);
                }
            }
        }
        return true;
    }

    /**
     * Pushes down every loop to the variable nodes.
     */
    private boolean pushLoop(SemiUnificationNode t){
        SemiUnificationNode r = this.find(t).getTarget();
        r.setSelfLoop(true);
        if(r.isProcessed()){
            return true;
        }
        if(r.isInStack()){
            return false;
        }
        r.setInStack(true);

        for(SemiUnificationNode node : r.getChildren()){
            if(!this.pushLoop(node)){
                return false;
            }
        }
        r.setInStack(false);
        r.setProcessed(true);
        t.setProcessed(true);

        return true;
    }

    /**
     * Checks if there is a bad cycle for node <code>t</code>
     */
    private boolean cycleVar(SemiUnificationNode t, int c){
        LinkTriple tt1 = this.find(t);
        SemiUnificationNode r = tt1.getTarget();
        int w1 = tt1.getOwnWeight();
        int w2 = tt1.getTargetWeight();

        if(r.isProcessed()){
            return true;
        }
        if(r.isInStack()){
            if(r.getCycleCost() >= c + w1 - w2){
                return false;
            }
            else{
                return true;
            }
        }
        else{
            r.setCycleCost(c + w1 - w2);
            r.setInStack(true);

            for(SemiUnificationNode node: r.getChildren()){
                if(!this.cycleVar(node, c + w1 - w2)){
                    return false;
                }
            }
            r.setInStack(false);
            r.setProcessed(true);
            t.setProcessed(true);

            return true;
        }
    }

    /**
     * Well-known algorithm to compute the greatest common divisor.
     */
    private int greatestCommonDivisor(int m, int n){
        if(m < n){
            return this.greatestCommonDivisor(n,m);
        }
        else{
            if(n==0){
                return m;
            }
            else{
                int r = m % n;
                return this.greatestCommonDivisor(n,r);
            }
        }
    }

    /**
     * Part of the "Mexican" solution extraction.
     */
    private void pushSubterm(SemiUnificationNode t, Pair<Integer,Integer> p, int ord){
        if(t.isFunctionNode()){
            TRSFunctionApplication f = (TRSFunctionApplication)t.getTerm();
            if(f.getRootSymbol().getArity()==0){
                return;
            }
        }
        Pair<Integer,Integer> selfLoopWeightsOfT = t.getSelfLoopWeights();
        if(t.isSelfLoop()){
            selfLoopWeightsOfT.x = this.greatestCommonDivisor(selfLoopWeightsOfT.x - selfLoopWeightsOfT.y, p.x - p.y);
            if(selfLoopWeightsOfT.y < p.y){
                selfLoopWeightsOfT.x = selfLoopWeightsOfT.x + selfLoopWeightsOfT.y;
            }
            else{
                selfLoopWeightsOfT.x = selfLoopWeightsOfT.x + p.y;
                selfLoopWeightsOfT.y = p.y;
            }
        }
        else{
            t.setSelfLoop(true);
            selfLoopWeightsOfT.x = p.x;
            selfLoopWeightsOfT.y = p.y;
        }

        if(t.isVariableNode()){
            if((ord>0) && (t.getOrder() > ord)){
                this.simplifyVar(t,ord);
            }
        }
        this.pushDown(t);
    }

    /**
     * Part of the "Mexican" solution extraction.
     */
    private void pushDown(SemiUnificationNode t){
        if(t.isFunctionNode()){
            for(SemiUnificationNode child : t.getChildren()){
                this.pushSubterm(child, t.getSelfLoopWeights(), 0);
            }
        }
    }


    /**
     * Part of the "Mexican" solution extraction.
     * Pushes down the self loops to the variables
     */
    private void pushLoops(){
        if(this.selfLoops==null){
            return;
        }
        for(SemiUnificationNode n : this.selfLoops){
            this.pushDown(n);
        }
    }

    /**
     * Part of the "Mexican" solution extraction.
     * Simplifies the link <code>l1</code> with <code>l2</code> depending on the variable order.
     */
    private void simplifyRule(LinkTriple l1, LinkTriple l2, int ord){
        SemiUnificationNode l1Target = l1.getTarget();
        SemiUnificationNode l2Target = l2.getTarget();
        Pair<Integer,Integer> l1TargetSelfLoopWeights = l1Target.getSelfLoopWeights();

        int c1 = (l1.getOwnWeight() - l2.getOwnWeight()) + l2.getTargetWeight();
        int c2 = l1.getTargetWeight();

        if(l1Target.isVariableNode()){
            if(l2Target.isVariableNode()){
                if(l2Target.getOrder() < l1Target.getOrder()){
                    LinkTriple aux = new LinkTriple(c2,c1,l2Target);
                    // System.out.println("add " + aux);
                    l1Target.getSolExtractList().add(0,aux);
                }
                else{
                    if(l2Target.getOrder() > l1Target.getOrder()){
                        LinkTriple aux = new LinkTriple(c1,c2,l1Target);
                        // System.out.println("add " + aux);
                        l2Target.getSolExtractList().add(0,aux);
                    }
                    else{
                        if(c1!=c2){
                            if(l1Target.isSelfLoop()){
                                if(c1<c2){
                                    int cc = c1;
                                    c1 = c2;
                                    c2 = cc;
                                }
                                l1TargetSelfLoopWeights.x = this.greatestCommonDivisor((c1-c2), (l1TargetSelfLoopWeights.x - l1TargetSelfLoopWeights.y));
                                if(c2 < l1TargetSelfLoopWeights.y){
                                    l1TargetSelfLoopWeights.x = l1TargetSelfLoopWeights.x + c2;
                                    l1TargetSelfLoopWeights.y = c2;
                                }
                                else{
                                    l1TargetSelfLoopWeights.x = l1TargetSelfLoopWeights.x + l1TargetSelfLoopWeights.y;
                                }
                            }
                            else{
                                l1Target.setSelfLoop(true);
                                if(c1 > c2){
                                    l1TargetSelfLoopWeights.x = c1;
                                    l1TargetSelfLoopWeights.y = c2;
                                }
                                else{
                                    l1TargetSelfLoopWeights.x = c2;
                                    l1TargetSelfLoopWeights.y = c1;
                                }
                            }
                        }
                    }
                }
            }
            else{
                LinkTriple aux = new LinkTriple(c2,c2,l2Target);
                // System.out.println("add " + aux);
                l1Target.getSolExtractList().add(0,aux);
            }
        }
        else{
            if(l2Target.isVariableNode()){
                LinkTriple aux = new LinkTriple(c1,c2,l1Target);
                // System.out.println("add " + aux);
                l2Target.getSolExtractList().add(0,aux);
            }
            else{
                if((l1Target==l2Target) && !l1Target.isConstantNode()){
                    Pair<Integer,Integer> pair = new Pair<Integer,Integer>(0,0);
                    if(c1 > c2){
                        pair.x = c1;
                        pair.y = c2;
                    }
                    else{
                        pair.x = c2;
                        pair.y = c1;
                    }
                    this.pushSubterm(l1Target,pair,ord);
                }
            }
        }
    }

    /**
     * Part of the "Mexican" solution extraction.
     * Simplifies the links of the extraction list of the variable depending on the variable order
     * until only one link remains.
     */
    private void simplifyVar(SemiUnificationNode t, int ord){
        if(t.getSolExtractList()==null){
            return;
        }
        while(t.getSolExtractList().size()>=2){
            //int c1;
            //int c2;
            LinkTriple l1 = t.getSolExtractList().get(0);
            LinkTriple l2 = t.getSolExtractList().get(1);

            // System.out.println("Simplifying: {" + l1.getOwnWeight() + "} " + t + " ---> {" + l1.getTargetWeight() + "} " + l1.getTarget() + " and {" + l2.getOwnWeight() + "} " + t + " ---> {" + l2.getTargetWeight() + "} " + l2.getTarget());

            if(l1.equals(l2)){
                t.getSolExtractList().remove(0);
                continue;
            }

            // start simplifying the actual rules depending on the source weight
            if(l1.getOwnWeight() > l2.getOwnWeight()){
                t.getSolExtractList().remove(0);
                this.simplifyRule(l1,l2,ord);
            }
            else{
                t.getSolExtractList().remove(1);
                this.simplifyRule(l2,l1,ord);
            }

            if(t.isSelfLoop()){
                int d1;
                int d2;

                int tSelfX = t.getSelfLoopWeights().x;
                int tSelfY = t.getSelfLoopWeights().y;
                LinkTriple firstElemOfSolExtr = t.getSolExtractList().get(0);

                // At this point some examples don't terminate.
                while(tSelfX <= firstElemOfSolExtr.getOwnWeight()){
                    firstElemOfSolExtr.setOwnWeight((firstElemOfSolExtr.getOwnWeight() - tSelfX) + tSelfY);
                }

                d1 = (tSelfX - firstElemOfSolExtr.getOwnWeight()) + firstElemOfSolExtr.getTargetWeight();
                d2 = tSelfY;

                LinkTriple aux = new LinkTriple(d2,d1,firstElemOfSolExtr.getTarget());
                if(firstElemOfSolExtr.getOwnWeight() > aux.getOwnWeight()){
                    this.simplifyRule(firstElemOfSolExtr, aux, ord);
                }
                else{
                    this.simplifyRule(aux, firstElemOfSolExtr, ord);
                    t.getSolExtractList().set(0,aux);
                }
            }
        }
    }

    /**
     * Part of the "Mexican" solution extraction.
     * Simplifies every extraction list of all variables in the dag.
     */
    private void simplify(){
        List<TRSVariable> dummyList = new ArrayList<TRSVariable>();
        for(TRSVariable actVar : this.variableOrder){
            dummyList.add(0,actVar);
        }
        for(TRSVariable actVar : dummyList){
            SemiUnificationNode actNode = this.dag.termAtNode.get(actVar);
            // System.out.println("** " + actNode + " **");
            // System.out.println(actNode.getSolExtractList());
            this.simplifyVar(actNode,actNode.getOrder());
        }
    }

    /**
     * Returns all constraints which were build during the semiunification-procedure.
     */
    private Set<Pair<TRSTerm,TRSTerm>> getAlgoConstraints(){;
        Set<Pair<TRSTerm,TRSTerm>> cons = new LinkedHashSet<Pair<TRSTerm,TRSTerm>>();
        for(TRSVariable var : this.variableOrder){
            SemiUnificationNode n = this.dag.termAtNode.get(var);
            if(n.getSolExtractList() != null){
                for(LinkTriple linksForVar : n.getSolExtractList()){
                    //System.out.println(n.getSolExtractList());
                    TRSTerm key   = PhiTermFunctions.constructPhiTerm(var,linksForVar.getOwnWeight(), this.phi);
                    TRSTerm value = PhiTermFunctions.constructPhiTerm(linksForVar.getTarget().getTerm(),linksForVar.getTargetWeight(), this.phi);
                    cons.add(new Pair<TRSTerm,TRSTerm>(key,value));
                }
            }
            else{
                if(n.isSelfLoop()){
                    TRSTerm key = PhiTermFunctions.constructPhiTerm(var,n.getSelfLoopWeights().x, this.phi);
                    TRSTerm value = PhiTermFunctions.constructPhiTerm(var,n.getSelfLoopWeights().y, this.phi);
                    cons.add(new Pair<TRSTerm,TRSTerm>(key,value));
                }
            }
        }
        return cons;
    }

    /**
     * Be aware of the side effect this method can make! The algorithm should only run once but is called here. So be sure
     * that the algorithm was never started before.
     */
    @Override
    public String export(Export_Util eo){
        return this.export(eo,false);
    }

    public String export(Export_Util eo, boolean debugInfo){
        StringBuilder s = new StringBuilder();
        s.append("SemiUnification problem: " + this.term1 + " <=? " + this.term2 + "\n\n");
        boolean semiUnify = this.semiUnify();

        if(semiUnify){
            s.append("These terms semiunify" + eo.linebreak() + eo.linebreak());
            long a = 0;
            long b = 0;
            if(debugInfo){
                a = System.nanoTime();
            }
            Pair<TRSSubstitution,TRSSubstitution> substPair = this.getSubstitutions();
            if(debugInfo){
                b = System.nanoTime();
            }
            TRSSubstitution ma = substPair.x;
            TRSSubstitution se = substPair.y;

            s.append("Matcher:     " + substPair.x + eo.linebreak());
            s.append("Semiunifier: " + substPair.y);

            if(debugInfo){
                TRSTerm newTerm1 = this.term1.applySubstitution(se).applySubstitution(ma);
                TRSTerm newTerm2 = this.term2.applySubstitution(se);
                s.append(eo.linebreak() + eo.linebreak());
                s.append("The terms after applying the substitutions:" + eo.linebreak());
                s.append(newTerm1 + " and " + eo.linebreak() + newTerm2);
                s.append(eo.linebreak() + eo.linebreak());
                s.append("It took " + ((b-a)/1000000) + " ms");
            }
        }
        else{
            s.append("These terms do not semiunify");
        }
        return s.toString();
    }

    @Override
    public String toString(){
        return this.export(new PLAIN_Util(),false);
    }

    /**
     * This prints out some extra stuff like used time or the terms after applying the substitutions.
     */
    public String debugOutput(Export_Util eo){
        return this.export(eo,true);
    }

    /**
     * @return the actual state of the DAG
     */
    public String getDotOfDag() {
        return this.dag.toDOT();
    }
}