/**
 *
 */
package aprove.verification.dpframework.DPProblem.Processors;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.dpframework.TRSProblem.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.Graph.*;
import immutables.*;

/**
 * @author swiste
 *
 */
@NoParams
public class QDPPairToRuleProcessor extends QDPProblemProcessor {
    /* (non-Javadoc)
     * @see aprove.verification.dpframework.DPProblem.Processors.QDPProblemProcessor#isQDPApplicable(aprove.verification.dpframework.DPProblem.QDPProblem)
     */
    @Override
    public boolean isQDPApplicable(QDPProblem qdp) {
        return qdp.getDependencyGraph().isSCC();
    }

    /* (non-Javadoc)
     * @see aprove.verification.dpframework.DPProblem.Processors.QDPProblemProcessor#processQDPProblem(aprove.verification.dpframework.DPProblem.QDPProblem, aprove.strategies.Abortions.Abortion)
     */
    @Override
    protected Result processQDPProblem(QDPProblem qdp, Abortion aborter)
            throws AbortionException {
        QDependencyGraph qdpGraph = qdp.getDependencyGraph();
        if (!qdpGraph.isSCC()) {
            return ResultFactory.unsuccessful();
        }
        Set<FunctionSymbol> constructorSymbols = new LinkedHashSet<FunctionSymbol>(qdp.getPRSignature());
        Set<FunctionSymbol> rDefinedSymbols = qdp.getRwithQ().getDefinedSymbolsOfR();
        constructorSymbols.removeAll(rDefinedSymbols);
        Graph<Rule,?> graph = qdpGraph.getGraph();
        Set<Node<Rule>> pNodes = graph.getNodes();
        Set<Node<Rule>> loops = new LinkedHashSet<Node<Rule>>();
        for (Node<Rule> pNode : pNodes){
            Set<Node<Rule>> oNodes = graph.getOut(pNode);
            if (oNodes != null && oNodes.contains(pNode)){
                Rule p = pNode.getObject();
                if (constructorSymbols.containsAll(p.getFunctionSymbols())){
                    Set<Rule> pred = graph.getObjectsFromNodes(graph.getIn(pNode));
                    Set<Rule> succ = graph.getObjectsFromNodes(graph.getOut(pNode));
                    pred.remove(p);
                    succ.remove(p);
                    QDPPairToRuleProof proof = new QDPPairToRuleProof();
                    QDPProblem nqdp = this.generateNewQDP(qdp,pred,p,succ,proof);
                    Set<Rule> newP2 = new LinkedHashSet<Rule>();
                    newP2.add(p);
                    QDPProblem n2qdp = QDPProblem.create(newP2, QTRSProblem.create(ImmutableCreator.create(new LinkedHashSet())), qdp.getMinimal());
                    Set<BasicObligation> aset = new LinkedHashSet<BasicObligation>();
                    aset.add(nqdp);
                    aset.add(n2qdp);
                    return ResultFactory.provedAnd(aset, YNMImplication.EQUIVALENT,proof);
                 }
            }
        }
        return ResultFactory.unsuccessful();
    }

    private QDPProblem generateNewQDP(QDPProblem oldqdp, Set<Rule> pred, Rule p, Set<Rule> succ,QDPPairToRuleProof proof) {
        proof.setPair(p);
        Set<String> used = new LinkedHashSet<String>();
        for (FunctionSymbol f : oldqdp.getPRSignature()){
           used.add(f.getName());
        }
        FreshNameGenerator fng = new FreshNameGenerator(used,FreshNameGenerator.FRIENDLYNAMES);

        TRSFunctionApplication fal = p.getLeft();
        FunctionSymbol fsym = fal.getRootSymbol();

        TRSFunctionApplication far = (TRSFunctionApplication) p.getRight();
        ArrayList<TRSTerm> newlArgs = new ArrayList<TRSTerm>();
        ArrayList<TRSTerm> newrArgs = new ArrayList<TRSTerm>();
        int farity = fsym.getArity();
        boolean[] filter = new boolean[farity];
        int Hcount = 1;
        int Fcount = 0;

        for (int i = 0;i < farity; i++){
            TRSTerm lArg = fal.getArgument(i);
            TRSTerm rArg = far.getArgument(i);
            boolean same = lArg.equals(rArg);
            filter[i]= same;
            if (same){
                Hcount++;
            } else {
                Fcount++;
                newlArgs.add(lArg);
                newrArgs.add(rArg);
            }
        }

        FunctionSymbol hsym = FunctionSymbol.create(fng.getFreshName("H",false),Hcount);
        FunctionSymbol anfsym = FunctionSymbol.create(fng.getFreshName("anew_"+fsym.getName(),false),Fcount);
        FunctionSymbol nfsym = FunctionSymbol.create(fng.getFreshName("new_"+fsym.getName(),false),Fcount);
        FunctionSymbol cfsym = FunctionSymbol.create(fng.getFreshName("cons_"+fsym.getName(),false),Fcount);


        Set<TRSFunctionApplication> nQTerms = new LinkedHashSet<TRSFunctionApplication>();
        Set<Rule> nRules = new LinkedHashSet<Rule>();
        TRSFunctionApplication nfl = TRSTerm.createFunctionApplication(nfsym,ImmutableCreator.create(newlArgs));
        TRSFunctionApplication anfl = TRSTerm.createFunctionApplication(anfsym,ImmutableCreator.create(newlArgs));
        TRSFunctionApplication nfr = TRSTerm.createFunctionApplication(nfsym,ImmutableCreator.create(newrArgs));
        nRules.add(Rule.create(anfl,nfr));
        nRules.add(Rule.create(nfl,nfr));
        proof.setRules(nRules);
        nQTerms.add(nfl);
        nQTerms.add(anfl);

        Set<Rule> npred = new LinkedHashSet<Rule>();
        for (Rule pr : pred){
            TRSFunctionApplication fpr = (TRSFunctionApplication) pr.getRight();
            ArrayList<TRSTerm> nfargs = new ArrayList<TRSTerm>();
            ArrayList<TRSTerm> nhargs = new ArrayList<TRSTerm>();
            for (int i=0;i< farity;i++){
                if (filter[i]){
                    nhargs.add(fpr.getArgument(i));
                } else {
                    nfargs.add(fpr.getArgument(i));
                }
            }
            nhargs.add(TRSTerm.createFunctionApplication(anfsym,ImmutableCreator.create(nfargs)));
            npred.add(Rule.create(pr.getLeft(),TRSTerm.createFunctionApplication(hsym,ImmutableCreator.create(nhargs))));
        }
        /*{
            FunctionApplication fpr = (FunctionApplication) p.getLeft();
            ArrayList<Term> nfargs = new ArrayList<Term>();
            ArrayList<Term> nhargs = new ArrayList<Term>();
            for (int i=0;i< farity;i++){
                if (filter[i]){
                    nhargs.add(fpr.getArgument(i));
                } else {
                    nfargs.add(fpr.getArgument(i));
                }
            }
            nhargs.add(Term.createFunctionApplication(cfsym,ImmutableCreator.create(nfargs)));
            npred.add(Rule.create(Term.createFunctionApplication(hsym,ImmutableCreator.create(nhargs)),p.getRight()));
        }*/
        Set<Rule> nsucc = new LinkedHashSet<Rule>();
        for (Rule s :succ){
            TRSFunctionApplication fsl = (TRSFunctionApplication) s.getLeft();
            ArrayList<TRSTerm> nfargs = new ArrayList<TRSTerm>();
            ArrayList<TRSTerm> nhargs = new ArrayList<TRSTerm>();
            for (int i=0;i< farity;i++){
                if (filter[i]){
                    nhargs.add(fsl.getArgument(i));
                } else {
                    nfargs.add(fsl.getArgument(i));
                }
            }
            TRSFunctionApplication fl = TRSTerm.createFunctionApplication(nfsym,ImmutableCreator.create(nfargs));
            TRSTerm cfr = TRSTerm.createFunctionApplication(cfsym,ImmutableCreator.create(nfargs));
            nhargs.add(cfr);
            nsucc.add(Rule.create(TRSTerm.createFunctionApplication(hsym,ImmutableCreator.create(nhargs)),fsl));
            nRules.add(Rule.create(fl, cfr));
            nQTerms.add(fl);
        }
        proof.setIpairs(npred);
        proof.setOpairs(nsucc);
        Set<Rule> newP =  new LinkedHashSet<Rule>(oldqdp.getP());
        newP.remove(p);
        //newP.removeAll(pred);
        //newP.removeAll(succ);
        newP.addAll(npred);
        newP.addAll(nsucc);

        QTRSProblem oldqtrs =  oldqdp.getRwithQ();
        Set<Rule> newR = new LinkedHashSet<Rule>(oldqtrs.getR());
        Set<TRSFunctionApplication> newQ = new LinkedHashSet<TRSFunctionApplication>(oldqtrs.getQ().getTerms());
        newR.addAll(nRules);
        newQ.addAll(nQTerms);
        QTRSProblem newQTRS = QTRSProblem.create(ImmutableCreator.create(newR),newQ);
        return QDPProblem.create(newP,newQTRS,oldqdp.getMinimal());
    }

    private static final class QDPPairToRuleProof extends QDPProof {
        Rule pair;
        Set<Rule> rules;
        Set<Rule> ipairs;
        Set<Rule> opairs;

        @Override
        public String export(Export_Util o, VerbosityLevel l) {
           StringBuilder sb = new StringBuilder();
           sb.append("The dependency pair ");
           sb.append(this.pair.export(o));
           sb.append(" was transformed to the following new rules:");
           sb.append(o.set(this.rules,Export_Util.RULES));
           sb.append(o.linebreak());
           sb.append("the following new pairs maintain the fan-in:");
           sb.append(o.set(this.ipairs,Export_Util.RULES));
           sb.append(o.linebreak());
           sb.append("the following new pairs maintain the fan-out:");
           sb.append(o.set(this.opairs,Export_Util.RULES));
           return sb.toString();
        }

        public String toBibTeX() {
            return "";
        }

        public Set<Rule> getIpairs() {
            return this.ipairs;
        }

        public void setIpairs(Set<Rule> ipairs) {
            this.ipairs = ipairs;
        }

        public Set<Rule> getOpairs() {
            return this.opairs;
        }

        public void setOpairs(Set<Rule> opairs) {
            this.opairs = opairs;
        }

        public Rule getPair() {
            return this.pair;
        }

        public void setPair(Rule pair) {
            this.pair = pair;
        }

        public Set<Rule> getRules() {
            return this.rules;
        }

        public void setRules(Set<Rule> rules) {
            this.rules = rules;
        }

    }
}
