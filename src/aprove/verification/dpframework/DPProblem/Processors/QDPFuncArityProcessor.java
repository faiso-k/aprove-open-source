package aprove.verification.dpframework.DPProblem.Processors;

import java.util.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Proofs.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.dpframework.TRSProblem.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.oldframework.Utility.Graph.*;
import immutables.*;

@NoParams
public class QDPFuncArityProcessor extends QDPProblemProcessor{

    @Override
    public boolean isQDPApplicable(final QDPProblem qdp) {
        for (final FunctionSymbol f : qdp.getPRSignature()) {
            if (f.getArity() > 2) {
                return true;
            }
        }
        return false;
    }

    @Override
    protected Result processQDPProblem(final QDPProblem qdp, final Abortion aborter) throws AbortionException {
        final Set<FunctionSymbol> signatureComplete = qdp.getSignature();
        final Map<FunctionSymbol, ArrayList<FunctionSymbol>> freshNamesMap =
            this.calculateFreshNames(signatureComplete);
        final Map<TRSFunctionApplication, TRSFunctionApplication> transformedTermMap = new HashMap<TRSFunctionApplication, TRSFunctionApplication>();
        final Pair<LinkedHashSet<Rule>, Map<Rule, Rule>> newP = this.processRules(qdp.getP(), freshNamesMap, transformedTermMap);
        final LinkedHashSet<Rule> newR = this.processRules(qdp.getR(), freshNamesMap, transformedTermMap).x;
        final LinkedHashSet<TRSFunctionApplication> qTerms= new LinkedHashSet<TRSFunctionApplication>(qdp.getQ().getTerms());
        final LinkedHashSet<TRSFunctionApplication> newQ =
            this.processFApps(qTerms, freshNamesMap, transformedTermMap);
        final Graph<Rule, ?> oldGraph = qdp.getDependencyGraph().getGraph();

        final Set<Node<Rule>> oldNodes = oldGraph.getNodes();
        final Set<Node<Rule>> newNodes = new HashSet<Node<Rule>>(oldNodes.size());
        final Map<Node<Rule>, Node<Rule>> oldNodeToNewNodeMap = new HashMap<Node<Rule>, Node<Rule>>();
        final Map<Rule, Rule> oldToNewRuleMap = newP.y;

        for(final Node<Rule> oldNode : oldNodes) {
            final Node<Rule> newNode = new Node<Rule>(oldToNewRuleMap.get(oldNode.getObject())) ;
            newNodes.add(newNode);
            oldNodeToNewNodeMap.put(oldNode, newNode);
        }

        Set<Node<Rule>> oldOutgoingNodes;
        final Set<Edge<Object, Rule>> newEdges = new HashSet<Edge<Object,Rule>>();
        for(final Node<Rule> oldNode : oldNodes) {
            oldOutgoingNodes = oldGraph.getOut(oldNode);
            final Node<Rule> newStartNode = oldNodeToNewNodeMap.get(oldNode);
            for(final Node<Rule> oldOut : oldOutgoingNodes) {
                newEdges.add(new Edge<Object, Rule>(newStartNode, oldNodeToNewNodeMap.get(oldOut)));
            }
        }

        final Graph<Rule, Object> g = new Graph<Rule, Object>(newNodes, newEdges);
        final QTRSProblem newQTRS = QTRSProblem.create(
                ImmutableCreator.create(newR), newQ);
        //Just for debugging:
        final QDependencyGraph oldDPGraph = qdp.getDependencyGraph();
        final QDependencyGraph newQDPgraph = QDependencyGraph.create(newP.x, newQTRS, g, qdp.getDependencyGraph());
        final QDPProblem newQDP = QDPProblem.create(newQTRS, newQDPgraph, qdp.getMinimal(), qdp.isRRRQreducable());
        int numberOfSccs = 0;
        if(!newQDPgraph.isSCC()) {
            numberOfSccs = newQDPgraph.getSubSCCs().size() ;
        }
        final Proof p = new FuncArityProof(qdp, newQDP, numberOfSccs);
        final Result result = ResultFactory.proved(newQDP, YNMImplication.EQUIVALENT, p);
        return result;
    }

    private Map<FunctionSymbol, ArrayList<FunctionSymbol>> calculateFreshNames(final Set<FunctionSymbol> signat) {
        final HashMap<FunctionSymbol, ArrayList<FunctionSymbol>> freshNamesMap =
            new HashMap<FunctionSymbol, ArrayList<FunctionSymbol>>();
        final HashSet<String> fSymNames = new HashSet<String>();
        final LinkedHashSet<FunctionSymbol> highArityFSyms = new LinkedHashSet<FunctionSymbol>();
        for(final FunctionSymbol fSym : signat) {
            fSymNames.add(fSym.getName());
            if(fSym.getArity()>2) {
                highArityFSyms.add(fSym);
            }
        }
        final FreshNameGenerator freshgen =
            new FreshNameGenerator(fSymNames, FreshNameGenerator.TYPE_INFERENCE);
        for(final FunctionSymbol fSym : highArityFSyms) {
            final int arity = fSym.getArity();
            final ArrayList<FunctionSymbol> freshNames = new ArrayList<FunctionSymbol>(arity-1);
            for(int i=0; i<arity; i++) {
                freshNames.add(FunctionSymbol.create(
                        freshgen.getFreshName(fSym.getName(), false), 2));
            }
            freshNamesMap.put(fSym, freshNames);
        }
        return freshNamesMap;
    }


    private Pair<LinkedHashSet<Rule>, Map<Rule, Rule>> processRules(final Collection<Rule> rules,
            final Map<FunctionSymbol, ArrayList<FunctionSymbol>> freshNamesmap,
            final Map<TRSFunctionApplication, TRSFunctionApplication> transformedTermMap) {
        Pair<LinkedHashSet<Rule>, Map<Rule, Rule>> resultPair;
        final LinkedHashSet<Rule> newRules = new LinkedHashSet<Rule>();
        final Map<Rule, Rule> oldRuleToNewRuleMap = new HashMap<Rule, Rule>();
        TRSFunctionApplication newLhs;
        TRSTerm newRhs;
        Rule newR;
        for(final Rule r : rules) {
            newLhs = (TRSFunctionApplication) this.processTerm(r.getLeft(), freshNamesmap, transformedTermMap);
            newRhs = this.processTerm(r.getRight(), freshNamesmap, transformedTermMap);
            newR = Rule.create(newLhs, newRhs);
            newRules.add(newR);
            oldRuleToNewRuleMap.put(r, newR);
        }
        resultPair = new Pair<LinkedHashSet<Rule>, Map<Rule,Rule>>(newRules, oldRuleToNewRuleMap);
        return resultPair;
    }

    private LinkedHashSet<TRSFunctionApplication> processFApps(
                    final Collection<TRSFunctionApplication> fApps,
                    final Map<FunctionSymbol, ArrayList<FunctionSymbol>> freshNamesmap,
                    final Map<TRSFunctionApplication, TRSFunctionApplication> transformedTermMap) {
        final LinkedHashSet<TRSFunctionApplication> newFApps = new LinkedHashSet<TRSFunctionApplication>();
        TRSFunctionApplication newFApp;
        for(final TRSFunctionApplication fApp : fApps) {
            newFApp = (TRSFunctionApplication)this.processTerm(fApp, freshNamesmap, transformedTermMap);
            newFApps.add(newFApp);
        }
        return newFApps;
    }

    private TRSTerm processTerm(
        final TRSTerm oldterm,
        final Map<FunctionSymbol, ArrayList<FunctionSymbol>> freshNamesmap,
        final Map<TRSFunctionApplication, TRSFunctionApplication> transformedTermMap
    ) {
        TRSTerm result;
        // Variables don't need any transformation
        if (oldterm.isVariable()) {
            result = oldterm;
        } else {
            // Constants don't need any transformation
            if (oldterm.getSubTerms().size() == 1) {
                result = oldterm;
            } else {
                // oldterm has to be a Function Application with at least one
                // argument!!
                // recursiv call to transform all inner function symbols to
                // arity 2.
                final TRSFunctionApplication fApp = (TRSFunctionApplication) oldterm;
                final FunctionSymbol actFSym = fApp.getRootSymbol();
                final ImmutableList<? extends TRSTerm> args = fApp.getArguments();
                final ArrayList<TRSTerm> processedArgs = new ArrayList<TRSTerm>();
                for (final TRSTerm t : args) {
                    processedArgs.add(this.processTerm(t, freshNamesmap, transformedTermMap) );
                }
                final ArrayList<FunctionSymbol> freshNames = freshNamesmap.get(actFSym);
                if(freshNames == null) {
                    //the original fSym actFSym has arity 1 or 2.
                    //It has to be processed here.
                    if(Globals.useAssertions) {
                        final int arity = actFSym.getArity();
                        assert(arity < 3);
                        if(arity == 1) {
                            assert(processedArgs.size() == 1);
                        }
                        else {
                            assert(processedArgs.size() == 2);
                        }
                    }
                    result = TRSTerm.createFunctionApplication(
                            actFSym,
                            ImmutableCreator.create(processedArgs));

                }
                else {
                    final Pair<TRSFunctionApplication, TRSFunctionApplication> resultPair =
                        this.replaceHighArityFSymsRoot(fApp,freshNamesmap.get(actFSym), transformedTermMap);
                    transformedTermMap.put(resultPair.x, resultPair.y);
                    result = resultPair.y;
                }
            }
        }
        return result;
    }


    /**
     * This method is a wrapper for the actual transformation.<br>
     * It is also needed to remember the root position of the term
     * to be transformed.
     * @param fApp the FAppl with the high arity FSym at root position
     * @param freshNames list of "fresh" function symbols with arity 2
     * @return Pair of the old FApp fApp and the transformed fApp.
     */
    private Pair<TRSFunctionApplication, TRSFunctionApplication> replaceHighArityFSymsRoot(
            final TRSFunctionApplication fApp,
            final ArrayList<FunctionSymbol> freshNames,
            final Map<TRSFunctionApplication, TRSFunctionApplication> transformedTermMap) {
        TRSFunctionApplication transformedTerm;
        Pair<TRSFunctionApplication, TRSFunctionApplication> result;
        final ArrayList<TRSTerm> args = new ArrayList<TRSTerm>(fApp.getArguments());
        for(int i=0; i<args.size(); i++) {
            final TRSTerm t = args.get(i);
            if(! t.isVariable()) {
                final TRSFunctionApplication fApplic = (TRSFunctionApplication) t;
                if(transformedTermMap.containsKey(fApplic)) {
                    args.set(i, transformedTermMap.get(fApplic));
                }
            }
        }

        transformedTerm = (TRSFunctionApplication) this.replaceHighArityFSyms(args, freshNames, 0);
        result = new Pair<TRSFunctionApplication, TRSFunctionApplication>(fApp, transformedTerm);
        return result;
    }

    /**
     * This method does the actual transformation.<br>
     *  Replace in every rule the Function Symbols
     *  with arity bigger than 2 by a new construct<br>
     *  e.g. f(v, w, x, y, z) is transformed into
     *  f1( f2(f3(v, w), x), f4(y,z)<br>
     *  The result is a blanced tree!
     * @param args the arguments of the high arity function symbol
     * @param freshNames list of "fresh" function symbols with arity 2
     * @param position an integer, marking the position from where the
     *                 next "fresh" symbol is to be taken
     *
     * @return the transformed term
     */
    private TRSTerm replaceHighArityFSyms(
            final List<TRSTerm> args,
            final ArrayList<FunctionSymbol> freshNames,
            final int position) {

        final ArrayList<TRSTerm> arguments = new ArrayList<TRSTerm>(2);
        final int numberOfArgs = args.size();

        if(numberOfArgs == 2) {
            arguments.addAll(args);
            return TRSTerm.createFunctionApplication(
                    freshNames.get(position),
                    ImmutableCreator.create(arguments));
        }
        else {
            if(numberOfArgs > 2) {
                int half;
                if((numberOfArgs % 2) == 0) {
                    half = (numberOfArgs / 2);
                }
                else {
                    half = ((numberOfArgs / 2) + 1);
                }
                arguments.add(0,
                              this.replaceHighArityFSyms(
                                args.subList(0, half),
                                freshNames,
                                position + 1));

                arguments.add(1,
                              this.replaceHighArityFSyms(
                                args.subList(half, numberOfArgs),
                                freshNames,
                                (position + half) ));

                return TRSTerm.createFunctionApplication(
                        freshNames.get(position),
                        ImmutableCreator.create(arguments));
                }
            else {
                if(Globals.useAssertions) {
                    assert(args.size() == 1);
                }
                return args.get(0);
            }
        }
    }


    private static class FuncArityProof extends QDPProof {

        private final QDPProblem qdpProblem;
        private final QDPProblem newQdp;
        private final int nrSccs;

        private FuncArityProof(final QDPProblem qdp, final QDPProblem newQdp, final int nrSccs) {
            this.qdpProblem = qdp;
            this.newQdp = newQdp;
            this.nrSccs = nrSccs;
        }

        @Override
        public String export(final Export_Util eu, final VerbosityLevel level) {
            final StringBuffer buffy = new StringBuffer();
            buffy.append("The approximation of the Dependency Graph ");
            buffy.append(eu.cite(Citation.LOPSTR));
            buffy.append(" contains ");
            buffy.append(this.nrSccs);
            buffy.append(" SCC");
            if(this.nrSccs > 1) {
                buffy.append('s');
            }
            buffy.append(eu.linebreak());
            buffy.append(eu.export("Q DP problem:"));
            buffy.append(eu.cond_linebreak());
            if (this.newQdp.getP().isEmpty()) {
                buffy.append("P is empty.");
                buffy.append(eu.linebreak());
            } else {
                buffy.append(eu.export("The TRS P consists of the following transformed rules:"));
                buffy.append(eu.cond_linebreak());
                buffy.append(eu.set(this.newQdp.getP(), Export_Util.RULES));
                buffy.append(eu.cond_linebreak());
            }

            if (this.newQdp.getR().isEmpty()) {
                buffy.append("R is empty.");
                buffy.append(eu.linebreak());
            } else {
                buffy.append(eu.export("The TRS R consists of the following transformed rules:"));
                buffy.append(eu.cond_linebreak());
                buffy.append(eu.set(this.newQdp.getR(), Export_Util.RULES));
                buffy.append(eu.cond_linebreak());
            }

            if (this.newQdp.getQ().getTerms().isEmpty()) {
                buffy.append("Q is empty.");
                buffy.append(eu.linebreak());
            } else {
                buffy.append(eu.export("The set Q consists of the following transformed terms:"));
                buffy.append(eu.cond_linebreak());
                buffy.append(eu.set(this.newQdp.getQ().getTerms(), Export_Util.RULES));
                buffy.append(eu.cond_linebreak());
            }

            buffy.append(eu.export("We have to consider all "+(this.newQdp.getMinimal() ? "minimal " : "")+"(P,Q,R)-chains."));
            buffy.append(this.newQdp.export(eu));
            final String result = buffy.toString();
            return result;
        }

    }





}
