/**
 *
 */
package aprove.verification.oldframework.Utility.Graph;

import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;

/**
 * @author swiste
 *
 */
public class FunctionSymbolGraph extends Graph<FunctionSymbol,Object> {

    private SCCGraph<FunctionSymbol,Object> sccGraph;
    private Set<Rule> rules;

    /**
     *
     */
    public FunctionSymbolGraph(Set<Rule> rules) {
        for (Rule rule : rules){
            FunctionSymbol f = rule.getRootSymbol();
            for(FunctionSymbol rf : rule.getRight().getFunctionSymbols()){
                Node<FunctionSymbol> nf = this.getNodeFromObject(f);
                if (nf == null){
                    nf = new Node<FunctionSymbol>(f);
                }
                Node<FunctionSymbol> nrf = this.getNodeFromObject(rf);
                if (nrf == null){
                    nrf = new Node<FunctionSymbol>(rf);
                }
                this.addEdge(nf,nrf);
            }
        }
        this.rules = rules;
    }

    public Set<FunctionSymbol> getFunctionsymbolsOfSCCOf(FunctionSymbol f){
        Cycle<FunctionSymbol> scc = this.getSCCOf(f);
        if (scc == null) {
            Set<FunctionSymbol> fs = new LinkedHashSet<FunctionSymbol>();
            fs.add(f);
            return fs;
        }
        return scc.getNodeObjects();
    }

    public Cycle<FunctionSymbol> getSCCOf(FunctionSymbol f){
        // if you need some pleasure watch this:
        return ((this.sccGraph == null) ? this.sccGraph = new SCCGraph<FunctionSymbol,Object>(this) : this.sccGraph).getSccFromObject(f);
        /** if you need help read this:
            if (this.sccGraph == null) {
                this.sccGraph = new SCCGraph<FunctionSymbol,E>(this)
            }
            return this.sccGraph.getSccFromObject(f);
        }
        */
    }


}
