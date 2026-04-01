package aprove.verification.oldframework.Rewriting;

import java.util.*;

import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Syntax.*;
import aprove.verification.oldframework.Utility.Graph.*;

/**
 * Diese Klasse stellt die funktionalen Abhaengigkeiten dar
 * @author Rene Thiemann
 */
public class FunctionSymbolGraph extends Graph<DefFunctionSymbol,Object> {

/**
 * Returns the graph representing the functional dependencies
 * @param rules the rules or the program as source of dependencies
 * @param ignore Defined symbols that will be ignored for dependencies
 * @param onlyRight only look in right sides for dependencies
 * @param addLoops if true, then every node has an arc to itself
 * @param reverse if true, edges will be turned in the other direction
 */
    public FunctionSymbolGraph(Set<Rule> rules, Set<DefFunctionSymbol> ignore, boolean onlyRight,boolean addLoops, boolean reverse) {

    super();
    this.buildNodes(rules,ignore,addLoops);
    this.buildEdges(rules,ignore,onlyRight,reverse);

    }

    public FunctionSymbolGraph(Program prog, boolean onlyRight) {

    this(prog.getRules(), null, onlyRight, true, false);

    }

    /**
     * Returns the graph representing the functional dependencies
     * @param rules the rules or the program as source of dependencies
     * @param onlyRight only look in right sides for dependencies
     */
    public FunctionSymbolGraph(Set<Rule> rules, boolean onlyRight) {

    this(rules,null,onlyRight,false,false);

    }

    /**
     * Returns the graph representing the functional dependencies
     * @param rules the rules or the program as source of dependencies
     *        both left and right sides will result in dependencies
     */
    public FunctionSymbolGraph(Set<Rule> rules) {

    this(rules,false);

    }

    /**
     * Returns the graph representing the functional dependencies
     * @param prog the rules or the program as source of dependencies
     *        both left and right sides will result in dependencies
     */
    public FunctionSymbolGraph(Program prog) {

        this(prog.getRules());

    }

    void buildNodes(Set<Rule> rules, Set<DefFunctionSymbol> ignore, boolean addLoops) {

    Set<DefFunctionSymbol> nodes = new LinkedHashSet<DefFunctionSymbol>();
    // first collect nodes
    Iterator ruleIt = rules.iterator();
    while (ruleIt.hasNext()) {
        Rule r = (Rule) ruleIt.next();
        SyntacticFunctionSymbol f = r.getRootSymbol();
        if (ignore == null || !ignore.contains(f)) {
        nodes.add((DefFunctionSymbol)f);
        }
    }
    // then store them
    // direct storing would lead to duplicates
    Iterator<DefFunctionSymbol> nodeIt = nodes.iterator();
    while (nodeIt.hasNext()) {
        Node<DefFunctionSymbol> n = new Node<DefFunctionSymbol>(nodeIt.next());
        this.addNode(n);
        if (addLoops) {
        this.addEdge(n, n);
        }
    }
    }

    void buildEdges(Set<Rule> rules, Set<DefFunctionSymbol> ignore, boolean onlyRight, boolean reverse) {

    Iterator<Rule> ruleIt = rules.iterator();
    while (ruleIt.hasNext()) {
        Rule r = ruleIt.next();
        SyntacticFunctionSymbol f = r.getRootSymbol();
        Node<DefFunctionSymbol> fNode = null;
        if (f instanceof DefFunctionSymbol) {
            fNode = this.getNodeFromObject((DefFunctionSymbol)f);
        }
        if (fNode == null) {
        // ignoring f
        continue;
        }
        DefFunctionSymbol g;
        Iterator gIt;
        if (!onlyRight) {
        AlgebraTerm left = r.getLeft();
        gIt = left.getDefFunctionSymbols().iterator();
        while (gIt.hasNext()) {
            g = (DefFunctionSymbol) gIt.next();
            Node<DefFunctionSymbol> gNode = this.getNodeFromObject(g);
            if (gNode != null) {
            if (reverse) {
                this.addEdge(gNode, fNode);
            } else {
                this.addEdge(fNode, gNode);
            }
            }
        }
        }
        AlgebraTerm right = r.getRight();
        gIt = right.getDefFunctionSymbols().iterator();
        while (gIt.hasNext()) {
        g = (DefFunctionSymbol) gIt.next();
        Node<DefFunctionSymbol> gNode = this.getNodeFromObject(g);
        if (gNode != null) {
            if (reverse) {
            this.addEdge(gNode, fNode);
            } else {
            this.addEdge(fNode, gNode);
            }
        }
        }
    }

    }

    public boolean hasPath(DefFunctionSymbol from, DefFunctionSymbol to) {

        return this.hasPath(this.getNodeFromObject(from), this.getNodeFromObject(to));

    }

}
