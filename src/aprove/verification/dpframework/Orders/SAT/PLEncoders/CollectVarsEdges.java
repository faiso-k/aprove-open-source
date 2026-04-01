package aprove.verification.dpframework.Orders.SAT.PLEncoders;

import java.util.*;

import aprove.verification.dpframework.Orders.SAT.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.PropositionalLogic.Formulae.*;
import aprove.verification.oldframework.PropositionalLogic.Formulae.Variable;
import aprove.verification.oldframework.PropositionalLogic.TheoryPropositions.*;

/**
 *
 * Traverses the Formula constraints to gather all used symbols.
 *
 */
// Factored out of SimpleBinaryPLEncoder, as it is useful for all Encoders.
class CollectVarsEdges extends MemorizingDepthFirstFormulaVisitor<None> {

    private Map<Variable<None>, Fact> poConstraints;

    CollectVarsEdges(Map<Variable<None>, Fact> poConstraints) {
        this.poConstraints = poConstraints;
    }

    Set<FunctionSymbol> vars = new LinkedHashSet<FunctionSymbol>();
    Map<FactBot, Variable<None>> bots = new LinkedHashMap<FactBot, Variable<None>>();
    Map<FactSucc, Variable<None>> succs = new LinkedHashMap<FactSucc, Variable<None>>();
    Map<FactEqual, Variable<None>> equals = new LinkedHashMap<FactEqual, Variable<None>>();
    @Override
    public Object caseVariable(Variable<None> var) {
        if (this.visited.contains(var)) {return null;} else {this.visited.add(var);}
        Fact fact = this.poConstraints.get(var);
        if (fact instanceof FactBot) {
            FactBot bot = (FactBot) fact;
            this.bots.put(bot, var);
            this.vars.add(bot.getFunctionSymbol());
        } else if (fact instanceof FactSucc) {
            FactSucc succ = (FactSucc) fact;
            this.succs.put(succ, var);
            this.vars.add(succ.getLeft());
            this.vars.add(succ.getRight());
        } else if (fact instanceof FactEqual) {
            FactEqual equal = (FactEqual) fact;
            this.equals.put(equal, var);
            this.vars.add(equal.getLeft());
            this.vars.add(equal.getRight());
        }
        return null;
    }
}