package aprove.verification.oldframework.Input.Annotations;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.verification.oldframework.Logic.Formulas.*;
import aprove.verification.oldframework.Rewriting.*;
import aprove.verification.oldframework.TheoremProverProblem.*;


/**
 * Class implements an annotator for formulas. Formulas are
 * annotated by transforming them into their prenexnormalform.
 * @author rabe
 */
public class FormulaAnnotation extends Annotation{

    protected Program                program;

    protected List<Formula>            formulas;

    protected ObligationNode        root;

    protected List<BasicObligationNode>    positions;

    /**
     * Standard constructor for this annotator
     * @param formulas List of formula to be annotated
     */
    public FormulaAnnotation(List<Formula> formulas, Program program) {
        super();

        // init object's variables
        this.program = program;
        this.formulas = formulas;

        this.clearResult();
    }

    public void clearResult() {
        if( !this.formulas.isEmpty() && (this.program != null) ) {
            this.positions = new ArrayList<BasicObligationNode>();
            for(Formula formula : this.formulas) {
                BasicObligationNode node = new BasicObligationNode(
                        new TheoremProverObligation(formula, this.program));
                node.addTruthValueListener(TruthToLemmaDatabase.INSTANCE);
                this.positions.add(node);
            }
            if (this.positions.size() == 1) {
                this.root = this.positions.get(0);
            } else {
                this.root = JunctorObligationNode.createAnd(this.positions);
            }
        }
    }

    public List<Formula> getFormulas() {
        return this.formulas;
    }

    public ObligationNode getRoot() {
        return this.root;
    }

    public List<BasicObligationNode> getPositions() {
        return this.positions;
    }

    /**
     * Methode transform this annotator into string containig html
     */
    @Override
    public String toHTML() {
        StringBuffer  result;

        // init return value
        result = new StringBuffer();

        if( this.formulas != null ) {

            HTML_Util htmlUtil = new HTML_Util();

            result.append(htmlUtil.paragraph());
            result.append(htmlUtil.bold("Formulas to prove:"));
            result.append(htmlUtil.linebreak());
            // call toHTML for every formula and append result
            // to return value
            for(Formula formula : this.formulas) {
               result.append(htmlUtil.export(formula));
               result.append(htmlUtil.linebreak());
            }

        }
        return result.toString();
    }
}


