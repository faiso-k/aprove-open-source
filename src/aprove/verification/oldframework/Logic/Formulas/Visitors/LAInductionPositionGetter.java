package aprove.verification.oldframework.Logic.Formulas.Visitors;

import java.util.*;

import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Logic.Formulas.*;
import aprove.verification.oldframework.Rewriting.*;
import aprove.verification.oldframework.Syntax.*;

/**
 * Finds all positions where where can do induction using LA.
 * There must be a LA based function symbol with LA terms as arguments.
 *
 * A LA term is
 *   - a variable of sort Nat
 *   - the term Zero
 *   - a term succ( t_1 ) where t_1 is a LA term
 *   - a term plus( t_1, t_2 ) where t_1 and t_2 are LA terms
 *
 *
 * @author dickmeis
 * @version $Id$
 */

public class LAInductionPositionGetter implements CoarseFormulaVisitor<Object> , FineGrainedTermVisitor<Boolean> {

    LAProgramProperties laProgramProperties;

    Position position;

    ArrayList<Position> positionsOfLATerms;

    private LAInductionPositionGetter(LAProgramProperties laProgramProperties){
        this.position = Position.create();
        this.laProgramProperties = laProgramProperties;
        this.positionsOfLATerms = new ArrayList<Position>();
    }

    public static List<Position> apply(Formula formula, LAProgramProperties laProgramProperties) {
        LAInductionPositionGetter laPositionGetter = new LAInductionPositionGetter(laProgramProperties);
        formula.apply(laPositionGetter);
        return laPositionGetter.positionsOfLATerms;
    }

    @Override
    public Boolean caseConstructorApp(ConstructorApp cterm) {
        ConstructorSymbol cs = cterm.getConstructorSymbol();

        if(cs.equals(this.laProgramProperties.csZero)){
            return true;
        }
        else if(cs.equals(this.laProgramProperties.csSucc)){
            this.position.add(0);
            Boolean subTermIsLA = cterm.getArgument(0).apply(this);
            if(subTermIsLA){
                return true;
            }
        }

        return false;
    }

    @Override
    public Boolean caseDefFunctionApp(DefFunctionApp fterm) {
        SyntacticFunctionSymbol fs = fterm.getFunctionSymbol();

        Position pos = this.position.deepcopy();

        if (fs.equals(this.laProgramProperties.fsPlus)){
            this.position.add(0);
            Boolean subTerm0IsLA = fterm.getArgument(0).apply(this);
            this.position = pos.deepcopy();;

            this.position.add(1);
            Boolean subTerm1IsLA = fterm.getArgument(1).apply(this);

            if(subTerm0IsLA && subTerm1IsLA){
                if(!fterm.getVars().isEmpty()){
                    this.positionsOfLATerms.add(pos);
                }
                return true;
            }
        }
        else{
            List<AlgebraTerm> args = fterm.getArguments();

            int argpos = 0;
            Boolean argsAreLA = true;
            for (AlgebraTerm term : args) {
                this.position.add(argpos);

                Boolean subTermIsLA = term.apply(this);
                argsAreLA = argsAreLA && subTermIsLA;

                argpos++;
                this.position = pos.deepcopy();
            }

            if(argsAreLA &&
                    this.laProgramProperties.laBasedFunctionSymbols.contains(fs) &&
                    !fterm.getVars().isEmpty()){
                this.positionsOfLATerms.add(pos);
            }
        }

        return false;
    }

    @Override
    public Boolean caseMetaFunctionApplication(MetaFunctionApplication metaFunctionApplication) {

        Position pos = this.position.deepcopy();

        List<AlgebraTerm> args = metaFunctionApplication.getArguments();

        int argpos = 0;
        Boolean argsAreLA = true;
        for (AlgebraTerm term : args) {
            this.position.add(argpos);

            Boolean subTermIsLA = term.apply(this);
            argsAreLA = argsAreLA && subTermIsLA;

            argpos++;
            this.position = pos.deepcopy();
        }

        if(argsAreLA && !metaFunctionApplication.getVars().isEmpty()){
            this.positionsOfLATerms.add(this.position);
        }

        return false;
    }

    @Override
    public Boolean caseVariable(AlgebraVariable v) {
        if (v.getSort().equals(this.laProgramProperties.sortNat)){
            return true;
        }
        else{
            return false;
        }
    }

    @Override
    public Object caseEquation(Equation eqFormula) {

        Position pos = this.position.deepcopy();

        this.position.add(0);
        eqFormula.getLeft().apply(this);
        this.position = pos;

        this.position.add(1);
        eqFormula.getRight().apply(this);

        return null;
    }

    @Override
    public Object caseJunctorFormula(JunctorFormula jFormula) {

        Position pos = this.position.deepcopy();

        this.position.add(0);
        jFormula.getLeft().apply(this);
        if (!( jFormula instanceof Not)) {
            this.position = pos;

            this.position.add(1);
            jFormula.getRight().apply(this);
        }
        return null;
    }

    @Override
    public Object caseTruthValue(FormulaTruthValue truthvalFormula) {
        return null;
    }

}
