package aprove.verification.oldframework.Logic.Formulas.Visitors;

import java.util.*;

import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Logic.Formulas.*;
import aprove.verification.oldframework.Rewriting.*;
import aprove.verification.oldframework.Syntax.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

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

public class LASubtermAndPositionGetter implements CoarseFormulaVisitor<Object> , FineGrainedTermVisitor<Boolean> {

    LAProgramProperties laProgramProperties;

    Position position;

    List<Pair<AlgebraTerm, Position>> laSubtermsAndPositions;

    private LASubtermAndPositionGetter(LAProgramProperties laProgramProperties){
        this.position = Position.create();
        this.laProgramProperties = laProgramProperties;
        this.laSubtermsAndPositions = new ArrayList<Pair<AlgebraTerm, Position>>();
    }

    public static List<Pair<AlgebraTerm, Position>> apply(Formula formula, LAProgramProperties laProgramProperties) {
        LASubtermAndPositionGetter laPositionGetter = new LASubtermAndPositionGetter(laProgramProperties);
        formula.apply(laPositionGetter);
        return laPositionGetter.laSubtermsAndPositions;
    }

    @Override
    public Boolean caseConstructorApp(ConstructorApp cterm) {
        ConstructorSymbol cs = cterm.getConstructorSymbol();

        if(cs.equals(this.laProgramProperties.csZero)){
            // do not abstract from numbers
            return true;
        }
        else if(cs.equals(this.laProgramProperties.csSucc)){
            // do not abstract from numbers
            // but maybe this is a complex term
            // we take care of numbers later
            Position pos = this.position.deepcopy();
            Pair<AlgebraTerm, Position> p = new Pair<AlgebraTerm, Position>(cterm, pos);
            this.laSubtermsAndPositions.add(p);

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

                Pair<AlgebraTerm, Position> p = new Pair<AlgebraTerm, Position>(fterm, pos);
                this.laSubtermsAndPositions.add(p);

                return true;
            }
        }
        else{
            List<AlgebraTerm> args = fterm.getArguments();

            int argpos = 0;
            for (AlgebraTerm term : args) {
                this.position.add(argpos);

                term.apply(this);

                argpos++;
                this.position = pos.deepcopy();
            }

        }

        return false;
    }

    @Override
    public Boolean caseMetaFunctionApplication(MetaFunctionApplication metaFunctionApplication) {

        Position pos = this.position.deepcopy();

        List<AlgebraTerm> args = metaFunctionApplication.getArguments();

        int argpos = 0;
        for (AlgebraTerm term : args) {
            this.position.add(argpos);

            term.apply(this);

            argpos++;
            this.position = pos.deepcopy();
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
