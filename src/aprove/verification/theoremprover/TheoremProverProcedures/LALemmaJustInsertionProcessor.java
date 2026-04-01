package aprove.verification.theoremprover.TheoremProverProcedures;

import java.util.*;

import aprove.prooftree.Obligations.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.dpframework.*;
import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Exceptions.*;
import aprove.verification.oldframework.LemmaDatabase.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Logic.Formulas.*;
import aprove.verification.oldframework.Logic.Formulas.Implication;
import aprove.verification.oldframework.Rewriting.*;
import aprove.verification.oldframework.Syntax.*;
import aprove.verification.oldframework.TheoremProverProblem.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.theoremprover.TheoremProverProofs.*;

/**
 * Processor that searches the lemma data base if there are lemmas including the
 * same uninterpreted function symbols as they occur in the formula which is to
 * prove. If so, a suitable instance of the corresponding lemma is inserted near
 * the equation containing that function symbol in a way that it is of use
 * during simplification.
 *
 * @author dickmeis
 * @version $Id$
 */
@NoParams
public class LALemmaJustInsertionProcessor extends TheoremProverProcessor {

    @Override
    public boolean isApplicable(BasicObligation obl) {
        if (obl instanceof TheoremProverObligation) {
            // only for indirect proofs
            TheoremProverObligation theorem_obl = (TheoremProverObligation) obl;
            return theorem_obl.isIndirectProof();
        }
        return false;
    }

    @Override
    protected Result process(TheoremProverObligation obligationInput,
            BasicObligationNode obligationNode, Abortion aborter,
            RuntimeInformation rti) throws AbortionException {

        Program program = obligationInput.getProgram();
        LAProgramProperties laProgram = program.laProgramProperties;

        Set<SyntacticFunctionSymbol> laFunctSymbols = new HashSet<SyntacticFunctionSymbol>(9);
        laFunctSymbols.add(laProgram.fsEqual);
        laFunctSymbols.add(laProgram.fsInequal);
        laFunctSymbols.add(laProgram.fsGreater);
        laFunctSymbols.add(laProgram.fsGreatereq);
        laFunctSymbols.add(laProgram.fsLess);
        laFunctSymbols.add(laProgram.fsLesseq);
        laFunctSymbols.add(laProgram.fsPlus);
        laFunctSymbols.add(laProgram.csSucc);
        laFunctSymbols.add(laProgram.csZero);

        Formula formula = obligationInput.getFormula();
        Set<AlgebraVariable> usedVariables = formula.getAllVariables();

        Set<Pair<AlgebraTerm, Position>> formulaMultiplicants = MultiplicantGetterVisitor
                .apply(formula, laFunctSymbols, laProgram);

        LemmaDatabase ldb = LemmaDatabaseFactory.getLemmmaDatabase();

        Set<Equation> equations = ldb.getAllEquations();

        Set<AlgebraTerm> usedMultiplicants = new HashSet<AlgebraTerm>();

        Set<Triple<Formula, Position, Boolean>> insertLemmasWithPosition = new HashSet<Triple<Formula, Position, Boolean>>();

        for (Formula lemma : equations) {
            lemma = lemma.deepcopy();
            lemma.renameAllVars(usedVariables);

            Set<Pair<AlgebraTerm, Position>> lemmaMultiplicants = MultiplicantGetterVisitor
                    .apply(lemma, laFunctSymbols, laProgram);

            for (Pair<AlgebraTerm, Position> lemmaMultiplicantWithPos : lemmaMultiplicants) {
                AlgebraTerm lemmaMultiplicant = lemmaMultiplicantWithPos.x;
                for (Pair<AlgebraTerm, Position> formulaMultiplicantWithPos : formulaMultiplicants) {
                    AlgebraTerm formulaMultiplicant = formulaMultiplicantWithPos.x;
                    try {
                        AlgebraSubstitution subst = lemmaMultiplicant.matches(formulaMultiplicant);
                        Formula insertLemma = lemma.apply(subst);
                        Triple<Formula, Position, Boolean> p = new Triple<Formula, Position, Boolean>(
                                insertLemma, formulaMultiplicantWithPos.y, true);
                        insertLemmasWithPosition.add(p);
                        usedMultiplicants.add(formulaMultiplicant);
                    }
                    catch (UnificationException e) {
                    }
                }
            }
        }




        Set<Implication> implications = ldb.getAllImplications();

        for (Implication lemma : implications) {
            lemma = (Implication) lemma.deepcopy();
            lemma.renameAllVars(usedVariables);

            Set<Pair<AlgebraTerm, Position>> lemmaMultiplicants = MultiplicantGetterVisitor
                    .apply(lemma.getRight(), laFunctSymbols, laProgram);

            for (Pair<AlgebraTerm, Position> lemmaMultiplicantWithPos : lemmaMultiplicants) {
                AlgebraTerm lemmaMultiplicant = lemmaMultiplicantWithPos.x;
                for (Pair<AlgebraTerm, Position> formulaMultiplicantWithPos : formulaMultiplicants) {
                    AlgebraTerm formulaMultiplicant = formulaMultiplicantWithPos.x;
                    try {
                        AlgebraSubstitution subst = lemmaMultiplicant.matches(formulaMultiplicant);
                        Formula insertLemma = lemma.apply(subst);
                        Triple<Formula, Position, Boolean> p = new Triple<Formula, Position, Boolean>(
                                insertLemma, formulaMultiplicantWithPos.y, true);
                        insertLemmasWithPosition.add(p);
                        usedMultiplicants.add(formulaMultiplicant);
                    }
                    catch (UnificationException e) {
                    }
                }
            }
        }

        if (insertLemmasWithPosition.isEmpty()) {
            return ResultFactory.notApplicable();
        }

        List<Formula> insertLemmas = new ArrayList<Formula>(
                                            insertLemmasWithPosition.size());

        Formula newFormula = formula.deepcopy();

        boolean isIndirectProof = obligationInput.isIndirectProof();

        for (Triple<Formula, Position, Boolean> pair : insertLemmasWithPosition) {

            if(pair.z == false){
                continue;
            }

            LemmaInsertVisitor lemmaAndInsertVisitor = new LemmaInsertVisitor(
                    pair.x, pair.y, isIndirectProof);
            try {
                newFormula = newFormula.apply(lemmaAndInsertVisitor);
            }
            catch (Exception e) {
                return ResultFactory.error(e);
            }
            insertLemmas.add(pair.x);
        }

        TheoremProverObligation newObligation = new TheoremProverObligation(
                                                        newFormula,
                                                        obligationInput);

        LALemmaJustInsertionProof proof = new LALemmaJustInsertionProof(
                                                usedMultiplicants, insertLemmas);

        return ResultFactory.proved(newObligation, YNMImplication.COMPLETE,
                                    proof);
    }

}

/**
 * Get every term out of a formula that is a function application of an
 * uninterpreted function symbol.
 */
class MultiplicantGetterVisitor implements CoarseGrainedTermVisitor<Object>,
        CoarseFormulaVisitor<Object> {

    Set<SyntacticFunctionSymbol> laFunctSymbols;

    Set<Pair<AlgebraTerm, Position>> multiplicants;

    Stack<Position> positionStack;

    private LAProgramProperties laProgram;

    /**
     * Constructs a set of terms occuring in the formula and being a function
     * application of an uninterpreted function symbol. With the terms the
     * position of the equation in the formula the terms occur in is stored,
     * too.
     *
     * @param formula
     *            The formula to search
     * @param laFunctSymbols
     *            As backgrund information all function smybols that are
     *            interpreted
     * @param laProgram
     *            More background information
     * @return a set of function applications of an uninterpreted function
     *         symbols with the position of the equation they occur in
     */
    public static Set<Pair<AlgebraTerm, Position>> apply(Formula formula,
            Set<SyntacticFunctionSymbol> laFunctSymbols, LAProgramProperties laProgram) {
        MultiplicantGetterVisitor multiplicantGetterVisitor
                = new MultiplicantGetterVisitor(laFunctSymbols, laProgram);
        formula.apply(multiplicantGetterVisitor);

        return multiplicantGetterVisitor.multiplicants;
    }

    public MultiplicantGetterVisitor(Set<SyntacticFunctionSymbol> laFunctSymbols,
            LAProgramProperties laProgram) {
        this.laFunctSymbols = laFunctSymbols;
        this.laProgram = laProgram;
        this.multiplicants = new HashSet<Pair<AlgebraTerm, Position>>();
        this.positionStack = new Stack<Position>();
        this.positionStack.push(Position.create());
    }

    @Override
    public Object caseFunctionApp(AlgebraFunctionApplication f) {

        Position pos = this.positionStack.peek();

        AlgebraFunctionApplication fappl = (AlgebraFunctionApplication) f;
        SyntacticFunctionSymbol fs = fappl.getFunctionSymbol();

        // ignore interpreted function symbols
        if (this.laFunctSymbols.contains(fs)) {
            for (AlgebraTerm t : fappl.getArguments()) {
                t.apply(this);
            }
        }
        /*
         * ignore terms of other sorts especially ignore true and false as they
         * are only syntactical necessary for an LA lemma
         */
        // this block must be placed behinde the second
        // because all LA predicats have the sort Bool
        else if (!f.getSort().equals(this.laProgram.sortNat)) {
            return null;
        }
        else {
            Pair<AlgebraTerm, Position> p = new Pair<AlgebraTerm, Position>(f, pos);
            this.multiplicants.add(p);
        }

        return null;
    }

    @Override
    public Object caseVariable(AlgebraVariable v) {
        return null;
    }

    @Override
    public Object caseEquation(Equation eqFormula) {

        AlgebraTerm left = eqFormula.getLeft();
        left.apply(this);

        AlgebraTerm right = eqFormula.getRight();
        right.apply(this);

        this.positionStack.pop();
        return null;
    }

    @Override
    public Object caseJunctorFormula(JunctorFormula jFormula) {

        Position pos = this.positionStack.peek();

        Position lPos = Position.create(pos);
        lPos.add(0);
        this.positionStack.push(lPos);

        Formula left = jFormula.getLeft();
        left.apply(this);

        Formula right = jFormula.getRight();
        if (right != null) {
            Position rPos = Position.create(pos);
            rPos.add(1);
            this.positionStack.push(rPos);

            right.apply(this);
        }

        this.positionStack.pop();
        return null;
    }

    @Override
    public Object caseTruthValue(FormulaTruthValue truthvalFormula) {
        this.positionStack.pop();
        return null;
    }

}

/**
 * Inserts the lemma into the formula next to the by position specified
 * equation. Depending of the amount of negations passed it is inserted as a
 * conjunction or its negation is inserted as a disjunction. This way it will be
 * of use during simplification.
 */
class LemmaInsertVisitor implements FineFormulaVisitorException<Formula> {

    Formula lemma;

    Position position;

    Position position_backup;

    boolean and_mode;

    public LemmaInsertVisitor(Formula lemma, Position position, boolean and_mode) {
        this.lemma = lemma;
        this.position = position.deepcopy();
        this.position_backup = position;
        this.and_mode = and_mode;
    }

    private Formula insertInto(Formula formula){
        if (this.and_mode) {
            Formula newFormula = And.create(formula, this.lemma);
            return newFormula;
        }
        else {
            Formula notLemma = Not.create(this.lemma);
            Formula newFormula = Or.create(formula, notLemma);
            return newFormula;
        }
    }

    @Override
    public Formula caseEquation(Equation eqFormula) throws InvalidPositionException {
        // reached
        if (! this.position.isEmpty()) {
            throw new InvalidPositionException(this.position_backup,
                    "The position is not the position of an equation.");
        }

        return this.insertInto(eqFormula);
    }

    @Override
    public Formula caseTruthValue(FormulaTruthValue truthvalFormula) throws InvalidPositionException {
        throw new InvalidPositionException(this.position_backup,
                "The position is not the position of an equation.");
    }

    @Override
    public Formula caseAnd(And andFormula) throws InvalidPositionException {
        if (this.position.isEmpty()) {
            // this may occur when several lemmas are applicable for the same multiplicant
            // and a the first has already been inserted
            // then the position of the equation points to an AND / OR
            // so insert here
            return this.insertInto(andFormula);
        }

        Integer go = this.position.remove(0);

        Formula left = andFormula.getLeft();
        Formula right = andFormula.getRight();

        if (go == 0) {
            Formula newLeft = left.apply(this);

            return And.create(newLeft, right);
        }
        else if (go == 1) {
            Formula newRight = right.apply(this);

            return And.create(left, newRight);
        }

        throw new InvalidPositionException(this.position_backup,
                     "Not a valid position in this formula.");
    }

    /**
     * We must transform equivalences into implications to handle the implicite
     * negation.
     * @throws InvalidPositionException
     */
    @Override
    public Formula caseEquivalence(Equivalence equivFormula) throws InvalidPositionException {
        if (this.position.isEmpty()) {
            throw new InvalidPositionException(this.position_backup,
                        "The position is not the position of an equation.");
        }

        Integer go = this.position.remove(0);

        if (go > 1) {
            throw new InvalidPositionException(this.position_backup,
                        "Not a valid position in this formula.");
        }

        Position position_safe = this.position.deepcopy();

        Formula left = equivFormula.getLeft();
        Formula right = equivFormula.getRight();

        Formula leftImpl = null;

        if (go == 0) {
            if (this.and_mode) {
                this.and_mode = false;
            }
            else {
                this.and_mode = true;
            }
            Formula newLeft = left.apply(this);

            leftImpl = Implication.create(newLeft, right);
        }
        else if (go == 1) {
            Formula newRight = right.apply(this);

            leftImpl = Implication.create(left, newRight);
        }

        this.position = position_safe;

        Formula rightImpl = null;

        if (go == 0) {
            Formula newLeft = left.apply(this);

            rightImpl = Implication.create(right, newLeft);
        }
        else if (go == 1) {
            if (this.and_mode) {
                this.and_mode = false;
            }
            else {
                this.and_mode = true;
            }
            Formula newRight = right.apply(this);

            rightImpl = Implication.create(newRight, left);
        }

        And and = And.create(leftImpl, rightImpl);

        return and;

    }

    @Override
    public Formula caseImplication(Implication implFormula) throws InvalidPositionException {
        if (this.position.isEmpty()) {
            throw new InvalidPositionException(this.position_backup,
                        "The position is not the position of an equation.");
        }

        Integer go = this.position.remove(0);

        Formula left = implFormula.getLeft();
        Formula right = implFormula.getRight();

        if (go == 0) {
            if (this.and_mode) {
                this.and_mode = false;
            }
            else {
                this.and_mode = true;
            }

            Formula newLeft = left.apply(this);

            return Implication.create(newLeft, right);
        }
        else if (go == 1) {
            Formula newRight = right.apply(this);

            return Implication.create(left, newRight);
        }

        throw new InvalidPositionException(this.position_backup,
                    "Not a valid position in this formula.");
    }

    @Override
    public Formula caseNot(Not notFormula) throws InvalidPositionException {
        if (this.position.isEmpty()) {
            throw new InvalidPositionException(this.position_backup,
                        "The position is not the position of an equation.");
        }

        Integer go = this.position.remove(0);

        Formula left = notFormula.getLeft();

        if (go == 0) {
            if (this.and_mode) {
                this.and_mode = false;
            }
            else {
                this.and_mode = true;
            }

            Formula newLeft = left.apply(this);

            return Not.create(newLeft);
        }

        throw new InvalidPositionException(this.position_backup,
                    "Not a valid position in this formula.");
    }

    @Override
    public Formula caseOr(Or orFormula) throws InvalidPositionException {
        if (this.position.isEmpty()) {
            // this may occur when several lemmas are applicable for the same multiplicant
            // and a the first has already been inserted
            // then the position of the equation points to an AND / OR
            // so insert here
            return this.insertInto(orFormula);
        }

        Integer go = this.position.remove(0);

        Formula left = orFormula.getLeft();
        Formula right = orFormula.getRight();

        if (go == 0) {
            Formula newLeft = left.apply(this);

            return Or.create(newLeft, right);
        }
        else if (go == 1) {
            Formula newRight = right.apply(this);

            return Or.create(left, newRight);
        }

        throw new InvalidPositionException(this.position_backup,
                    "Not a valid position in this formula.");
    }

}