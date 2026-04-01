package aprove.verification.theoremprover.Simplifier;

import java.util.*;
import java.util.logging.*;

import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.SimplifierProblem.*;
import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Syntax.*;
import aprove.verification.oldframework.Typing.*;

@NoParams
public class SymbolicSimplifier extends SimplifierProcessor {

    protected static final int RWLABELLIMIT = 3;
    protected static final int RWITERLIMIT = 500;
    protected static final int RWDEPTHLIMIT = 100;
    protected static final int RWSIZELIMIT = 1000;

    public SimplifierObligation obl;

    /* Symbolic Evaluation (Transformation) */

     public SymbolicSimplifier() {
        super("Symbolic Simplifier", "SE", "Symbolic Evaluation");
    }

    @Override
    public SimplifierObligation simplify(final SimplifierObligation oobl) {
        this.obl = oobl.shallowcopy();
        final Vector<DefFunctionSymbol> vor = new Vector<DefFunctionSymbol>();
    SimplifierProcessor.log.log(Level.FINER, "Simplifier: Performing symbolic evaluation.\n");
        final Iterator it = (new Vector(this.obl.defs)).iterator();
        while (it.hasNext()) {
            final DefFunctionSymbol fsym = (DefFunctionSymbol) it.next();
            final int sig = fsym.getSignatureClass();
            if (sig == Symbol.MAINSIG || sig == Symbol.DEFAULTSIG) {
                if (this.obl.symbolicEvaluation(fsym)) {
                    vor.add(fsym);
                }
        }
        }
        if (vor.isEmpty()) {
            return null;
        }
        this.setProof(new SymbolicProof(oobl, vor, this.obl));
        return this.obl;
    }



    /**
     * Takes the first occurence of a projection not at root position (found in
     * leftmost-outermost fashion) in <b>term</b> and lifts it to the top
     * @param term Term in which projections shall be lifted
     * @return the new term with the projection as root function
     */
    public AlgebraTerm liftProjection(final AlgebraTerm term) {
    if (term.isVariable()) {
            return null;
        }
        final SyntacticFunctionSymbol fsym = (SyntacticFunctionSymbol) term.getSymbol();
        final Position epsilon = Position.create();
        this.obl.isProjection(term.getSymbol());
        final Iterator it = term.getPositions().iterator();
        while (it.hasNext()) {
            final Position p = (Position) it.next();
            if (p.equals(epsilon)) {
                continue;
            }
            final AlgebraTerm t = term.getSubterm(p);

            if (this.obl.isProjection(t.getSymbol())) {
                try {
                    final SyntacticFunctionSymbol oldproj =
                        (SyntacticFunctionSymbol) t.getSymbol();
                    AlgebraTerm newterm = term.replaceAt(t.getArgument(0), p);
                    final int arity = oldproj.getArity();
                    final Vector<AlgebraTerm> types = new Vector<AlgebraTerm>();
                    final Vector<AlgebraTerm> args = new Vector<AlgebraTerm>();

                    final AlgebraTerm fTypeMatrix =
                        this.obl.typeContext.getSingleTypeOf(fsym).getTypeMatrix();
                    final AlgebraTerm oldProjTypeMatrix =
                        this.obl.typeContext.getSingleTypeOf(oldproj).getTypeMatrix();
                    // result Type is result Type of fsym
                    types.add(TypeTools.getResultTerm(fTypeMatrix));

            args.add(newterm);
                    for (int i = 1; i < arity; i++) {
                        types.add(TypeTools.getFunctionArgAt(oldProjTypeMatrix,
                            i));
                        args.add(t.getArgument(i));
                    }

            final SyntacticFunctionSymbol newprojTyped =
                        this.obl.getProjectionTyped(types);
                    newterm = AlgebraFunctionApplication.create(newprojTyped, args);
                    return newterm;
                } catch (final Exception e) {
                }
            }
        }
        return null;
    }

    /**
     * Returns the term that one would get by merging two nested projections. If
     * there is no projection with a nested projection, null is returned.
     */
    public AlgebraTerm mergeProjections(final AlgebraTerm term) {
    if (term.isVariable()) {
            return null;
        }
        final SyntacticFunctionSymbol proj = (SyntacticFunctionSymbol) term.getSymbol();
        if (proj.getArity() < 2 || !this.obl.isProjection(proj)) {
            return null;
        }
        final AlgebraTerm p = term.getArgument(0);
        if (!this.obl.isProjection(p.getSymbol())) {
            return null;
        }

        final AlgebraTerm termTypeM =
            this.obl.typeContext.getSingleTypeOf(term.getSymbol()).getTypeMatrix();
        final AlgebraTerm pTypeM =
            this.obl.typeContext.getSingleTypeOf(p.getSymbol()).getTypeMatrix();

    final List<AlgebraTerm> projargs1 = p.getArguments();
        final List<AlgebraTerm> projargs1Types = TypeTools.getFunctionArgs(pTypeM);

    final AlgebraTerm t = projargs1.remove(0);
        final AlgebraTerm tType = projargs1Types.remove(0);

    final List<AlgebraTerm> projargs2 = term.getArguments();
        final List<AlgebraTerm> projargs2Types = TypeTools.getFunctionArgs(termTypeM);

    projargs2.remove(0);
        projargs2Types.remove(0);
        projargs1.addAll(projargs2);
        projargs1Types.addAll(projargs2Types);
        return this.obl.makeProjectionTyped(t, tType, projargs1, projargs1Types);
    }

    /**
     * Returns the term that one would get by deleting the projection in the
     * given term if at the given position there is a projection with just one
     * argument, null otherwise.
     */
    public AlgebraTerm eliminateProjection(final AlgebraTerm term) {
    if (term.isVariable()) {
            return null;
        }
        final SyntacticFunctionSymbol proj = (SyntacticFunctionSymbol) term.getSymbol();
        if (!(proj.getArity() == 1 && this.obl.isProjection(proj))) {
            return null;
        }
        return term.getArgument(0);
    }

    /**
     * Return the rule that one would get by replacing all of the arguments,
     * which root-symbol is a total-function, of the projection.
     */
    public AlgebraTerm replaceArguments(final AlgebraTerm term) {
    boolean changed = false;
        if (!this.obl.isProjection(term.getSymbol())) {
            return null;
        }

        final AlgebraTerm termTypeM =
            this.obl.typeContext.getSingleTypeOf(term.getSymbol()).getTypeMatrix();

        final Vector<AlgebraTerm> args = new Vector<AlgebraTerm>();
        final Vector<AlgebraTerm> argTypes = new Vector<AlgebraTerm>();

        final Iterator it = term.getArguments().iterator();
        final AlgebraTerm t = (AlgebraTerm) it.next();

        final List<AlgebraTerm> termArgTypes = TypeTools.getFunctionArgs(termTypeM);
        final Iterator<AlgebraTerm> it_argType = termArgTypes.iterator();

        // the first type is also the return type
        final AlgebraTerm tTypeM = it_argType.next();

        while (it.hasNext()) {
            final AlgebraTerm p = (AlgebraTerm) it.next();
            final AlgebraTerm pType = it_argType.next();
            final Symbol sym = p.getSymbol();
            if (sym instanceof VariableSymbol) {
                changed = true;
            } else if (!SimplifierObligation.isTotal(sym)
                || this.obl.isProjection(sym)) {
                args.add(p);
                argTypes.add(pType);
            } else {
                changed = true;
                args.addAll(p.getArguments());
                // p cannot be a variable, because of the if(sym...) statement
                // above => there is a type for p.getSymbol()
                argTypes.addAll(TypeTools.getFunctionArgs(this.obl.typeContext.getSingleTypeOf(
                    p.getSymbol()).getTypeMatrix()));
            }
        }
        if (changed) {
            final AlgebraTerm newProj =
                this.obl.makeProjectionTyped(t, tTypeM, args, argTypes);
            return newProj;
        }
        return null;
    }

}
