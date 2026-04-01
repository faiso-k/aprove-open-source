package aprove.verification.dpframework.Orders.Solvers;

import java.util.*;
import java.util.logging.*;

import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.Orders.*;

/** Constraint solver that uses the Embedding order.
 *  <p>
 *  Very weak!
 *
 * @author Stephan Falke
 * @version $Id$
 */

public class EMBSolver implements AbortableConstraintSolver<TRSTerm>, ProvidesCriticalConstraint<TRSTerm> {

    final static Logger log = Logger.getLogger("aprove.verification.dpframework.Orders.Solvers.EMBSolver");

    private Constraint<TRSTerm> crit;
    private EMB emb;

    /* constructors */
    private EMBSolver() {
        this.emb = EMB.create();
    }

    /** Creates a new instance of <code>EMBSolver</code>.
     */
    public static EMBSolver create() {
        return new EMBSolver();
    }

    @Override
    public ExportableOrder<TRSTerm> solve(Collection<Constraint<TRSTerm>> cs, Abortion aborter) {
        for (Constraint<TRSTerm> c : cs) {
            EMBSolver.log.log(Level.FINE,"EMBSolver: now solving {0}\n",c);
            if (!this.emb.solves(c)) {
                this.crit = c;
                return null;
            }
        }
        return this.emb;
    }

    @Override
    public Constraint<TRSTerm> getCriticalConstraint() {
        return this.crit;
    }

}
