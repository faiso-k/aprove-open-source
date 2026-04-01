package aprove.verification.oldframework.Algebra.Terms;

import java.util.*;

/** This abstract implementation uses depth first recursion as a default.
 *  Extending classes should override at least one of the inXXX / outXXX / caseXXX /
 *  defaultXXX methods.
 *  <p>
 *  The standard behavior of this visitor is to branch into all subterms in a depth first fashion.
 *  Actions that are to be carried out when entering or leaving a node should be implemented via
 *  the inXXX and outXXX methods. The standard implementations of these call the defaultXXX methods
 *  that can be overriden to enforce different default operations on entering and/or leaving nodes.
 *  The caseXXX methods should only be overridden if the descent behavior of the visitor has to be
 *  altered.
 *  @author Peter Schneider-Kamp
 *  @version $Id$
 */

public abstract class CoarseGrainedDepthFirstTermVisitor<T> implements CoarseGrainedTermVisitor<T> {

    public void defaultIn(AlgebraTerm t) {
    }

    public void defaultOut(AlgebraTerm t) {
    }

    public void inFunctionApp(AlgebraFunctionApplication f) {
    this.defaultIn(f);
    }

    public void outFunctionApp(AlgebraFunctionApplication f) {
    this.defaultOut(f);
    }

    @Override
    public T caseFunctionApp(AlgebraFunctionApplication f) {
    this.inFunctionApp(f);
    Iterator i = f.getArguments().iterator();
    while (i.hasNext()) {
        ((AlgebraTerm)i.next()).apply(this);
    }
    this.outFunctionApp(f);
    return null;
    }

    public void inVariable(AlgebraVariable v) {
    this.defaultIn(v);
    }

    public void outVariable(AlgebraVariable v) {
    this.defaultOut(v);
    }

    @Override
    public T caseVariable(AlgebraVariable v) {
    this.inVariable(v);
    this.outVariable(v);
    return null;
    }

}
