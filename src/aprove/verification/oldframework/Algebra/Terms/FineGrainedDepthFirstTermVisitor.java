package aprove.verification.oldframework.Algebra.Terms;


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

public abstract class FineGrainedDepthFirstTermVisitor<T> implements FineGrainedTermVisitor<T> {

    public void defaultIn(AlgebraTerm t) {
    }

    public void defaultOut(AlgebraTerm t) {
    }

    public void inConstructorApp(ConstructorApp cterm) {
        this.defaultIn(cterm);
    }

    public void outConstructorApp(ConstructorApp cterm) {
        this.defaultOut(cterm);
    }

    @Override
    public T caseConstructorApp(ConstructorApp cterm ) {
        this.inConstructorApp(cterm);
        for(AlgebraTerm term : cterm.getArguments()) {
            term.apply(this);
        }
        this.outConstructorApp(cterm);
        return null;
    }

    public void inDefFunctionApp(DefFunctionApp fterm) {
        this.defaultIn(fterm);
    }

    public void outDefFunctionApp(DefFunctionApp fterm) {
        this.defaultOut(fterm);
    }

    public void inMetaFunctionApp(MetaFunctionApplication metaFunctionApplication) {
        this.defaultIn(metaFunctionApplication);
    }

    public void outMetaFunctionApp(MetaFunctionApplication metaFunctionApplication) {
        this.defaultOut(metaFunctionApplication);
    }

    @Override
    public T caseDefFunctionApp(DefFunctionApp fterm) {
        this.inDefFunctionApp(fterm);
        for(AlgebraTerm term : fterm.getArguments()) {
            term.apply(this);
        }
        this.outDefFunctionApp(fterm);
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

    @Override
    public T caseMetaFunctionApplication(MetaFunctionApplication metaFunctionApplication) {
        this.inMetaFunctionApp(metaFunctionApplication);
        for(AlgebraTerm term : metaFunctionApplication.getArguments()) {
            term.apply(this);
        }
        this.outMetaFunctionApp(metaFunctionApplication);
        return null;
    }


}
