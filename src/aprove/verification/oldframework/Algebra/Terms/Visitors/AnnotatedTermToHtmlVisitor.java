/*
 * Created on Oct 10, 2004
 */
package aprove.verification.oldframework.Algebra.Terms.Visitors;

import java.util.*;

import aprove.verification.oldframework.Algebra.Terms.*;

/**
 * @author rabe
 */
public class AnnotatedTermToHtmlVisitor implements CoarseGrainedTermVisitor {

    protected Set<Position> annotations;

    protected StringBuffer   returnValue;


    public static String apply(AlgebraTerm term, Set<Position> annotations) {
        return ((StringBuffer)term.apply(new AnnotatedTermToHtmlVisitor(annotations))).toString();
    }

    /**
     *
     */
    public AnnotatedTermToHtmlVisitor(Set<Position> annotations) {
        this.annotations = annotations;
        this.returnValue = new StringBuffer();
    }

    /* (non-Javadoc)
     * @see aprove.verification.oldframework.Algebra.Terms.CoarseGrainedTermVisitor#caseFunctionApp(aprove.verification.oldframework.Algebra.Terms.FunctionApplication)
     */
    @Override
    public Object caseFunctionApp(AlgebraFunctionApplication f) {

        this.returnValue.append(f.toHTML());

        Iterator iterator = f.getArguments().iterator();

        while( iterator.hasNext() ) {
            ((AlgebraTerm)iterator.next()).apply(this);
        }

        return this.returnValue;
    }

    /* (non-Javadoc)
     * @see aprove.verification.oldframework.Algebra.Terms.CoarseGrainedTermVisitor#caseVariable(aprove.verification.oldframework.Algebra.Terms.Variable)
     */
    @Override
    public Object caseVariable(AlgebraVariable v) {
        return this.returnValue.append(v.toHTML());
    }
}
