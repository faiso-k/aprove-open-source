package aprove.verification.dpframework.Orders ;

import aprove.strategies.Abortions.*;

/**
 *   Interface for orders between Ts.
 *
 *   @author Peter Schneider-Kamp
 *   @version $Id$
 */
public interface Order<T> {

    public boolean inRelation(T s, T t) throws AbortionException;

    public boolean solves(Constraint<T> c) throws AbortionException;

    public boolean areEquivalent(T s, T t) throws AbortionException;

}
