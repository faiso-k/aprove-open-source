/*
 * Created on Dec 6, 2004
 */
package aprove.verification.oldframework.Algebra.Terms;

import java.util.*;

import aprove.verification.oldframework.Exceptions.*;
import aprove.verification.oldframework.LemmaDatabase.Index.*;

/**
 * @author rabe
 */
public interface TermOrFormula {

    public List<? extends TermOrFormula> getArguments();

    public TermOrFormula getSubPart(Position p) throws InvalidPositionException;

    public IndexSymbol   getRootIndexSymbol();

    public boolean isTerm();

    public boolean isFormula();

}
