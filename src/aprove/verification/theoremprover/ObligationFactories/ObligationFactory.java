package aprove.verification.theoremprover.ObligationFactories;

import java.util.*;

import aprove.prooftree.Obligations.*;
import aprove.verification.oldframework.Input.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;


public interface ObligationFactory {
    public Pair<ObligationNode, List<BasicObligationNode>> getRootAndPositions(AnnotatedInput annotatedInput);
    public void clearResult(AnnotatedInput annotatedInput);
}
