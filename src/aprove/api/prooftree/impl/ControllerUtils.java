package aprove.api.prooftree.impl;

import java.util.*;

import aprove.prooftree.Obligations.*;

public enum ControllerUtils {
    ;

    public static List<BasicObligationNode> collectBasicObligationNodes(ObligationNode node) {
        if (node instanceof BasicObligationNode) {
            return Collections.singletonList((BasicObligationNode) node);
        } else {
            JunctorObligationNode junctor = (JunctorObligationNode) node;
            List<BasicObligationNode> result = new ArrayList<BasicObligationNode>();
            for (ObligationNode child : junctor.getChildren()) {
                result.addAll(collectBasicObligationNodes(child));
            }
            return result;
        }
    }
}
