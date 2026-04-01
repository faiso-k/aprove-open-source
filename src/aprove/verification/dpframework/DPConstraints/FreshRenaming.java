package aprove.verification.dpframework.DPConstraints;

import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;

public class FreshRenaming implements Substitution {

    private final InfRuleContext irc;

    private final Map<TRSVariable, TRSVariable> map;

    public FreshRenaming(InfRuleContext ircParam) {
        super();
        this.irc = ircParam;
        this.map = new LinkedHashMap<TRSVariable, TRSVariable>();
    }

    public FreshRenaming(InfRuleContext ircParam, Map<TRSVariable, TRSVariable> mapParam) {
        super();
        this.irc = ircParam;
        this.map = new LinkedHashMap<>(mapParam);
    }

    public Set<TRSVariable> getCurrentCodomain() {
        return new LinkedHashSet<TRSVariable>(this.map.values());
    }

    @Override
    public TRSTerm substitute(Variable v) {
        TRSVariable nv = this.map.get(v);
        if (nv == null) {
            nv = this.irc.getFreshVariable();
            this.map.put((TRSVariable)v, nv);
        }
        return nv;
    }

}
