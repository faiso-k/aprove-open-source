package aprove.verification.idpframework.Core.IDPGraph;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import immutables.*;

/**
 * @author Martin Pluecker
 */
public enum EdgeType implements Exportable {

    INF(false, true),
    @Deprecated
    REWRITE_INF(true, true),
    REWRITE(true, false),
    NO_EDGE(false, false);

    public static final ImmutableSet<EdgeType> REWRITE_EDGE_TYPES;
    static {
        final Set<EdgeType> types = new LinkedHashSet<EdgeType>();
        types.add(REWRITE_INF);
        types.add(REWRITE);
        REWRITE_EDGE_TYPES = ImmutableCreator.create(types);
    };

    public static final ImmutableSet<EdgeType> INF_EDGE_TYPES;
    static {
        final Set<EdgeType> types = new LinkedHashSet<EdgeType>();
        types.add(REWRITE_INF);
        types.add(INF);
        INF_EDGE_TYPES = ImmutableCreator.create(types);
    };

    public static EdgeType getType(final boolean rewrite, final boolean inf) {
        if (rewrite) {
            if (inf) {
                return REWRITE_INF;
            } else {
                return REWRITE;
            }
        } else if (inf) {
            return INF;
        } else {
            return NO_EDGE;
        }
    }

    private final boolean rewrite;
    private final boolean inf;
    private volatile ImmutableSet<EdgeType> subTypes;

    private EdgeType(final boolean rewrite, final boolean inf) {
        this.rewrite = rewrite;
        this.inf = inf;
    }

    public boolean isRewrite() {
        return this.rewrite;
    }

    public boolean isInf() {
        return this.inf;
    }

    @Override
    public final String export(final Export_Util o) {
        return this.name();
    }

    public EdgeType subtractType(final boolean rewrite,
            final boolean inf) {
        return EdgeType.getType(this.rewrite && !rewrite, this.inf && !inf);
    }

    public EdgeType subtractType(final EdgeType type) {
        return this.subtractType(type.isRewrite(), type.isInf());
    }

    public EdgeType addType(final boolean rewrite,
        final boolean inf) {
        return EdgeType.getType(this.rewrite || rewrite, this.inf || inf);
    }

    public EdgeType addType(final EdgeType type) {
        return this.addType(type.isRewrite(), type.isInf());
    }

    public boolean isSubType(final EdgeType type) {
        return (this.isRewrite() || !type.isRewrite())
            && (this.isInf() || !type.isInf());
    }

    public boolean isDisjoint(final EdgeType type) {
        return (!this.isRewrite() || !type.isRewrite())
        && (!this.isInf() || !type.isInf());
    }

    public ImmutableSet<EdgeType> getSubTypes() {
        if (this.subTypes == null) {
            synchronized(this) {
                if (this.subTypes == null) {
                    final LinkedHashSet<EdgeType> st = new LinkedHashSet<EdgeType>();
                    for (final EdgeType et : EdgeType.values()) {
                        if (this.isSubType(et)) {
                            st.add(et);
                        }
                    }
                    this.subTypes = ImmutableCreator.create(st);
                }
            }
        }

        return this.subTypes;
    }
}
