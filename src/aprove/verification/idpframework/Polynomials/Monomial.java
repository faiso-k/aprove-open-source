package aprove.verification.idpframework.Polynomials;


import java.util.*;
import java.util.Map.Entry;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.idpframework.Core.*;
import aprove.verification.idpframework.Core.BasicStructures.*;
import aprove.verification.idpframework.Core.SemiRings.*;
import aprove.verification.oldframework.Utility.*;
import immutables.*;

/**
 *
 * @author Martin Pluecker
 */
public class Monomial<C extends SemiRing<C>> implements IDPExportable, XmlExportable {

    static <C extends SemiRing<C>> Monomial<C> create(final C ring, PolyFactory factory) {
        return Monomial.create(ring,
                ImmutableCreator.create(Collections.<PolyVariable<C>, BigInt>emptyMap()),
                factory);
    }

    static <C extends SemiRing<C>> Monomial<C> create(final C ring, ImmutableMap<? extends PolyVariable<C>, BigInt> map,
        final PolyFactory factory) {
        final Map<PolyVariable<C>, BigInt> cleanMap =
            new LinkedHashMap<PolyVariable<C>, BigInt>();

        boolean changedMap = false;
        for (final Map.Entry<? extends PolyVariable<C>, BigInt> entry : map.entrySet()) {
            if (entry.getValue().getBigInt().signum() != 0) {
                boolean booleanVar = false;
                if (!entry.getKey().isMax()) {
                    final IVariable<C> realVar = (IVariable<C>) entry.getKey();
                    booleanVar = realVar.getDomain().isBooleanRange();
                }

                if (booleanVar) {
                    cleanMap.put(entry.getKey(), BigInt.ONE);
                    changedMap = true;
                } else {
                    cleanMap.put(entry.getKey(), entry.getValue());
                }
            } else {
                changedMap = true;
            }
        }

        if (changedMap) {
            map = ImmutableCreator.create(cleanMap);
        }

        return new Monomial<C>(ring, map, factory);
    }

    private final C ring;
    private final ImmutableMap<? extends PolyVariable<C>, BigInt> map;
    private final int hash;
    private final PolyFactory factory;

    private volatile ImmutableSet<IVariable<C>> variables;
    private volatile ImmutableSet<PolyMaxVariable<C>> maxVariables;

    private Monomial(final C ring, final ImmutableMap<? extends PolyVariable<C>, BigInt> map,
            final PolyFactory factory) {
        this.ring = ring;
        this.map = map;
        this.hash = map.hashCode();
        this.factory = factory;
    }

    public ImmutableSet<? extends IVariable<C>> getVariables() {
        if (this.variables == null) {
            synchronized (this) {
                if (this.variables == null) {
                    final Set<IVariable<C>> res =
                        new LinkedHashSet<IVariable<C>>();

                    for (final PolyVariable<C> variable : this.map.keySet()) {
                        if (!variable.isMax()) {
                            res.add((IVariable<C>) variable);
                        } else {
                            final PolyMaxVariable<C> maxVar = (PolyMaxVariable<C>) variable;
                            res.addAll(maxVar.getVariables());
                        }
                    }

                    return this.variables = ImmutableCreator.create(res);
                }
            }
        }
        return this.variables;
    }

    public Set<PolyMaxVariable<C>> getMaxVariables() {
        if (this.maxVariables == null) {
            synchronized (this) {
                if (this.maxVariables == null) {
                    final Set<PolyMaxVariable<C>> res =
                        new LinkedHashSet<PolyMaxVariable<C>>();

                    for (final PolyVariable<C> variable : this.map.keySet()) {
                        if (variable.isMax()) {
                            res.add((PolyMaxVariable<C>) variable);
                        }
                    }

                    return this.maxVariables = ImmutableCreator.create(res);
                }
            }
        }
        return this.maxVariables;
    }

    public boolean isConstantPart() {
        return this.map.isEmpty();
    }

    public boolean isVariable() {
        if (this.map.size() == 1) {
            final Entry<? extends PolyVariable<C>, BigInt> entry = this.map.entrySet().iterator().next();
            return entry.getValue().isOne();
        }
        return false;
    }

    public PolyVariable<C> getVariable() {
        if (this.map.size() == 1) {
            final Entry<? extends PolyVariable<C>, BigInt> entry = this.map.entrySet().iterator().next();
            if (entry.getValue().isOne()) {
                return entry.getKey();
            }
        }
        throw new UnsupportedOperationException("not a real variable: " + this);
    }

    public boolean isRealVariable() {
        if (this.map.size() == 1) {
            final Entry<? extends PolyVariable<C>, BigInt> entry = this.map.entrySet().iterator().next();
            return entry.getValue().isOne() && !entry.getKey().isMax();
        }
        return false;
    }

    public IVariable<C> getRealVariable() {
        if (this.map.size() == 1) {
            final Entry<? extends PolyVariable<C>, BigInt> entry = this.map.entrySet().iterator().next();
            if (entry.getValue().isOne() && !entry.getKey().isMax()) {
                return (IVariable<C>) entry.getKey();
            }
        }
        throw new UnsupportedOperationException("not a real variable: " + this);
    }

    public ImmutableMap<? extends PolyVariable<C>, BigInt> getExponents() {
        return this.map;
    }

    public Monomial<C> mult(final Monomial<C> m) {
        final Map<PolyVariable<C>, BigInt> newMonomial =
            new LinkedHashMap<PolyVariable<C>, BigInt>(this.map);
        for (final Map.Entry<? extends PolyVariable<C>, BigInt> mon : m.map.entrySet()) {
            final BigInt exp = newMonomial.get(mon.getKey());
            if (exp != null) {
                final BigInt newExp =
                    BigInt.create(exp.getBigInt().add(
                        mon.getValue().getBigInt()));
                if (newExp.getBigInt().signum() != 0) {
                    newMonomial.put(mon.getKey(), newExp);
                }
            } else {
                newMonomial.put(mon.getKey(), mon.getValue());
            }
        }
        return this.factory.createMonomial(this.ring, ImmutableCreator.create(newMonomial));
    }

    public Monomial<C> div(final Monomial<C> m) {
        final Map<PolyVariable<C>, BigInt> newMonomial =
            new LinkedHashMap<PolyVariable<C>, BigInt>(this.map);
        for (final Map.Entry<? extends PolyVariable<C>, BigInt> mon : m.map.entrySet()) {
            final BigInt exp = newMonomial.get(mon.getKey());
            if (exp != null) {
                final BigInt newExp =
                    BigInt.create(exp.getBigInt().subtract(
                        mon.getValue().getBigInt()));
                if (newExp.getBigInt().signum() != 0) {
                    newMonomial.put(mon.getKey(), newExp);
                }
            } else {
                newMonomial.put(mon.getKey(),
                    BigInt.create(mon.getValue().getBigInt().negate()));
            }
        }
        return this.factory.createMonomial(this.ring, ImmutableCreator.create(newMonomial));
    }

    public Monomial<C> removeVar(final PolyVariable<C> var) {
        if (this.map.containsKey(var)) {
            final Map<PolyVariable<C>, BigInt> newMonomial =
                new LinkedHashMap<PolyVariable<C>, BigInt>(this.map);
            newMonomial.remove(var);
            return this.factory.createMonomial(this.ring, ImmutableCreator.create(newMonomial));
        } else {
            return this;
        }
    }

    public Monomial<C> changeExp(final PolyVariable<C> var, final BigInt exp) {
        if (this.map.containsKey(var)) {
            final Map<PolyVariable<C>, BigInt> newMonomial =
                new LinkedHashMap<PolyVariable<C>, BigInt>(this.map);
            newMonomial.remove(var);
            return this.factory.createMonomial(this.ring, ImmutableCreator.create(newMonomial));
        } else {
            return this;
        }
    }

    @Override
    public final String toString() {
        return this.export(new PLAIN_Util());
    }

    @Override
    public final String export(final Export_Util o) {
        return this.export(o, IDPExportable.DEFAULT_LEVEL);
    }

    @Override
    public final String export(final Export_Util o,
        final VerbosityLevel verbosityLevel) {
        final StringBuilder sb = new StringBuilder();
        this.export(sb, o, verbosityLevel);
        return sb.toString();
    }

    @Override
    public void export(final StringBuilder sb,
        final Export_Util o,
        final VerbosityLevel verbosityLevel) {
        final Iterator<? extends Map.Entry<? extends PolyVariable<C>, BigInt>> variables = this.map.entrySet().iterator();
        while (variables.hasNext()) {
            final Map.Entry<? extends PolyVariable<C>, BigInt> variable = variables.next();
            variable.getKey().export(sb, o, verbosityLevel);
            if (!variable.getValue().equals(BigInt.ONE)) {
                sb.append(o.sup(variable.getValue().export(o)));
            }

            if (variables.hasNext()) {
                sb.append(" ");
                sb.append(o.multSign());
                sb.append(" ");
            }
        }
    }

    @Override
    public Map<String, String> getXmlAttribs(XmlExporter xe) {
        return null;
    }

    @Override
    public XmlContentsMap getXmlContents(XmlExporter xe) {
        XmlContentsMap contents = new XmlContentsMap();

        int id = 0;

        for (final Map.Entry<? extends PolyVariable<C>, BigInt> variable : this.map.entrySet()) {
            contents.add("var", "id", Integer.toString(id), variable.getKey());
            contents.add("exp", "id", Integer.toString(id), variable.getValue());

            id++;
        }
        return contents;
    }

    @Override
    public int hashCode() {
        return this.hash;
    }

    @Override
    public boolean equals(final Object obj) {
        if (this == obj) {
            return true;
        }
        if (obj == null) {
            return false;
        }
        if (this.getClass() != obj.getClass()) {
            return false;
        }
        final Monomial<C> other = (Monomial<C>) obj;
        return this.map.equals(other.map);
    }

}
