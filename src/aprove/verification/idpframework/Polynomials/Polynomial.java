package aprove.verification.idpframework.Polynomials;

import java.math.*;
import java.util.*;
import java.util.Map.Entry;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.idpframework.Core.*;
import aprove.verification.idpframework.Core.BasicStructures.*;
import aprove.verification.idpframework.Core.BasicStructures.Substitutions.*;
import aprove.verification.idpframework.Core.PredefinedFunctions.*;
import aprove.verification.idpframework.Core.PredefinedFunctions.Domains.*;
import aprove.verification.idpframework.Core.PredefinedFunctions.PredefinedFunction.*;
import aprove.verification.idpframework.Core.SemiRings.*;
import aprove.verification.idpframework.Core.Utility.*;
import aprove.verification.oldframework.Utility.*;
import immutables.*;

/**
 * @author Martin Pluecker
 */
public class Polynomial<C extends SemiRing<C>> extends IDPExportable.IDPExportableSkeleton implements Immutable,
        SemiRing<Polynomial<C>>, IDPExportable, HasVariables<IVariable<C>>, HasDomain {

    private final ImmutableMap<Monomial<C>, C> monomials;
    private final int hash;
    private final PolyFactory factory;

    private volatile ImmutableSet<IVariable<C>> variables;
    private volatile ImmutableSet<PolyMaxVariable<C>> maxVariables;
    private final C ring;

    static <C extends SemiRing<C>> Polynomial<C> create(ImmutableMap<Monomial<C>, C> monomials,
        final PolyFactory factory, final C ring) {
        if (monomials.values().contains(ring.zero())) {
            final Map<Monomial<C>, C> cleanMap =
                new LinkedHashMap<Monomial<C>, C>();
            for (final Map.Entry<Monomial<C>, C> entry : monomials.entrySet()) {
                if (!entry.getValue().isZero()) {
                    cleanMap.put(entry.getKey(), entry.getValue());
                }
            }
            monomials = ImmutableCreator.create(cleanMap);
        }
        return new Polynomial<C>(monomials, factory, ring);
    }

    private Polynomial(final ImmutableMap<Monomial<C>, C> monomials,
            final PolyFactory factory, final C ring) {
        this.monomials = monomials;
        this.factory = factory;
        this.ring = ring;
        {
            final int prime = 31;
            int result = 1;
            result =
                prime * result
                    + monomials.hashCode();
            this.hash = result;
        }
    }

    @Override
    public boolean isZero() {
        return this.monomials.isEmpty();
    }

    @Override
    public boolean isOne() {
        return this.equals(this.factory.one(this.ring));
    }

    public boolean isConstant() {
        return this.isZero() || this.monomials.size() == 1 && this.monomials.keySet().iterator().next().isConstantPart();
    }

    public Polynomial<C> getConstantPart() {
        for (final Map.Entry<Monomial<C>, C> monomialCoeff : this.monomials.entrySet()) {
            if (monomialCoeff.getKey().isConstantPart()) {
                return this.factory.create(monomialCoeff.getValue());
            }
        }
        return this.zero();
    }

    public C getConstantValue() {
        if (this.monomials.size() == 1) {
            final Entry<Monomial<C>, C> monomialEnry = this.monomials.entrySet().iterator().next();
            if (monomialEnry.getKey().isConstantPart()) {
                return monomialEnry.getValue();
            }
        } else if (this.monomials.isEmpty()) {
            return this.ring.zero();
        }
        throw new UnsupportedOperationException("not a constant polynomial: " + this);
    }


    public boolean isRealVariable() {
        if (this.monomials.size() == 1) {
            final Entry<Monomial<C>, C> monomialEnry = this.monomials.entrySet().iterator().next();
            return monomialEnry.getValue().isOne() && monomialEnry.getKey().isRealVariable();
        }
        return false;
    }

    public IVariable<C> getRealVariable() {
        if (this.monomials.size() == 1) {
            final Entry<Monomial<C>, C> monomialEnry = this.monomials.entrySet().iterator().next();
            if (monomialEnry.getValue().isOne() && monomialEnry.getKey().isRealVariable()) {
                return monomialEnry.getKey().getRealVariable();
            }
        }
        throw new UnsupportedOperationException("not a real variable: " + this);
    }

    public ImmutableMap<Monomial<C>, C> getMonomials() {
        return this.monomials;
    }

    public Polynomial<C> add(final Collection<Polynomial<C>> ps) {
        Polynomial<C> result = this;
        for (final Polynomial<C> p : ps) {
            result = result.add(p);
        }
        return result;
    }

    @Override
    public Polynomial<C> add(final Polynomial<C> p) {
        if (p.isZero()) {
            return this;
        }
        if (this.isZero()) {
            return p;
        }

        final Map<Monomial<C>, C> newMonomials =
            new LinkedHashMap<Monomial<C>, C>(this.monomials);
        for (final Map.Entry<Monomial<C>, C> monom : p.monomials.entrySet()) {
            final C old = newMonomials.get(monom.getKey());
            if (old != null) {
                final C c = old.add(monom.getValue());
                if (!c.isZero()) {
                    newMonomials.put(monom.getKey(), c);
                } else {
                    newMonomials.remove(monom.getKey());
                }
            } else {
                newMonomials.put(monom.getKey(), monom.getValue());
            }
        }
        return this.factory.create(this.ring, ImmutableCreator.create(newMonomials));
    }

    @Override
    public Polynomial<C> subtract(final Polynomial<C> p) {
        if (p.isZero()) {
            return this;
        }
        final Map<Monomial<C>, C> newMonomials =
            new LinkedHashMap<Monomial<C>, C>(this.monomials);
        for (final Map.Entry<Monomial<C>, C> monom : p.monomials.entrySet()) {
            final C old = newMonomials.get(monom.getKey());
            if (old != null) {
                final C c = old.subtract(monom.getValue());
                if (!c.isZero()) {
                    newMonomials.put(monom.getKey(), c);
                } else {
                    newMonomials.remove(monom.getKey());
                }
            } else {
                newMonomials.put(monom.getKey(), monom.getValue().negate());
            }
        }
        return this.factory.create(this.ring, ImmutableCreator.create(newMonomials));
    }

    @Override
    public Polynomial<C> mult(final Polynomial<C> p) {
        if (p.isZero()) {
            return this.zero();
        }
        if (p.isZero()) {
            return this;
        }
        if (this.isOne()) {
            return p;
        }

        final Map<Monomial<C>, C> newMonomials =
            new LinkedHashMap<Monomial<C>, C>(this.monomials.size()
                * p.monomials.size());

        for (final Map.Entry<Monomial<C>, C> monom : this.monomials.entrySet()) {
            for (final Map.Entry<Monomial<C>, C> pMonom : p.monomials.entrySet()) {
                final Monomial<C> newMon =
                    monom.getKey().mult(pMonom.getKey());
                C newC = monom.getValue().mult(pMonom.getValue());
                final C c = newMonomials.get(newMon);
                if (c != null) {
                    newC = c.add(newC);
                    if (!newC.isZero()) {
                        newMonomials.put(newMon, newC);
                    } else {
                        newMonomials.remove(newMon);
                    }
                } else {
                    newMonomials.put(newMon, newC);
                }
            }
        }
        return this.factory.create(this.ring, ImmutableCreator.create(newMonomials));
    }

    @Override
    public Polynomial<C> negate() {
        final Map<Monomial<C>, C> newMonomials =
            new LinkedHashMap<Monomial<C>, C>();
        for (final Map.Entry<Monomial<C>, C> monom : this.monomials.entrySet()) {
            newMonomials.put(monom.getKey(), monom.getValue().negate());
        }
        return this.factory.create(this.ring, ImmutableCreator.create(newMonomials));
    }

    @Override
    public ImmutableSet<IVariable<C>> getVariables() {
        if (this.variables == null) {
            synchronized (this) {
                if (this.variables == null) {
                    final Set<IVariable<C>> res =
                        new LinkedHashSet<IVariable<C>>();
                    for (final Map.Entry<Monomial<C>, C> monom : this.monomials.entrySet()) {
                        res.addAll(monom.getKey().getVariables());
                    }
                    return this.variables = ImmutableCreator.create(res);
                }
            }
        }
        return this.variables;
    }

    public ImmutableSet<PolyMaxVariable<C>> getMaxVariables() {
        if (this.maxVariables == null) {
            synchronized (this) {
                if (this.maxVariables == null) {
                    final Set<PolyMaxVariable<C>> res =
                        new LinkedHashSet<PolyMaxVariable<C>>();

                    for (final Map.Entry<Monomial<C>, C> monom : this.monomials.entrySet()) {
                        res.addAll(monom.getKey().getMaxVariables());
                    }
                    return this.maxVariables = ImmutableCreator.create(res);
                }
            }
        }
        return this.maxVariables;
    }

    public Polynomial<C> applyVarSubstitution(final Map<IVariable<C>, C> sigma) {

        boolean changedMonomials = false;
        Polynomial<C> res = this.factory.zero(this.ring);

        for (final Map.Entry<Monomial<C>, C> monom : this.monomials.entrySet()) {
            final Map<PolyVariable<C>, BigInt> newMonomMap =
                new LinkedHashMap<PolyVariable<C>, BigInt>();
            boolean changedMonom = false;
            C newCoeff = monom.getValue();
            for (final Map.Entry<? extends PolyVariable<C>, BigInt> monomEntry : monom.getKey().getExponents().entrySet()) {
                if (!sigma.containsKey(monomEntry.getKey())) {
                    if (monomEntry.getKey().isMax()) {
                        final PolyMaxVariable<C> maxVar =
                            (PolyMaxVariable<C>) monomEntry.getKey();
                        final PolyMaxVariable<C> newMaxVar =
                            maxVar.applyVarSubstitution(sigma);
                        newMonomMap.put(newMaxVar, monomEntry.getValue());
                        if (newMaxVar != maxVar) {
                            changedMonom = true;
                        }
                    } else {
                        newMonomMap.put(monomEntry.getKey(),
                            monomEntry.getValue());
                    }
                } else {
                    final C multCoeff = sigma.get(monomEntry.getKey());

                    newCoeff = newCoeff.mult(multCoeff);
                    changedMonom = true;
                }
            }
            if (!changedMonom) {
                final Polynomial<C> addPoly = this.factory.create(monom.getKey(), monom.getValue());
                res =
                    res.add(addPoly);
                continue;
            }
            changedMonomials = true;
            final Monomial<C> newMonom =
                this.factory.createMonomial(this.ring, ImmutableCreator.create(newMonomMap));
            final Polynomial<C> mult = this.factory.create(newMonom, newCoeff);
            res = res.add(mult);
        }
        if (changedMonomials) {
            return res;
        } else {
            return this;
        }
    }

    public Polynomial<C> applySubstitution(final BasicPolySubstitution sigma) {
        boolean changedMonomials = false;
        Polynomial<C> res = this.factory.zero(this.ring);

        for (final Map.Entry<Monomial<C>, C> monom : this.monomials.entrySet()) {
            final Map<PolyVariable<C>, BigInt> newMonomMap =
                new LinkedHashMap<PolyVariable<C>, BigInt>();
            boolean changedMonom = false;
            for (final Map.Entry<? extends PolyVariable<C>, BigInt> monomEntry : monom.getKey().getExponents().entrySet()) {
                if (!sigma.substitutesPoly(monomEntry.getKey())) {
                    if (monomEntry.getKey().isMax()) {
                        final PolyMaxVariable<C> maxVar =
                            (PolyMaxVariable<C>) monomEntry.getKey();
                        final PolyMaxVariable<C> newMaxVar =
                            maxVar.applySubstitution(sigma);
                        newMonomMap.put(newMaxVar, monomEntry.getValue());
                        if (newMaxVar != maxVar) {
                            changedMonom = true;
                        }
                    } else {
                        newMonomMap.put(monomEntry.getKey(),
                            monomEntry.getValue());
                    }
                } else {
                    changedMonom = true;
                }
            }
            if (!changedMonom) {
                final Polynomial<C> addPoly = this.factory.create(monom.getKey(), monom.getValue());
                res =
                    res.add(addPoly);
                continue;
            }
            changedMonomials = true;
            final Monomial<C> newMonom =
                this.factory.createMonomial(this.ring, ImmutableCreator.create(newMonomMap));
            Polynomial<C> mult = this.factory.create(newMonom, monom.getValue());
            for (final Map.Entry<? extends PolyVariable<C>, BigInt> monomEntry : monom.getKey().getExponents().entrySet()) {
                if (sigma.substitutesPoly(monomEntry.getKey())) {
                    for(int i = monomEntry.getValue().intValue() - 1; i >= 0; i--) {
                        mult = mult.mult(sigma.substitutePoly(monomEntry.getKey()));
                    }
                }
            }
            res = res.add(mult);
        }
        if (changedMonomials) {
            return res;
        } else {
            return this;
        }
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
        if (obj instanceof Polynomial<?>) {
            final Polynomial<?> other = (Polynomial<?>) obj;
            return other.hash == this.hash && this.monomials.equals(other.monomials);
        } else {
            return false;
        }
    }

    @Override
    public void export(final StringBuilder sb,
        final Export_Util o,
        final VerbosityLevel verbosityLevel) {
        if (this.isZero()) {
            this.ring.zero().export(sb, o, verbosityLevel);
            return;
        } else if (this.isOne()) {
            this.ring.one().export(sb, o, verbosityLevel);
            return;
        }

        boolean first = true;
        for (final Map.Entry<Monomial<C>, C> monomial : this.monomials.entrySet()) {
            C coeff = monomial.getValue();
            if (!first) {
                if (monomial.getValue().signum() == -1) {
                    sb.append(" - ");
                    coeff = coeff.negate();
                } else {
                    sb.append(" + ");
                }
            } else if (monomial.getValue().signum() == -1) {
                sb.append("-");
                coeff = coeff.negate();
            }

            first = false;

            final boolean constantPart = monomial.getKey().isConstantPart();

            if (!coeff.isOne() ||
                    constantPart) {
                coeff.export(sb, o, verbosityLevel);
                if (!constantPart) {
                    sb.append(" ");
                    sb.append(o.multSign());
                    sb.append(" ");
                }
            }

            if (!constantPart) {
                monomial.getKey().export(sb, o, verbosityLevel);
            }

        }
    }

    @Override
    public Map<String, String> getXmlAttribs(final XmlExporter xe) {
        return null;
    }

    @Override
    public XmlContentsMap getXmlContents(final XmlExporter xe) {
        final XmlContentsMap contents = new XmlContentsMap();

        int id = 0;

        if (this.monomials.isEmpty()) {
            contents.add("coeff", "id", Integer.toString(id), this.ring.zero());
            contents.add("monomial", "id", Integer.toString(id), Monomial.create(this.ring, this.factory));
        } else {
            for (final Map.Entry<Monomial<C>, C> monomial : this.monomials.entrySet()) {
                contents.add("coeff", "id", Integer.toString(id), monomial.getValue());
                contents.add("monomial", "id", Integer.toString(id), monomial.getKey());

                id++;
            }
        }
        return contents;
    }

    @Override
    public Polynomial<C> one() {
        return this.factory.one(this.ring);
    }

    @Override
    public Polynomial<C> zero() {
        return this.factory.zero(this.ring);
    }

    @Override
    public Integer semiCompareTo(final Polynomial<C> other) {
        return null;
    }

    @Override
    public Polynomial<C> getValue() {
        return this;
    }

    @Override
    public Integer signum() {
        return null;
    }

    @Override
    public String getDomainSuffix() {
        return null;
    }

    @Override
    public SemiRingDomain<C> getDomain() {
        return this.ring.createUnknownVarRange();
    }

    @Override
    public boolean isSameRing(final SemiRing<?> other) {
        if (other instanceof Polynomial<?>) {
            final Polynomial<?> otherPoly = (Polynomial<?>) other;
            return otherPoly.factory.equals(this.factory);
        }
        return false;
    }

    public PolyFactory getFactory() {
        return this.factory;
    }

    @Override
    public SemiRingDomain<Polynomial<C>> createVarRange(final Polynomial<C> min,
        final Polynomial<C> max) {
        throw new UnsupportedOperationException("not implemented");
    }

    @Override
    public SemiRingDomain<Polynomial<C>> createUnknownVarRange() {
        throw new UnsupportedOperationException("not implemented");
    }

    public ITerm<C> toTerm(final IDPPredefinedMap predefinedMap) {
        final SemiRingDomain<C> dom = this.getDomain();

        ITerm<C> res = null;

        if (!this.isZero()) {
            final List<SemiRingDomain<C>> dom_dom = new ArrayList<SemiRingDomain<C>>(2);
            dom_dom.add(dom);
            dom_dom.add(dom);

            @SuppressWarnings("unchecked")
            final IFunctionSymbol<C> addSymbol = (IFunctionSymbol<C>) predefinedMap.getFunctionSymbol(Func.Add, dom_dom);
            @SuppressWarnings("unchecked")
            final IFunctionSymbol<C> multSymbol = (IFunctionSymbol<C>) predefinedMap.getFunctionSymbol(Func.Mul, dom_dom);

            for (final Map.Entry<Monomial<C>, C> monomialCoeff : this.monomials.entrySet()) {
                final ITerm<C> monomialCoeffTerm = this.convertMonomial(monomialCoeff.getKey(), monomialCoeff.getValue(), predefinedMap, multSymbol);

                if (res == null) {
                    res = monomialCoeffTerm;
                } else {
                    res = ITerm.createFunctionApplication(addSymbol, res, monomialCoeffTerm);
                }
            }
        }

        if (res != null) {
            return res;
        } else {
            return this.ring.zero().getTerm(predefinedMap);
        }
    }

    private ITerm<C> convertMonomial(final Monomial<C> monomial, final C coeff, final IDPPredefinedMap predefinedMap, final IFunctionSymbol<C> multSymbol) {
        ITerm<C> res;
        if (monomial.isConstantPart() || !coeff.isOne()) {
            res = coeff.getValue().getTerm(predefinedMap);
        } else {
            res = null;
        }

        for (final Map.Entry<? extends PolyVariable<C>, BigInt> varExponent : monomial.getExponents().entrySet()) {
            if (varExponent.getKey().isMax()) {
                throw new UnsupportedOperationException("max is not predefined yet");
            } else {
                final IVariable<C> var = (IVariable<C>) varExponent.getKey();

                BigInteger remainingExponent = varExponent.getValue().getBigInt();
                assert remainingExponent.signum() >= 0 : "illegal polinomial with negative exponent";
                while (remainingExponent.signum() != 0) {
                    remainingExponent = remainingExponent.subtract(BigInteger.ONE);
                    if (res != null) {
                        res = ITerm.createFunctionApplication(multSymbol, res, var);
                    } else {
                        res = var;
                    }
                }
            }
        }

        return res;
    }

    public C getRing() {
        return this.ring;
    }

    @Override
    public boolean isBoundedRing() {
        return this.ring.isBoundedRing();
    }

    @Override
    @Deprecated
    public ITerm<Polynomial<C>> getTerm(final IDPPredefinedMap predefinedMap) {
        throw new UnsupportedOperationException("no pre-defined terms for polynomials");
    }
}
