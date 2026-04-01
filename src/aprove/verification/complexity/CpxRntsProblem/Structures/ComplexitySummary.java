package aprove.verification.complexity.CpxRntsProblem.Structures;

import java.util.Optional;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.complexity.TruthValue.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import immutables.*;

/**
 * A summary of a function's complexity, containing both runtime and size
 * bounds. Each bound is represented by its complexity class (ComplexityValue)
 * and a polynomial bound (if the complexity is polynomial).
 *
 * @author mnaaf
 *
 */
public class ComplexitySummary implements Immutable, Exportable {

    public enum CpxType { Runtime, Size };

    private final Optional<ComplexityValue> cpxRuntime, cpxSize;
    private final Optional<SimplePolynomial> polyRuntime, polySize;

    private ComplexitySummary(Optional<ComplexityValue> cpxRuntime, Optional<SimplePolynomial> polyRuntime,
            Optional<ComplexityValue> cpxSize, Optional<SimplePolynomial> polySize) {
        this.cpxRuntime = cpxRuntime;
        this.cpxSize = cpxSize;
        this.polyRuntime = polyRuntime;
        this.polySize = polySize;
    }

    public static ComplexitySummary partial(CpxType cpxtype, ComplexityValue cpx, Optional<SimplePolynomial> poly) {
        if (poly.isPresent()) {
            assert cpx.equalsAsymptotic(ComplexityValue.fixedDegreePoly(poly.get().getDegree()));
        }
        switch (cpxtype) {
            case Runtime: return new ComplexitySummary(Optional.of(cpx), poly, Optional.empty(), Optional.empty());
            case Size: return new ComplexitySummary(Optional.empty(), Optional.empty(), Optional.of(cpx), poly);
        }
        return null;
    }

    public ComplexitySummary update(CpxType cpxtype, ComplexityValue cpx, Optional<SimplePolynomial> poly) {
        switch (cpxtype) {
            case Runtime: return new ComplexitySummary(Optional.of(cpx), poly, this.cpxSize, this.polySize);
            case Size: return new ComplexitySummary(this.cpxRuntime, this.polyRuntime, Optional.of(cpx), poly);
        }
        return null;
    }

    public boolean hasRuntime() {
        return this.cpxRuntime.isPresent();
    }

    public boolean hasSize() {
        return this.cpxSize.isPresent();
    }

    public ComplexityValue getRuntime() {
        return this.cpxRuntime.get();
    }

    public ComplexityValue getSize() {
        return this.cpxSize.get();
    }

    public Optional<SimplePolynomial> getRuntimePoly() {
        return this.polyRuntime;
    }

    public Optional<SimplePolynomial> getSizePoly() {
        return this.polySize;
    }

    private String exportBound(Optional<ComplexityValue> cpx, Optional<SimplePolynomial> poly, Export_Util eu) {
        if (!cpx.isPresent()) {
            return eu.escape("?");
        } else {
            String s = cpx.get().export(eu,"O");
            if (!poly.isPresent()) {
                return s;
            }
            return s + " [" + poly.get().export(eu) + "]";
        }
    }

    @Override
    public String export(Export_Util eu) {
        StringBuilder s = new StringBuilder();
        s.append(eu.escape("runtime: "));
        s.append(this.exportBound(this.cpxRuntime,this.polyRuntime,eu));
        s.append(eu.escape(", size: "));
        s.append(this.exportBound(this.cpxSize,this.polySize,eu));
        return s.toString();
    }

    @Override
    public String toString() {
        return this.export(new PLAIN_Util());
    }
}
