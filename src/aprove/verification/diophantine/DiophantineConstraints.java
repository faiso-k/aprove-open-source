package aprove.verification.diophantine;

import java.util.*;

import org.w3c.dom.*;

import aprove.prooftree.Export.ProofPurposeDescriptors.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.verification.dpframework.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.xml.*;

public class DiophantineConstraints extends DefaultBasicObligation {

    private List<SimplePolyConstraint> constraints;

    public DiophantineConstraints(List<SimplePolyConstraint> constraints) {
        this.constraints = constraints;
    }

    @Override
    public String getName(NameLength length) {
        return length.equals(NameLength.SHORT) ? "DIO" : "Diophantine Constraints";
    }

    @Override
    public String export(Export_Util o) {
        StringBuilder sb = new StringBuilder();
        for (SimplePolyConstraint constraint : this.constraints) {
            sb.append(o.export(constraint));
            sb.append(o.newline());
        }
        return sb.toString();
    }

    public Collection<? extends SimplePolyConstraint> getConstraints() {
        return this.constraints;
    }

    @Override
    public Element toDOM(Document doc, XMLMetaData xmlMetaData) {
        Element constraintsTag = XMLTag.DIO_CONSTRAINTS.createElement(doc);
        for (SimplePolyConstraint constraint : this.constraints) {
            Element constraintTag = constraint.toDIODOM(doc, xmlMetaData);
            constraintsTag.appendChild(constraintTag);
        }
        return constraintsTag;
    }

    @Override
    public ProofPurposeDescriptor getProofPurposeDescriptor() {
        return new DiophantineProofPurposeDescriptor(this);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String getStrategyName() {
        return "dio";
    }

}
