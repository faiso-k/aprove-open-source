package aprove.verification.dpframework.TRSProblem.Utility.SRSNonLoop;

import java.util.*;

import org.w3c.dom.*;

import aprove.xml.*;

public interface DerivationStructure extends CPFAdditional {

    public boolean selfEmbedding();

    public int getBigness();

    public Set<DerivationStructure> overlapsWith(DerivationStructure ds);

    public Reason getReason();

    public TRSType getType();

    // only for DEBUG
    public String toString(int depth);

    public void toCPF(final Document doc, final XMLMetaData xmlMetaData, Element patterns, Set<DerivationStructure> exported);

    public Element toNontermCPF(final Document doc, final XMLMetaData xmlMetaData);


}