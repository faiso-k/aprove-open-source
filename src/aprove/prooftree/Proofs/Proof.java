package aprove.prooftree.Proofs;

import org.w3c.dom.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.dpframework.*;
import aprove.verification.oldframework.Utility.*;
import aprove.xml.*;
import immutables.*;

/**
 * Created on 27.05.2005 by marmer Interface representing a proof. In constrast
 * to the earlier version of proof which provided much functionality to control
 * the build of the proof graph and generate a linear output, we will keep
 * proofs simple now and assign all control to other classes.
 * @author marmer
 * @version $Id$
 */

public interface Proof extends Immutable, VerbosityExportable, XMLProofExportable, CPFProof {
    /*
     * Every proof has to provide a short and a long name.
     */
    public String getName(NameLength length);

    public Proof deepcopy();

    public abstract class DefaultProof implements Proof {

        /*
         * Override these attributes to automatically return
         * short and long name in getName(NameLength) (in
         * compliance with the old Proof class.
         */
        protected String shortName;
        protected String longName;

        protected StringBuffer result;

        public DefaultProof() {
            this.result = new StringBuffer();
            this.shortName = this.getClass().getSimpleName();
            this.longName = this.getClass().getName();
        }

        /**
         * Needs to be called before export is started.
         */
        protected void startUp() {
            this.result = new StringBuffer();
        }

        /*
         * Default implementation using short- and longName attributes.
         */
        @Override
        public String getName(final NameLength length) {
            switch (length) {
            case SHORT:
                return this.shortName;
            case LONG:
                return this.longName;
            default:
                return "Unknown name length.";
            }
        }

        @Override
        public String export(final Export_Util o) {
            return this.export(o, VerbosityExportable.DEFAULT_LEVEL);
        }

        /**
         * Public getter method which should only be used by XMLEncoder.
         */
        public String getLongName() {
            return this.longName;
        }

        /**
         * Public setter method which should only be used by XMLDecoder.
         */
        public void setLongName(final String longName) {
            this.longName = longName;
        }

        /**
         * Public getter method which should only be used by XMLEncoder.
         */
        public String getShortName() {
            return this.shortName;
        }

        /**
         * Public setter method which should only be used by XMLDecoder.
         */
        public void setShortName(final String shortName) {
            this.shortName = shortName;
        }

        @Override
        public Proof deepcopy() {
            return null;
        }

        @Override
        public Element toDOM(final Document doc, final XMLMetaData storage) {
            final Element e = XMLTag.UNKNOWN_PROOF.createElement(doc);
            e.appendChild(doc.createTextNode(this.getClass().getCanonicalName()+" is not formalized yet!"));
            return e;
        }

        @Override
        public Element toCPF(
            final Document doc,
            final Element[] childrenProofs,
            final XMLMetaData xmlMetaData,
            final CPFModus modus)
        {
            throw new RuntimeException("toCPF of " + this.getClass().getCanonicalName() + " is not formalized yet!");
        }

        @Override
        public XMLMetaData adaptMetaData(final XMLMetaData metaData) {
            return metaData;
        }

        @Override
        public boolean isCPFCheckableProof(final CPFModus modus) {
            return false;
        }

        /**
         * delivers the tag that should be used for proofs
         */
        @Override
        public CPFTag positiveTag() {
            return CPFTag.UNKNOWN_INPUT_PROOF;
        }

        /**
         * delivers the tag that should be used for disproofs
         */
        @Override
        public CPFTag negativeTag() {
            return CPFTag.UNKNOWN_INPUT_PROOF;
        }


        @Override
        public String getNonCPFExportableReason(final CPFModus modus) {
            final String s = this.getClass().getCanonicalName();
            return s == null ? "unknown class" : s;
        }

        @Override
        public boolean requireFullSubproof(final CPFModus modus, final int i) {
            return false;
        }

        /**
         * @return a nice string representation
         */
        @Override
        public String toString() {
            return this.export(new PLAIN_Util());
        }

    }

}
