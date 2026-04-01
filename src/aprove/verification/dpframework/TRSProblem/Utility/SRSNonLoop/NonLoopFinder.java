package aprove.verification.dpframework.TRSProblem.Utility.SRSNonLoop;

import java.util.*;

import aprove.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.dpframework.TRSProblem.*;

/**
 * <p>
 * NonLoopFinder provides methods to find NonLoops according to <br>
 *"Automatische Erkennung von Ableitungsmustern in nichtterminierenden
 * Wortersetzungssystemen" <br>
 * Martin Oppelt
 * </p>
 * Transformation to QDPProblem by Fabian Emmes and Tim Enger
 * @author Tim Enger
 */

public class NonLoopFinder {

    private int newStructures = 0;

    /**
     * until this size of newStructures <br>
     * every "size" is checked if overlapsWith with OC1 rules
     */
    private int compareWithOC1;

    /**
     * store the generated DerivationStructures in different levels of bigness
     */
    private Map<Integer, Set<DerivationStructure>> structures;

    private Set<DerivationStructure> lookUpMap;

    /**
     * store self-embedding rule
     */
    private DerivationStructure nonLoop = null;

    private Abortion aborter;

    public NonLoopFinder(Abortion aborter, QDPProblem qdp, int compareWithOC1) {
        this.aborter = aborter;
        this.compareWithOC1 = compareWithOC1;
        this.lookUpMap = new HashSet<DerivationStructure>();
        this.structures = new LinkedHashMap<Integer, Set<DerivationStructure>>();

        // ******************* OC 1 *********************
        Set<DerivationStructure> ocs = new LinkedHashSet<DerivationStructure>();
        for (Rule rule : qdp.getR()) {
            ocs.add(new OverlapClosure(new StringPattern(rule.getLeft()),
                new StringPattern(rule.getRight()), 1, new Reason(
                    "original rule (OC 1)", rule, ReasonType.OC1), TRSType.R));
        }

        for (Rule rule : qdp.getP()) {
            ocs.add(new OverlapClosure(new StringPattern(rule.getLeft()),
                new StringPattern(rule.getRight()), 1, new Reason(
                    "original rule (OC 1)", rule, ReasonType.OC1), TRSType.P));
        }

        this.structures.put(0, ocs);

        this.testAndInsert(ocs);
    }

    public NonLoopFinder(Abortion aborter, QTRSProblem qtrs, int compareWithOC1) {
        this.aborter = aborter;
        this.compareWithOC1 = compareWithOC1;
        this.lookUpMap = new HashSet<DerivationStructure>();
        this.structures = new LinkedHashMap<Integer, Set<DerivationStructure>>();

        // ******************* OC 1 *********************
        Set<DerivationStructure> ocs = new LinkedHashSet<DerivationStructure>();
        for (Rule rule : qtrs.getR()) {
            ocs.add(new OverlapClosure(new StringPattern(rule.getLeft()),
                new StringPattern(rule.getRight()), 1, new Reason(
                    "original rule (OC 1)", rule, ReasonType.OC1), TRSType.R));
        }

        this.structures.put(0, ocs);

        this.testAndInsert(ocs);
    }

    public DerivationStructure findNonLoop() throws AbortionException {

        int count = 2;

        Set<DerivationStructure> firstOnes =
            new LinkedHashSet<DerivationStructure>(this.structures.get(0));

        while (this.nonLoop == null) {

            if (Globals.DEBUG_NEX) {
                System.err.println("-- #" + count + " -- #Structures: "
                    + this.newStructures);
            }

            this.aborter.checkAbortion();

            Set<DerivationStructure> valueCount = this.structures.get(count - 1);

            if (valueCount != null) {
                for (DerivationStructure ds : valueCount) {
                    if (ds instanceof DerivationPattern) {
                        DerivationPattern dp = (DerivationPattern) ds;
                        this.testAndInsert(dp.rotate());
                        this.testAndInsert(dp.lift());
                        this.testAndInsert(dp.expand());
                    } else {
                        this.testAndInsert(((OverlapClosure) ds).selfOverlapping());
                    }
                }
            }

            for (int i = 1; i < count; i++) {
                int temp = count - i;

                Set<DerivationStructure> valueI = this.structures.get(i);
                Set<DerivationStructure> valueTemp = this.structures.get(temp);

                if (valueI != null && valueTemp != null) {
                    Set<DerivationStructure> a =
                        new LinkedHashSet<DerivationStructure>(valueI);
                    Set<DerivationStructure> b =
                        new LinkedHashSet<DerivationStructure>(valueTemp);

                    for (DerivationStructure ds1 : a) {
                        if (this.compareWithOC1 >= this.newStructures) {

                            // heuristic
                            for (DerivationStructure ds2 : firstOnes) {
                                this.testAndInsert(ds1.overlapsWith(ds2));
                            }
                        }

                        for (DerivationStructure ds2 : b) {
                            this.testAndInsert(ds1.overlapsWith(ds2));
                        }
                    }
                }
            }
            count++;
        }

        if (Globals.DEBUG_NEX) {
            System.err.println("Structures: " + this.newStructures);
        }

        return this.nonLoop;
    }

    /**
     * insert a {@link Set} of DerivationStructures in set of rules w.r.t.
     * bigness (level)
     * @param setDs Set<DerivationStructure>
     */
    private void testAndInsert(Set<DerivationStructure> setDs) {
        // boolean newOne;

        for (DerivationStructure ds : setDs) {
            if (ds.selfEmbedding()) {
                this.nonLoop = ds;
                return;
            }

            // already inserted?
            /* newOne = true;
            for (int i : structures.keySet()) {
                if (structures.get(i).contains(ds) && i != 0) {
                    newOne = false;
                    break;
                }
            }*/

            if (!this.lookUpMap.contains(ds)) {
                this.newStructures++;
                Set<DerivationStructure> value =
                    this.structures.get(ds.getBigness());

                if (value != null) {
                    value.add(ds);
                    this.lookUpMap.add(ds);

                } else {
                    Set<DerivationStructure> set =
                        new LinkedHashSet<DerivationStructure>();
                    set.add(ds);
                    this.structures.put(ds.getBigness(), set);
                    this.lookUpMap.add(ds);
                }
            }
        }
    }
}
