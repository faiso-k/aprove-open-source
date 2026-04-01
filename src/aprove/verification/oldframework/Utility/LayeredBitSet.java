package aprove.verification.oldframework.Utility;

import java.util.*;

/**
 * @author Christian Kaeunicke
 * @version $Id$
 */
public class LayeredBitSet {
    protected int layers;

    BitSet[] bitSets;

    public LayeredBitSet() {
    this(1, -1);
    };

    public LayeredBitSet(int layers) {
    this(layers, -1);
    };

    public LayeredBitSet(int layers, int nbits) {
    this.bitSets = new BitSet[layers];
    this.layers = layers;
    for (int i = 0 ; i < layers ; i++) {
        if (nbits > 0) {
        this.bitSets[i] = new BitSet(nbits);
        } else {
        this.bitSets[i] = new BitSet();
        };
    };
    };

    public void or(LayeredBitSet set) {
    for (int i = 0 ; i < this.layers ; i++) {
        this.bitSets[i].or(set.getLayer(i));
    }
    };

    public void and(LayeredBitSet set) {
    for (int i = 0 ; i < this.layers ; i++) {
        this.bitSets[i].and(set.getLayer(i));
    }
    };

    public boolean get(int layer, int pos) {
    return this.bitSets[layer].get(pos);
    };

    public boolean get(int pos) {
    return this.get(0, pos);
    };

    public void set(int pos) {
     this.set(0, pos, true);
    };

    public void set(int pos, boolean value) {
     this.set(0, pos, value);
    };

    public void set(int layer, int pos) {
     this.set(layer, pos, true);
    };

    public void set(int layer, int pos, boolean value) {
     this.bitSets[layer].set(pos, value);
    };

    public void set(int layer, int from, int to) {
    this.set(layer, from, to, true);
    };

    public void set(int layer, int from, int to, boolean value) {
    this.bitSets[layer].set(from, to, value);
    };

    public BitSet getLayer(int layer) {
    return this.bitSets[layer];
    };
}
