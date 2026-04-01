package aprove.verification.oldframework.PropositionalLogic.Translation;

import java.io.*;


/**
 * This implements Tseitin's algorithm for transforming arbitrary SAT formulae into CNF.
 * It is implemented to reasonably save time and space.
 * By introducing side effects we could save more of both, but for time being try to avoid that.
 *
 * This class is not reentrant.
 *
 * @author kabasci
 *
 */
public class Tseitinizer {

    //////////////////////////////////////////////////////
    // Code spoiler: This one is actually quite easy to understand if disregarding all the assertSane blocks.
    // Those ones are only there because a dimacs clause containing the same literal negated and nonnegated is undefined in value.
    // Well it is true, but since we are interested in the outputs, this leads to trouble.
    // Furthermore SAT solvers are not forced to implement this behaviour.
    // This actually makes up more than 2/3s of the code, and the rest is straightforward.
    //////////////////////////////////////////////////////

    // This one is used to write to. We assume it has been created before.
    private final DimacsGenerator out;

    /**
     * Creates a new Tseitinizer based on a DimacsGenerator.
     * @param output
     */
    public Tseitinizer(final DimacsGenerator output) {
        this.out = output;
    }

    // Helper array to save space; we grow it like an arrayList.
    private int[] clause = new int[4];

    // Shall we conduct sanity checks? Note: Increases complexity from O(n) to O(n^2) where n is the number of literals in a clause.
    private final static boolean assertSane = true;

    /**
     * Resize the array as needed; at least double its size each time to avoid doing this too often.
     * The reference to the old array is dropped.
     * @param newSize The new required size.
     */
    private void redimArray(final int newSize) {
        if (this.clause.length < newSize) {
            this.clause = new int[newSize > this.clause.length * 2 ? newSize : this.clause.length * 2];
        }
    }


    /**
     * An or is basically transformed into a clause containing all the inputs
     * and the negated output (at least one),
     * and per input one clause containing the output and this negated input (any one is enough).
     * @param output The id of the output gate.
     * @param inputs The inputs to use in this or
     * @param count The number of inputs to regard
     */
    public void pushOr(final int output, final int[] inputs, final int count) throws IOException {

        // Local copies - only needed in case we use the sanity check.
        int lcount = count;
        int[] linputs = inputs;

        if (Tseitinizer.assertSane) {

            // "Quick" sanity check (actually square); the clause cannot contain the same literal twice. If we can really ensure that this is not needed, we can put it away.
            // Since this never ever should happen, we should optimize this away before.
            for (int i=0; i<lcount; i++) {
                // Maybe we even have the output equal to an input?
                if (Math.abs(output) == Math.abs(linputs[i])) {
                    // We *seriously* don't like that. This is just plain undefined.
                    // For us, anyway: A way would be to define a fixed point and using absorbtion.
                    // However I strongly think in our case this is a clear hint for a modelling error and thus we throw one.
                    throw new IllegalArgumentException("Non-DAG as input for Tseitinizer.");
                }
                for (int j=i+1; j<lcount; j++) {
                    if (Math.abs(linputs[i]) == Math.abs(linputs[j])) {
                        // ok that went wrong. Now the result depends on the sign...
                        if (linputs[i] == -linputs[j]) {
                            // This one ain't goning to be false anymore.
                            this.clause[0] = output;
                            this.out.outputClause(this.clause, 1);
                            return;
                        } else {
                            // "just" a redundant symbol.
                            // Swap it with the last one and decrease the local count.
                            // First to avoid side effects we now need a local copy of the input - if this is the first occasion of this.
                            if (linputs == inputs) {
                                // This is the first happening of this inside this clause.
                                linputs = new int[count-1];
                                // Copy the whole array, skipping the j-Position.
                                for (int k=0; k<j; k++) {
                                    linputs[k] = inputs[k];
                                }
                                for (int k=j+1; k<count; k++) {
                                    linputs[k-1] = inputs[k];
                                }
                                lcount = count - 1;
                            } else {
                                // Oh, one more :)
                                // no problem, just swap thisone with the last entry and decrease the count.
                                final int temp = linputs[lcount-1];
                                // Note that we keep the *first one*. This is better since the latter one could also *be* the last one.
                                linputs[lcount-1] = linputs[j];
                                linputs[j] = temp;
                                lcount--;
                            }
                        }
                    }
                }
            }
        }



        // is the array big enough?
        this.redimArray(lcount+1);

        /* This works for counts of one or more. Thus catch empty ors...*/
        if (lcount == 0) {
            // by default, an empty or is false.
            // We represent this by the clause containing only the negated output.
            // At this stage this should actually not happen since it should have been simplified away...
            this.clause[0] = -output;
            this.out.outputClause(this.clause, 1);
            return;
        }
        // first, consider the at least one clause...
        for (int i=0; i < lcount; i++) {
            this.clause[i] = linputs[i];
        }
        this.clause[lcount] = -output;
        this.out.outputClause(this.clause, lcount+1);

        // now for all the inputs the implication...
        for (int i=0; i < lcount; i++) {
            this.clause[0] = output;
            this.clause[1] = -linputs[i];
            this.out.outputClause(this.clause, 2);
        }

    }

    /**
     * An and is basically transformed into a clause containing all the negated inputs
     * and the output (all of them),
     * and per input one clause containing the negated output and this input (any one not fails).
     * @param output The id of the output gate.
     * @param inputs The inputs to use in this or
     * @param count The number of inputs to regard
     */
    public void pushAnd(final int output, final int[] inputs, final int count) throws IOException {

        // Local copies - only needed in case we use the sanity check.
        int lcount = count;
        int[] linputs = inputs;

        if (Tseitinizer.assertSane) {

            // "Quick" sanity check (actually square); the clause cannot contain the same literal twice. If we can really ensure that this is not needed, we can put it away.
            // Since this never ever should happen, we should optimize this away before.
            for (int i=0; i<lcount; i++) {
                // Maybe we even have the output equal to an input?
                if (Math.abs(output) == Math.abs(linputs[i])) {
                    // We *seriously* don't like that. This is just plain undefined.
                    // For us, anyway: A way would be to define a fixed point and using absorbtion.
                    // However I strongly think in our case this is a clear hint for a modelling error and thus we throw one.
                    throw new IllegalArgumentException("Non-DAG as input for Tseitinizer.");
                }
                for (int j=i+1; j<lcount; j++) {
                    if (Math.abs(linputs[i]) == Math.abs(linputs[j])) {
                        // ok that went wrong. Now the result depends on the sign...
                        if (linputs[i] == -linputs[j]) {
                            // This one ain't goning to be true.
                            this.clause[0] = -output;
                            this.out.outputClause(this.clause, 1);
                            return;
                        } else {
                            // "just" a redundant symbol.
                            // Swap it with the last one and decrease the local count.
                            // First to avoid side effects we now need a local copy of the input - if this is the first occasion of this.
                            if (linputs == inputs) {
                                // This is the first happening of this inside this clause.
                                linputs = new int[count-1];
                                // Copy the whole array, skipping the j-Position.
                                for (int k=0; k<j; k++) {
                                    linputs[k] = inputs[k];
                                }
                                for (int k=j+1; k<count; k++) {
                                    linputs[k-1] = inputs[k];
                                }
                                lcount = count - 1;
                            } else {
                                // Oh, one more :)
                                // no problem, just swap thisone with the last entry and decrease the count.
                                final int temp = linputs[lcount-1];
                                // Note that we keep the *first one*. This is better since the latter one could also *be* the last one.
                                linputs[lcount-1] = linputs[j];
                                linputs[j] = temp;
                                lcount--;
                            }
                        }
                    }
                }
            }
        }

        // is the array big enough?
        this.redimArray(lcount+1);

        /* This works for counts of one or more. Thus catch empty ands...*/
        if (lcount == 0) {
            // by default, an empty and is true.
            // We represent this by the clause containing only the output.
            // At this stage this should actually not happen since it should have been simplified away...
            this.clause[0] = output;
            this.out.outputClause(this.clause, 1);
            return;
        }
        // first, consider the all of them clause...
        for (int i=0; i < lcount; i++) {
            this.clause[i] = -linputs[i];
        }
        this.clause[lcount] = output;
        this.out.outputClause(this.clause, lcount+1);

        // now for all the inputs the implication...
        for (int i=0; i < lcount; i++) {
            this.clause[0] = -output;
            this.clause[1] = linputs[i];
            this.out.outputClause(this.clause, 2);
        }

    }

    /**
     * An iff is true iff the two inputs are the same.
     * By Tseitin, we transform it into two clauses insisting they not be unequal and two clauses insisting it be true if both are equal.
     * @param output
     * @param in1
     * @param in2
     */
    public void pushIff(final int output, final int in1, final int in2) throws IOException {

        // The sanity check...
        // We do not need local copies here, we either have a constant or an error if it fails.
        if (Tseitinizer.assertSane) {
            if (output == in1 || output == in2) {
                // Undefined. There is even not a fixed point for this.
                throw new IllegalArgumentException("Non-DAG input to Tseitinizer.");
            } else if (in1 == in2) {
                // This is true.
                this.clause[0] = output;
                this.out.outputClause(this.clause, 1);
                return;
            } else if (in1 == -in2) {
                // This is false.
                this.clause[0] = -output;
                this.out.outputClause(this.clause, 1);
                return;
            }
        }



        this.redimArray(3);

        // False if in1+, in2-
        this.clause[0] = -output;
        this.clause[1] = -in1;
        this.clause[2] = in2;
        this.out.outputClause(this.clause, 3);

        // False if in1-, in2+
        this.clause[0] = -output;
        this.clause[1] = in1;
        this.clause[2] = -in2;
        this.out.outputClause(this.clause, 3);

        // True if in1-, in2-
        this.clause[0] = output;
        this.clause[1] = in1;
        this.clause[2] = in2;
        this.out.outputClause(this.clause, 3);

        // True if in1+, in2+
        this.clause[0] = output;
        this.clause[1] = -in1;
        this.clause[2] = -in2;
        this.out.outputClause(this.clause, 3);

    }

    /**
     * We duly hope this is only used once, but nevertheless needed.
     * @param output The literal assigned to true
     * @throws IOException
     */
    public void pushTrue(final int output) throws IOException {
       this.redimArray(1);
       this.clause[0] = output;
       this.out.outputClause(this.clause, 1);
    }

    /**
     * We duly hope this is only used once, but nevertheless needed.
     * @param output The literal assigned to false
     * @throws IOException
     */
    public void pushFalse(final int output) throws IOException {
       this.redimArray(1);
       this.clause[0] = -output;
       this.out.outputClause(this.clause, 1);
    }

    /**
     * ITE is true iff either if is true and then is true, or if is false and else is true
     * By Tseitin this corresponds to the following clauses:
     * not then or not if or ITE
     * not else or if or ITE
     * else or if or not ITE
     * then or not if or not ITE
     * @param output Output id
     * @param ifpart The id of the if-Part of the gate
     * @param thenpart The id of the then-Part of the gate
     * @param elsepart The id of the else-Part of the gate
     * TODO: Add a clause aiding Minisat-Propagation
     */
    public void pushITE(final int output, final int ifpart, final int thenpart, final int elsepart) throws IOException {

        this.redimArray(3);

        // The sanity check.
        // Here we actually have a sane duplication: then or else can be the same (though then the whole thing collapses to an iff).
        // Anything else is completely different upfront:
        // if == then becomes -if => else
        // if == -else becomes if => then
        // if == -then != (-1)else becomes !if
        // if == else != (-1)then becomes if
        // all the same becomes if
        // and so forth. Comments for each case below.
        // and anything == output is undefined again
        boolean useThen = true;
        boolean useElse = true;

        if (Tseitinizer.assertSane) {
            if (Math.abs(output) == Math.abs(ifpart) || Math.abs(output) == Math.abs(thenpart) || Math.abs(output) == Math.abs(elsepart)) {
                throw new IllegalArgumentException("Non-DAG input to Tseitinizer.");
            }
            if (thenpart == ifpart) {
                // Hmm. Are we at least orthogonal to the else?
                if (thenpart == elsepart) {
                    // if x then x else x. True for x=true.
                    // nope, all the same. Assert that it holds.

                    this.clause[0] = output;
                    this.clause[1] = -ifpart;
                    this.out.outputClause(this.clause, 2);

                    this.clause[0] = -output;
                    this.clause[1] = ifpart;
                    this.out.outputClause(this.clause, 2);

                    return;

                } else if (thenpart == -elsepart) {
                    // if x then x else -x.
                    // Tautology.

                    this.clause[0] = output;
                    this.out.outputClause(this.clause, 2);
                    return;
                } else {
                    // if x then x else y.
                    // The then part is trival, just ensure the else.
                    useThen = false;
                }
            } else if (thenpart == -ifpart) {
                // ok, this already can only hold if the ifpart is false.
                // Are we orthogonal to the else part?
                if (thenpart == elsepart) {
                    // if x then -x else -x. True for x=false.
                    // That's fine. Just ensure the ifpart does not hold.

                    this.clause[0] = output;
                    this.clause[1] = ifpart;
                    this.out.outputClause(this.clause, 2);

                    this.clause[0] = -output;
                    this.clause[1] = -ifpart;
                    this.out.outputClause(this.clause, 2);
                    return;

                } else if (thenpart == -elsepart) {
                    // if x then -x else x
                    // Not going to work, contradiction.
                    this.clause[0] = -output;
                    this.out.outputClause(this.clause, 2);
                    return;
                } else {
                    // if x then -x else y
                    // ok, this can actually work. But we need to ensure the else part, AND that the ifpart is false.
                    this.clause[0] = output;
                    this.clause[1] = ifpart;
                    this.out.outputClause(this.clause, 2);

                    this.clause[0] = -output;
                    this.clause[1] = -ifpart;
                    this.out.outputClause(this.clause, 2);

                    this.clause[0] = output;
                    this.clause[1] = -elsepart;
                    this.out.outputClause(this.clause, 2);

                    this.clause[0] = -output;
                    this.clause[1] = elsepart;
                    this.out.outputClause(this.clause, 2);

                    return;



                }
                // Ok, completely weird cases done here.
            } else if (ifpart == elsepart) {
                // if x then y else x
                // We already know it is orthogonal to the thenpart.
                // So we need to ensure that it holds, and that the then part holds. Else part is not going to make it true.

                this.clause[0] = output;
                this.clause[1] = -ifpart;
                this.out.outputClause(this.clause, 2);

                this.clause[0] = -output;
                this.clause[1] = ifpart;
                this.out.outputClause(this.clause, 2);

                this.clause[0] = output;
                this.clause[1] = -thenpart;
                this.out.outputClause(this.clause, 2);

                this.clause[0] = -output;
                this.clause[1] = thenpart;
                this.out.outputClause(this.clause, 2);

                return;


            } else if (ifpart == -elsepart) {
                // if x then y else -x
                // We are orthogonal to the then part, and the else case trivially holds. So all left is to check the then part.
                useElse = false;
            }
        }


        if (useThen) {
            // False if then-, if+
            this.clause[0] = -output;
            this.clause[1] = -ifpart;
            this.clause[2] = thenpart;
            this.out.outputClause(this.clause, 3);
            // True if if+, then+
            this.clause[0] = output;
            this.clause[1] = -ifpart;
            this.clause[2] = -thenpart;
            this.out.outputClause(this.clause, 3);
        }

        if (useElse) {
            // False if else-, if-
            this.clause[0] = -output;
            this.clause[1] = ifpart;
            this.clause[2] = elsepart;
            this.out.outputClause(this.clause, 3);
            // True if if-, else+
            this.clause[0] = output;
            this.clause[1] = ifpart;
            this.clause[2] = -elsepart;
            this.out.outputClause(this.clause, 3);
        }

    }

    /**
     * The bad one: XOr needs to be represented by its individual min/maxterms.
     * For two inputs this means
     * -Xor left right
     * -Xor -left -right
     * Xor -left right
     * Xor left -right
     * For more inputs this needs to be split accordingly.
     * It is adviseable to split the input before passing it here.
     * This method cannot do this since for labelling reasons it is restricted to returning only one output.
     * @param output
     * @param inputs
     * @param count
     * @throws IOException
     */
    public void pushXOr(final int output, final int[] inputs, final int count) throws IOException{

        // First a check to see if we have exactly two arguments. In this case use an optimized code.
        if (count == 2) {
            this.pushXOr2(output, inputs[0], inputs[1]);
        } else if (count > 2) {
            this.pushXOrN(output, inputs, count);
        } else if (count == 1) {

            // Sanity check:
            if (Tseitinizer.assertSane) {
                if (Math.abs(output) == Math.abs(inputs[0])) {
                    throw new IllegalArgumentException("Non-DAG-input to Tseitinizer");
                }
            }

            this.redimArray(2);

            // Identity
            this.clause[0] = -inputs[0];
            this.clause[1] = output;
            this.out.outputClause(this.clause, 2);

            this.clause[0] = inputs[0];
            this.clause[1] = -output;
            this.out.outputClause(this.clause, 2);

        } else if (count == 0) {
            // An empty XOr is defined to be false.
            this.clause[0] = -output;
            this.out.outputClause(this.clause, 1);
        }

    }


    /**
     * Helper for binary XOr. Since that is all that should be used, and the rest uses deep copies and recursion extensively, this is an optimized should-be-case handler.
     * @param output
     * @param in1
     * @param in2
     * @throws IOException
     */
    private void pushXOr2(final int output, final int in1, final int in2) throws IOException {

        // Sanity check
        if (Tseitinizer.assertSane) {
            if (Math.abs(output) == Math.abs(in1) || Math.abs(output) == Math.abs(in2)) {
                // We don't want that.
                throw new IllegalArgumentException("Non-DAG input to Tseitinizer");
            } else if (in1 == in2) {
                // This is a contradiction.
                this.clause[0] = -output;
                this.out.outputClause(this.clause, 1);
            } else if (in1 == -in2) {
                // This is a tautology.
                this.clause[0] = output;
                this.out.outputClause(this.clause, 1);
            }
        }

        // The four clauses for a binary XOr...
        this.redimArray(3);

        // False if in1+, in2+
        this.clause[0] = -output;
        this.clause[1] = -in1;
        this.clause[2] = -in2;
        this.out.outputClause(this.clause, 3);

        // False if in1-, in2-
        this.clause[0] = -output;
        this.clause[1] = in1;
        this.clause[2] = in2;
        this.out.outputClause(this.clause, 3);

        // True if in1-, in2+
        this.clause[0] = output;
        this.clause[1] = in1;
        this.clause[2] = -in2;
        this.out.outputClause(this.clause, 3);

        // True if in1+, in2-
        this.clause[0] = output;
        this.clause[1] = -in1;
        this.clause[2] = in2;
        this.out.outputClause(this.clause, 3);



    }

    /**
     * Internal helper for n-ary XOrs. This one actually only does the sanity check and starts the recursion.
     * @param output
     * @param inputs
     * @param count
     * @throws IOException
     */
    private void pushXOrN(final int output, final int[] inputs, final int count) throws IOException {

        // We are going to check the sanity once, in the beginning. Saves trouble later.
        // There is one creative point to this sanity check:
        // if we do find double entries, and each time we do so, we invert the output.
        // This is due to the nature of the XOr with y = x + x + ... = - (x + ...).
        //                                FIXME                        ^^^^^^^^^^^?


        // Local copies - only needed in case we use the sanity check. Note the local output.
        int lcount = count;
        int loutput = output;
        int[] linputs = inputs;

        if (Tseitinizer.assertSane) {

            // "Quick" sanity check (actually square); the clause cannot contain the same literal twice. If we can really ensure that this is not needed, we can put it away.
            // Since this never ever should happen, we should optimize this away before.
            for (int i=0; i<lcount; i++) {
                // Maybe we even have the output equal to an input?
                if (Math.abs(output) == Math.abs(linputs[i])) {
                    // We *seriously* don't like that. This is just plain undefined.
                    // For us, anyway: A way would be to define a fixed point and using absorbtion.
                    // However I strongly think in our case this is a clear hint for a modelling error and thus we throw one.
                    throw new IllegalArgumentException("Non-DAG as input for Tseitinizer.");
                }
                for (int j=i+1; j<lcount; j++) {
                    if (Math.abs(linputs[i]) == Math.abs(linputs[j])) {
                        // ok that went wrong. Now the result depends on the sign...
                        if (linputs[i] == -linputs[j]) {
                            // x + -x + ... = ... is a tautology. So we can actually remove *both* of them.
                            if (linputs == inputs) {
                                // This is the first happening of this inside this clause.
                                linputs = new int[count-2];
                                // Copy the whole array, skipping the i and j-Position. We do know j > i.
                                for (int k=0; k<i; k++) {
                                    linputs[k] = inputs[k];
                                }
                                for (int k=i+1; k<j; k++) {
                                    linputs[k-1] = inputs[k];
                                }
                                for (int k=j+1; k<count; k++) {
                                    linputs[k-2] = inputs[k];
                                }
                                lcount = count - 2;
                            } else {
                                // Oh, one more :)
                                // no problem, just replace thisone with the last entry, the other one with the one before and decrease the count by two.
                                // No need for temps here, we won't need it again.
                                // First take away the first one...
                                linputs[i] = linputs[lcount-2];
                                // now the second.
                                linputs[j] = linputs[lcount-1];
                                // Note that we might have done identity assignments here, but then due to the decrease of the count it won't matter.
                                lcount-=2;
                            }

                        } else {
                            // "just" a redundant symbol.
                            // Swap it with the last one and decrease the local count.
                            // First to avoid side effects we now need a local copy of the input - if this is the first occasion of this.
                            if (linputs == inputs) {
                                // This is the first happening of this inside this clause.
                                linputs = new int[count-1];
                                // Copy the whole array, skipping the j-Position.
                                for (int k=0; k<j; k++) {
                                    linputs[k] = inputs[k];
                                }
                                for (int k=j; k<count; k++) {
                                    linputs[k-1] = inputs[k];
                                }
                                lcount = count - 1;
                                // and toggle the output.
                                loutput *= -1;
                            } else {
                                // Oh, one more :)
                                // no problem, just swap thisone with the last entry and decrease the count.
                                final int temp = linputs[lcount-1];
                                // Note that we keep the *first one*. This is better since the latter one could also *be* the last one.
                                linputs[lcount-1] = linputs[j];
                                linputs[j] = temp;
                                lcount--;
                                // and toggle the output.
                                loutput *= -1;
                            }
                        }
                    }
                }
            }
        }

        // Did we reduce the count far enough to be in a special case?
        if (lcount < 3) {
            // Yes. Save the trouble and use our old helper method.
            this.pushXOr(loutput, linputs, lcount);
            // Terminates since lcount must be < count for this to be called.
        }

        // Check array size.
        this.redimArray(lcount+1);
        // ok, now that we are sane, we will need to recursively swap the entries.
        // We will feed our array with all of the values, positive. The last one is the output.
        for (int i=0; i < lcount; i++) {
            this.clause[i] = linputs[i];
        }
        this.clause[lcount] = loutput;

        // Now recursively generate clauses like lit1 lit2 lit3... counting whether an xor would be true for that maxterm and setting the output accordingly.
        this.pushXOrRec(this.clause, lcount, 0, -1);



    }

    /**
     * This is the internal recursion handler for n-ary XOrs. We assume sanity checks have been performed.
     * Side effect warning! The clause array is modified in the course of this method.
     * @param clause The array containing the inputs, and - at position count - the output. Will be modified during the course of the method, but will return in its original state.
     * @param count The number of inputs. The total number of relevant entries is this + 1.
     * @param position The position we are starting with. For position < count, split cases. For position == count, generate the respective clause.
     * @param outputModifier The output modifier, that is: so far, should the term be true for this maxterm? 1 for yes, -1 for no.
     */
    private void pushXOrRec(final int[] clause, final int count, final int position, final int outputModifier) throws IOException {

        // Are we ready to generate a clause?
        if (count == position) {
            // Ok, this is ready to be pushed.
            // Depending on the outputModifier, we will now set the clause.
            // If the outputModifier is 1 this means that for this minterm, XOr should return true. Else false.
            // Due to the construction, we can multiply this to the output.
            clause[count] *= outputModifier;
            this.out.outputClause(clause, count+1);
            // Undo the output modification.
            clause[count] *= outputModifier;
        } else {
            // Still work to do.
            // Case one: This minterm contains a false at the current position.
            // We work on maxterms, this means we invert the minterms by DeMorgan.
            // So this minterm is not negated for a false at this position.
            // A false is neutral to a minterm.
            this.pushXOrRec(clause, count, position + 1, outputModifier);
            // Case two: This minterm contains a true at the current position.
            // We work on maxterms, invert => negate the current atom:
            clause[position] *= -1;
            // A true negates the value of the rest of the XOr.
            this.pushXOrRec(clause, count, position + 1, -outputModifier);
            // Undo the change in the minterm before continuing.
            clause[position] *= -1;
        }

    }

}
