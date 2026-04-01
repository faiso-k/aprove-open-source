package aprove.verification.oldframework.Bytecode.StateRepresentation.Annotations;

import static aprove.verification.oldframework.Bytecode.Parser.ClassName.Important.*;
import static java.util.stream.Collectors.*;

import java.util.*;

import aprove.*;
import aprove.input.Programs.jbc.*;
import aprove.verification.oldframework.Bytecode.*;
import aprove.verification.oldframework.Bytecode.Parser.*;
import aprove.verification.oldframework.Bytecode.Parser.ClassName.*;
import aprove.verification.oldframework.Bytecode.Utils.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * Representation of type information stored for abstract instances and arrays.
 * AbstractTypes may contain types which can not be instantiated.
 * @author Marc Brockschmidt
 * @author Fabian K&uuml;rten
 */
public class AbstractType implements Immutable {
    /**
     * Set of possible classes of this instance.
     */
    private final ImmutableSet<FuzzyType> possibleClasses;

    /**
     * A cache for the enclosed type (helps if Array.get is called often).
     */
    private AbstractType enclosedType;

    /**
     * @param cPath The considered class path for this analysis.
     * @param possibleClass a type an instance annotated with this
     * {@link AbstractType} can be an instance of.
     */
    public AbstractType(final ClassPath cPath, final FuzzyType possibleClass) {
        if (Globals.useAssertions) {
            if (possibleClass.getArrayDimension() == 0 && possibleClass instanceof FuzzyClassType) {
                final FuzzyClassType fct = (FuzzyClassType) possibleClass;
                if (fct.isConcrete()) {
                    assert (!cPath.getTypeTree(fct.getMinimalClass()).isAbstract());
                }
            }
        }
        this.possibleClasses = ImmutableCreator.create(Collections.singleton(possibleClass));
    }

    /**
     * @param cPath The considered class path for this analysis.
     * @param possibleC the set of possible classes an instance annotated
     *  with this {@link AbstractType} can be an instance of.
     */
    public AbstractType(final ClassPath cPath, final JBCOptions options, final Collection<FuzzyType> possibleC) {
        assert (!possibleC.isEmpty());
        this.possibleClasses = ImmutableCreator.create(AbstractType.compress(cPath, options, possibleC));
        assert (!this.possibleClasses.isEmpty());
    }

    /**
     * @return true iff all needle types are also represented by the haystack
     * types.
     * @param haystack some number of fuzzytypes
     * @param needles some number of fuzzytypes
     * @param cPath The considered class path for this analysis.
     */
    private static boolean containsAll(
        final Set<? extends FuzzyType> haystack,
        final Set<? extends FuzzyType> needles,
        final ClassPath cPath,
        final JBCOptions options)
    {
        // first, throw out the exact matches
        final Set<FuzzyType> remaining = new LinkedHashSet<>(needles);
        remaining.removeAll(haystack);
        if (remaining.isEmpty()) {
            return true;
        }
        /*
         * Okay, we need to expand to be sure. Start with a single expansion
         * step, which is not enough to correctly handle arrays.
         */
        final Set<FuzzyType> candidates = new LinkedHashSet<>(haystack);
        candidates.removeAll(needles);
        if (candidates.isEmpty()) {
            // emptyset containsAll non-emptyset: false
            return false;
        }
        final Set<FuzzyType> expandedCandidates = new LinkedHashSet<>();
        for (final FuzzyType candidate : candidates) {
            candidate.expand(expandedCandidates, cPath, options);
        }
        remaining.removeAll(expandedCandidates);
        if (remaining.isEmpty()) {
            /*
             * This single expansion step was enough to reach all remaining
             * types.
             */
            return true;
        }

        // Now expand all remaining fuzzy types from the argument type.
        final Set<FuzzyType> expandedRemaining = new LinkedHashSet<>();
        for (final FuzzyType type : remaining) {
            type.expand(expandedRemaining, cPath, options);
        }
        expandedRemaining.removeAll(expandedCandidates);
        if (expandedRemaining.isEmpty()) {
            /*
             * Okay, after expansion on both sides, we reached all remaining
             * types.
             */
            return true;
        }
        expandedCandidates.removeAll(expandedRemaining);
        if (expandedCandidates.isEmpty()) {
            // emptyset containsAll non-emptyset: false
            return false;
        }

        for (final FuzzyType rem : expandedRemaining) {
            if (!rem.isArrayType()) {
                /*
                 * We try to find some non-array type. A single expansion always is
                 * enough to find this type, so this type is not contained.
                 */
                return false;
            }
        }

        /*
         * We need to answer "true" if one of the elements in the haystack is
         * [[...[jlO... (or some other array parent class) with a lower array
         * dimension, so that the higher array dimension of the needle can be
         * constructed.
         */
        final Pair<Integer, Integer> arrayInfoHaystack = AbstractType.getArrayInfoFromType(expandedCandidates);

        /*
         * There is a [...[jlO... (or some other array parent class) where
         * minArrayParentDim gives the number of "[".
         */
        final int minArrayParentDim = arrayInfoHaystack.x;

        for (final FuzzyType rem : expandedRemaining) {
            final int dim = rem.getArrayDimension();
            assert (dim > 0);
            if (minArrayParentDim > dim) {
                // we can't create [A| out of [[jlO...
                return false;
            } else if (minArrayParentDim == dim) {
                // now we need to have a closer look at the types
                if (!AbstractType.containsAll(expandedCandidates, Collections.singleton(rem), cPath, options)) {
                    return false;
                }
            }
        }
        return true;
    }

    /**
     * For some type X... or X| compute the expansion of X...
     * @param type Some type
     * @param typeExpansion set in which all children of <code>type</code> in
     * the type tree will be put.
     * @param cPath The considered class path for this analysis.
     */
    private static void expandAllPossibleTypes(
        final FuzzyType type,
        final Set<FuzzyType> typeExpansion,
        final ClassPath cPath,
        final JBCOptions options)
    {
        FuzzyType fuzzyType = type;
        // Make fuzzyType abstract
        if (fuzzyType instanceof FuzzyClassType) {
            final FuzzyClassType classType = (FuzzyClassType) fuzzyType;
            if (fuzzyType.isConcrete()) {
                fuzzyType = new FuzzyClassType(classType.getMinimalClass(), false, classType.getArrayDimension());
            }
        }
        fuzzyType.expand(typeExpansion, cPath, options);
    }

    /**
     * @param allTypes a collection of types
     * @param thisType Some type (should be in <code>allTypes</code>
     * @param otherTypes the union of the type expansions of all types
     *  in <code>allTypes</code> that are not equal to <code>thisType</code>
     *  (= \bigcup_{t \in allTypes \ {thisType} } expand(t))
     * @param cPath The considered class path for this analysis.
     */
    private static void expandOtherTypes(
        final Collection<FuzzyType> allTypes,
        final FuzzyType thisType,
        final Set<FuzzyType> otherTypes,
        final ClassPath cPath,
        final JBCOptions options)
    {
        //Construct the set of types described without type:
        for (final FuzzyType t : allTypes) {
            if (thisType == t) {
                continue;
            }
            t.expand(otherTypes, cPath, options);
        }
    }

    /**
     * @param fuzzyTypes the fuzzy types to analyze
     * @return Pair of integers, of which the first is the minimal array
     * dimension of an array parent class type (jlO, Serializable, Cloneable)
     * and the second is the maximal array dimension of any type.
     */
    private static Pair<Integer, Integer> getArrayInfoFromType(final Collection<FuzzyType> fuzzyTypes) {
        int minimalArrayParentDim = Integer.MAX_VALUE;
        int maximalArrayDim = 0;
        for (final FuzzyType fuzzyT : fuzzyTypes) {

            if (fuzzyT.getArrayDimension() > maximalArrayDim) {
                maximalArrayDim = fuzzyT.getArrayDimension();
            }
            if (fuzzyT instanceof FuzzyClassType
                && ((FuzzyClassType) fuzzyT).isArrayParentClass()
                && !fuzzyT.isConcrete()
                && fuzzyT.getArrayDimension() < minimalArrayParentDim)
            {
                minimalArrayParentDim = fuzzyT.getArrayDimension();
            }
        }

        return new Pair<>(minimalArrayParentDim, maximalArrayDim);
    }

    /**
     * @param prog The program context of this abstract type
     * @param firstType some fuzzy type
     * @param secondType another fuzzy type
     * @return the maximal common supertype of firstType and secondType
     */
    private static FuzzyType maximalCommonSupertype(
        final ClassPath cPath,
        final FuzzyType firstType,
        final FuzzyType secondType)
    {
        if (Globals.useAssertions) {
            assert (!(firstType instanceof FuzzyPrimitiveType && secondType instanceof FuzzyPrimitiveType && firstType
                .getArrayDimension() != secondType.getArrayDimension())) : "Trying to merge primitive type arrays of different dim "
                + firstType
                + " and "
                + secondType;
            assert (!(firstType instanceof FuzzyPrimitiveType && secondType instanceof FuzzyClassType && !firstType
                .isArrayType())) : "Trying to merge primitive type " + firstType + " with non-primitive " + secondType;
            assert (!(secondType instanceof FuzzyPrimitiveType && firstType instanceof FuzzyClassType && !secondType
                .isArrayType())) : "Trying to merge primitive type " + secondType + " with non-primitive " + firstType;
        }

        if (firstType instanceof FuzzyPrimitiveType && secondType instanceof FuzzyPrimitiveType) {
            return firstType;
        } else if ((firstType instanceof FuzzyPrimitiveType && secondType instanceof FuzzyClassType)
            || (secondType instanceof FuzzyPrimitiveType && firstType instanceof FuzzyClassType))
        {
            return new FuzzyClassType(JAVA_LANG_OBJECT.getClassName(), false, Math.min(
                firstType.getArrayDimension(),
                secondType.getArrayDimension()));
        } else {
            if (firstType.getArrayDimension() == secondType.getArrayDimension()) {
                return new FuzzyClassType(cPath
                    .getTypeTree((FuzzyClassType) firstType)
                    .getMaxCommonSupertype(cPath.getTypeTree((FuzzyClassType) secondType))
                    .getClassName(), false, firstType.getArrayDimension());
            }
            return new FuzzyClassType(JAVA_LANG_OBJECT.getClassName(), false, Math.min(
                firstType.getArrayDimension(),
                secondType.getArrayDimension()));
        }
    }

    /**
     * Takes a number of fuzzy types and tries to compress the contained information, i.e.,
     * if we have X| and all subtypes of X (as Y| or Y...), we change this to X...
     * @param cPath The considered class path for this analysis.
     * @param possibleClasses collection of fuzzy types
     * @return a set of types equivalent to <code>possibleClasses</code>, but possibly
     *  smaller
     */
    private static Set<FuzzyType> compress(final ClassPath cPath, final JBCOptions options, final Collection<FuzzyType> possibleClasses) {
        FuzzyType jlo = FuzzyClassType.FT_JAVA_LANG_OBJECT.toAbstract();
        if (possibleClasses.contains(jlo)) {
            return Collections.singleton(jlo);
        }
        if (options.avoidExpandingTypeTree()) {
            return new LinkedHashSet<>(possibleClasses);
        }
        if (possibleClasses.size() == 1) {
            return Collections.singleton(possibleClasses.iterator().next());
        }
        //Start by moving types of different array dimensions to separate sets
        final CollectionMap<Integer, FuzzyType> typesGroupedByDimension = new CollectionMap<>();
        for (final FuzzyType f : possibleClasses) {
            typesGroupedByDimension.add(f.getArrayDimension(), f);
        }

        // sort the array dimensions we need to look at
        final Set<Integer> keySet = typesGroupedByDimension.keySet();
        final Integer[] arrayDims = keySet.toArray(new Integer[keySet.size()]);
        Arrays.sort(arrayDims);

        // introduce X... as often and as high (low array dimension) as possible
        AbstractType.introduceAbstraction(cPath, options, typesGroupedByDimension, arrayDims);

        /*
         * We can save a lot of work if we have [...[jlO... or some other array
         * parent. If so, all "deeper" array types are already represented.
         */
        // The last entry in arrayDims is the greatest, i.e, this is the highest depth.
        int deleteDeeperThan = arrayDims[arrayDims.length - 1];
        OUTER: for (int i = 0; i < arrayDims.length; i++) {
            final int dim = arrayDims[i];
            // Loop over all types of the current dimension
            for (final FuzzyType type : typesGroupedByDimension.get(dim)) {
                if (type instanceof FuzzyClassType) {
                    final FuzzyClassType fct = (FuzzyClassType) type;
                    if (fct.isAbstract() && fct.isArrayParentClass()) {
                        deleteDeeperThan = dim;
                        break OUTER;
                    }
                }
            }
        }
        for (int i = 1; i < arrayDims.length; i++) {
            final int dim = arrayDims[i];
            if (dim > deleteDeeperThan) {
                typesGroupedByDimension.get(dim).clear();
            }
        }

        /*
         * In the second step we remove all those types that are already
         * represented by some other type (of the same array dimension). As an
         * example, "[[X..." also represents "[[Y|", so we remove "[[Y|".
         */
        for (int i = 1; i <= arrayDims.length; i++) {
            final int dim = arrayDims[arrayDims.length - i];
            final Set<FuzzyType> removed = new LinkedHashSet<>();
            for (final FuzzyType type : typesGroupedByDimension.get(dim)) {
                if (type.isConcrete()) {
                    // no subtypes, irrelevant
                    continue;
                }

                if (removed.contains(type)) {
                    // already represented, irrelevant
                    continue;
                }

                if (Globals.useAssertions) {
                    assert type instanceof FuzzyClassType : "non class type is not concrete";
                }
                final FuzzyClassType classType = (FuzzyClassType) type;

                //Set of types represented by type:
                final Set<FuzzyType> typeExpansion = new LinkedHashSet<>();
                AbstractType.expandAllPossibleTypes(classType, typeExpansion, cPath, options);

                // remove all the subtypes (concrete and abstract)
                for (final FuzzyType exp : typeExpansion) {
                    if (exp instanceof FuzzyClassType) {
                        // we do not want to remove the original type
                        final FuzzyClassType abstractType = ((FuzzyClassType) exp).toAbstract();
                        if (!abstractType.equals(classType)) {
                            removed.add(abstractType);
                        }
                    }
                }
                removed.addAll(typeExpansion);
            }

            typesGroupedByDimension.get(dim).removeAll(removed);
        }

        //Now compress
        final Set<FuzzyType> res = new LinkedHashSet<>();
        for (final Collection<FuzzyType> typeSet : typesGroupedByDimension.values()) {
            res.addAll(typeSet);
        }
        if (Globals.useAssertions) {
            assert !res.isEmpty() : "no type left";
        }
        return res;
    }

    /**
     * @return true iff the given type is represented by this abstract type.
     * @param argType another abstract type
     * @param cPath The considered class path for this analysis.
     */
    public boolean contains(final FuzzyType argType, final ClassPath cPath, final JBCOptions options) {
        return AbstractType.containsAll(this.possibleClasses, Collections.singleton(argType), cPath, options);
    }

    /**
     * @return true iff the types represented by the given abstract type are all
     * represented by this abstract type.
     * @param argType another abstract type
     * @param cPath The considered class path for this analysis.
     */
    public boolean containsAll(final AbstractType argType, final ClassPath cPath, final JBCOptions options) {
        return AbstractType.containsAll(this.possibleClasses, argType.possibleClasses, cPath, options);
    }

    /**
     * @return true iff one of the described types is an abstract array parent
     * type (such as jlObject, Cloneable or Serializable)
     */
    public boolean containsAbstractArrayParentType() {
        for (final FuzzyType t : this.possibleClasses) {
            if (t instanceof FuzzyClassType && !t.isConcrete()) {
                final FuzzyClassType fcT = (FuzzyClassType) t;
                if (fcT.isArrayParentClass()) {
                    return true;
                }
            }
        }
        return false;
    }

    /**
     * @return true iff not all of the described types are reference types.
     */
    public boolean containsPrimitiveType() {
        for (final FuzzyType t : this.possibleClasses) {
            if (t instanceof FuzzyPrimitiveType && t.getArrayDimension() == 0) {
                return true;
            }
        }
        return false;
    }

    /**
     * @return true iff not all of the described types are primitive types.
     */
    public boolean containsReferenceType() {
        for (final FuzzyType t : this.possibleClasses) {
            if (t instanceof FuzzyClassType || t.getArrayDimension() > 0) {
                return true;
            }
        }
        return false;
    }

    /**
     * This method provides all fuzzy types that are defined by this abstract
     * type. All returned fuzzy types are concrete ("X|" instead of "X..."),
     * apart from freshly introduced array dimensions (e.g. "Object..." to
     * "[Object..."). Beware that Object... is only expanded to [Object..., but
     * not [X|. You may need to call expand more than once or do some other
     * tricks.
     * @param cPath The considered class path for this analysis.
     * @return the set of fuzzy types described by this {@link AbstractType}
     */
    public Set<FuzzyType> expand(final ClassPath cPath, final JBCOptions options) {
        final Set<FuzzyType> res = new LinkedHashSet<>();
        for (final FuzzyType t : this.possibleClasses) {
            t.expand(res, cPath, options);
        }
        return res;
    }

    /**
     * @return Pair of integers, of which the first is the minimal array
     *  dimension of an array parent class type (jlO, Serializable, Cloneable)
     *  and the second is the maximal array dimension of any type.
     */
    private Pair<Integer, Integer> getArrayInfoFromType() {
        return AbstractType.getArrayInfoFromType(this.possibleClasses);
    }

    /**
     * @return the set of possible types that can be enclosed in an array of
     * this type
     * @param cPath The considered class path for this analysis.
     */
    public AbstractType getEnclosedTypes(final ClassPath cPath, final JBCOptions options) {
        if (this.enclosedType == null) {
            final Collection<FuzzyType> enclosedTypes = new LinkedHashSet<>();
            for (final FuzzyType t : this.possibleClasses) {
                enclosedTypes.add(t.getEnclosedType());
            }
            this.enclosedType = new AbstractType(cPath, options, enclosedTypes);
        }
        return this.enclosedType;
    }

    /**
     * @return the minimal ClassName if this type describes only a single class,
     *  otherwise null
     */
    public FuzzyClassType getMinimalClass() {
        if (this.possibleClasses.size() == 1) {
            for (final FuzzyType f : this.possibleClasses) {
                if (f instanceof FuzzyClassType && !f.isArrayType()) {
                    return ((FuzzyClassType) f);
                }
            }
        }
        return null;
    }

    /**
     * @param cPath The considered class path for this analysis.
     * @return Type constructed from this by making all concrete types
     *  non-concrete.
     */
    public AbstractType getNonConcreteTypes(final ClassPath cPath, final JBCOptions options) {
        final Collection<FuzzyType> enclosedNonConcreteTypes = new LinkedHashSet<FuzzyType>();
        for (final FuzzyType t : this.possibleClasses) {
            if (t instanceof FuzzyClassType) {
                final FuzzyClassType ct = (FuzzyClassType) t;
                enclosedNonConcreteTypes.add(new FuzzyClassType(ct.getMinimalClass(), false, ct.getArrayDimension()));
            } else {
                enclosedNonConcreteTypes.add(t);
            }
        }
        return new AbstractType(cPath, options, enclosedNonConcreteTypes);
    }

    /**
     * @return the set of possible fuzzy classes of this type as a new set
     */
    public Set<FuzzyType> getPossibleClassesCopy() {
        return new LinkedHashSet<>(this.possibleClasses);
    }

    /**
     * @return the primitive type if this type describes only a single primitive
     * type, otherwise null
     */
    public FuzzyPrimitiveType getPrimitiveType() {
        if (this.possibleClasses.size() == 1) {
            for (final FuzzyType f : this.possibleClasses) {
                if (f instanceof FuzzyPrimitiveType && !f.isArrayType()) {
                    return ((FuzzyPrimitiveType) f);
                }
            }
        }
        return null;
    }

    /**
     * @param that some other {@link AbstractType}
     * @param cPath The considered class path for this analysis.
     * @return true iff <code>this</code> and <code>that</code> have at least
     *  one type in common.
     */
    public boolean hasIntersectionWith(final AbstractType that, final ClassPath cPath, final JBCOptions options) {
        boolean thisIsJlO;
        boolean thatIsJlO;
        if (options.dontExpandTypeTree()) {
            thisIsJlO = this.isAbstractJLOLike();
            thatIsJlO = that.isAbstractJLOLike();
        } else {
            thisIsJlO = this.isAbstractJLO();
            thatIsJlO = that.isAbstractJLO();
        }
        if (thisIsJlO && that.containsReferenceType()) {
            return true;
        }
        if (thatIsJlO && this.containsReferenceType()) {
            return true;
        }

        // first try to find some common fuzzy type
        for (final FuzzyType ftThis : this.possibleClasses) {
            for (final FuzzyType ftThat : that.possibleClasses) {
                if (ftThis.equals(ftThat)) {
                    return true;
                }
            }
        }

        final Set<FuzzyType> thisTypeExpansion = this.expand(cPath, options);
        final Set<FuzzyType> thatTypeExpansion = that.expand(cPath, options);

        //Get the intersection:
        thisTypeExpansion.retainAll(thatTypeExpansion);
        if (!thisTypeExpansion.isEmpty()) {
            return true;
        }

        /*
         * This looks safe, but the type expansion doesn't actually
         * get all types: Array expansion is only done by one level.
         * If we are not sure yet, check if array types are
         * possibly involved:
         *
         * We now need to iterate over both sets to find
         * out the minimal array dimension of an array parent
         * type and the maximal array dimension of any type.
         *
         * Note that calling containsArrayParentType() does not
         * improve performance, as it does the same iteration
         * we need to gather our information:
         */
        final Pair<Integer, Integer> thisArrayInfo = this.getArrayInfoFromType();
        final Pair<Integer, Integer> thatArrayInfo = that.getArrayInfoFromType();

        /*
         * If the minimal array parent dim is smaller than the
         * maximal array dim in the other type, we can expand
         * the former to get the latter:
         */
        if (thisArrayInfo.getKey() < thatArrayInfo.getValue() || thatArrayInfo.getKey() < thisArrayInfo.getValue()) {
            return true;
        }
        return false;
    }

    /**
     * Replace X| by X... if all subtypes of X are part of this abstract type
     * (this is not done for final classes or types without subtypes). This
     * method works on the "typesGroupedByDimension" argument.
     * @param cPath The considered class path for this analysis.
     * @param typesGroupedByDimension this abstract type, grouped by array
     * dimensions
     * @param arrayDims the non-empty array dimensions, ordered
     */
    private static void introduceAbstraction(
        final ClassPath cPath,
        final JBCOptions options,
        final CollectionMap<Integer, FuzzyType> typesGroupedByDimension,
        final Integer[] arrayDims)
    {
        /*
         * Here we collect the types that can be disregarded during the
         * computation (we do not delete directly because of concurrent modification issues).
         */
        final Collection<FuzzyType> removeTypes = new LinkedHashSet<>();

        for (int i = 1; i <= arrayDims.length; i++) {
            final int dim = arrayDims[arrayDims.length - i];

            final Set<FuzzyType> newTypeCollection = new LinkedHashSet<>();

            for (final FuzzyType type : typesGroupedByDimension.get(dim)) {
                if (removeTypes.contains(type)) {
                    /*
                     * We already have X... for some super type X, so we do not
                     * need to have a closer look at this type.
                     */
                    continue;
                }
                if (type instanceof FuzzyPrimitiveType) {
                    // there are no subtypes and primitives cannot be abstract
                    newTypeCollection.add(type);
                    continue;
                }
                assert (type instanceof FuzzyClassType);
                final FuzzyClassType classType = (FuzzyClassType) type;

                // for final types we don't really need to look at subclasses
                final boolean isFinal = cPath.getClass(classType.getMinimalClass()).isEffectivelyFinal();
                if (isFinal) {
                    if (classType.isConcrete()) {
                        newTypeCollection.add(new FuzzyClassType(classType.getMinimalClass(), true, classType
                            .getArrayDimension()));
                    } else {
                        newTypeCollection.add(classType);
                    }
                    continue;
                }

                if (classType.isAbstract()) {
                    // we already have "X...", nothing to do in this step
                    newTypeCollection.add(classType);
                    continue;
                }
                assert (classType.isConcrete());

                /*
                 * Now we have X| but would like to replace this by X... We are
                 * allowed to do this, if all subtypes of X are included. For
                 * that, we create a set "typeExpansion" that includes all those
                 * subtypes. To test the inclusion, we also generate a set
                 * "otherTypes" that includes all types that we have (apart
                 * from X).
                 */

                //Set of types represented by type:
                final Set<FuzzyType> typeExpansion = new LinkedHashSet<>();
                AbstractType.expandAllPossibleTypes(classType, typeExpansion, cPath, options);

                /*
                 * note:
                 * typeExpansion of X| may be Y| if X is abstract and Y is the
                 * only implementation!
                 */
                if (typeExpansion.size() == 1 && typeExpansion.contains(classType)) {
                    // X does not have subtypes, so we are fine with X| and do not need X...
                    newTypeCollection.add(classType);
                    continue;
                }

                //Set of types represented by the rest of the types (all expansions of other
                //types of the same dimension + stuff from dim+1 in some cases):
                final Set<FuzzyType> otherTypes = new LinkedHashSet<>();
                AbstractType.expandOtherTypes(typesGroupedByDimension.get(dim), classType, otherTypes, cPath, options);

                /*
                 * For X in {java.lang.Object, java.io.Serializable,
                 * java.lang.Clonable} we can also create, for example,
                 * [...[int, so we need to consider that we can represent
                 * [...[int. This information is hidden in the set for the
                 * higher array dimension.
                 */

                /*
                 * We do not need to do the inclusion check, if [...[jlO... is
                 * needed, but not available.
                 */
                boolean inclusionPossible = true;

                if (classType.isArrayParentClass()) {
                    // only reset to true, if we have [...[jlO...
                    inclusionPossible = false;
                    for (final FuzzyType nextDimType : typesGroupedByDimension.getNotNull(dim + 1)) {
                        if (nextDimType instanceof FuzzyPrimitiveType) {
                            otherTypes.add(nextDimType);
                        } else if (!inclusionPossible && nextDimType instanceof FuzzyClassType) {
                            final FuzzyClassType nextDimClassType = (FuzzyClassType) nextDimType;
                            if (nextDimClassType.getMinimalClass().equals(JAVA_LANG_OBJECT.getClassName())
                                && nextDimClassType.isAbstract())
                            {
                                inclusionPossible = true;
                                otherTypes.add(nextDimType);
                            }
                        }
                    }
                }

                //If this is a concrete class type, but all of it's subtypes are included,
                //we replace it by it's abstract variant.
                typeExpansion.remove(classType);
                if (inclusionPossible && otherTypes.containsAll(typeExpansion)) {
                    //Add a copy of classType, indicating that children are allowed
                    newTypeCollection.add(new FuzzyClassType(classType.getMinimalClass(), false, classType
                        .getArrayDimension()));

                    /*
                     * The new type (X...) already represents all types in
                     * typeExpansion, so we do not need to keep them (or try to
                     * compress them).
                     */
                    removeTypes.addAll(typeExpansion);
                } else {
                    newTypeCollection.add(classType);
                }
            }
            newTypeCollection.removeAll(removeTypes);
            typesGroupedByDimension.put(dim, newTypeCollection);
        }
    }

    /**
     * Check if this type can be cast to the class in question. This only checks
     * reference types and must not be called for primitive types!
     * @param checkedTypes abstract type to check
     * @param cPath The considered class path for this analysis.
     * @return true iff the checkedType is assignment compatible to all types
     * described by this {@link AbstractType}, false if it is not, and NULL if
     * some types are assignment compatible and some aren't.
     */
    public Boolean isAssignmentCompatibleTo(final AbstractType checkedTypes, final ClassPath cPath) {
        Boolean result = null;
        for (final FuzzyType checkedType : checkedTypes.possibleClasses) {
            final Boolean subResult = this.isAssignmentCompatibleTo(checkedType, cPath);
            if (subResult == null) {
                // no clue for at least one of the fuzzy types
                return null;
            }
            if (result == null) {
                // first answer
                result = subResult;
            } else {
                //The answers are mixed, we can't decide => return NULL:
                if (result.booleanValue() != subResult) {
                    return null;
                }
            }
        }
        return result;
    }

    /**
     * Check if this type can be cast to the class in question. This only checks
     * reference types and must not be used for primitive types!
     * @param checkedType type to check
     * @param cPath The considered class path for this analysis.
     * @return true iff the checkedType is assignment compatible to all types
     * described by this {@link AbstractType}, false if it is not, and NULL if
     * some types are assignment compatible and some aren't.
     */
    public Boolean isAssignmentCompatibleTo(final FuzzyType checkedType, final ClassPath cPath) {
        Boolean result = null;
        for (final FuzzyType subjectType : this.possibleClasses) {
            final Boolean subResult = subjectType.isAssignmentCompatibleTo(checkedType, cPath);
            if (subResult == null) {
                return null;
            }
            if (result == null) {
                result = subResult;
            } else {
                //The answers are mixed, we can't decide => return NULL:
                if (!result.equals(subResult)) {
                    return null;
                }
            }
        }
        return result;
    }

    /**
     * @return true iff this abstract type represents a single concrete type
     */
    public boolean isConcrete() {
        if (this.possibleClasses.size() > 1) {
            return false;
        }
        final FuzzyType fT = this.possibleClasses.iterator().next();
        return fT.isConcrete();
    }

    /**
     * Check if the this type can be stored in an array of type <code>arrayType</code>.
     * @param arrayType abstract type of an array in which an element of type
     *  <code>this</code> should be stored.
     * @param cPath The considered class path for this analysis.
     * @return true iff an object of this type can be stored in an array of type
     *  <code>arrayType</code>, false if it is not, and NULL if some types can
     *  and some can't.
     */
    public Boolean isStorageCompatibleTo(final AbstractType arrayType, final ClassPath cPath, final JBCOptions options) {
        /* Trick: Construct an array out of value type and check if
         * that type is assignment compatible to the array type. If not,
         * we need to throw an ArrayStoreException. The algorithm is the
         * same. */
        final Set<FuzzyType> valueArrayTypes = new LinkedHashSet<>(this.possibleClasses.size());

        //the value is a non-primitive:
        for (final FuzzyType f : this.possibleClasses) {
            final FuzzyType arrayedF;
            if (f instanceof FuzzyClassType) {
                final FuzzyClassType fClassT = (FuzzyClassType) f;
                arrayedF =
                    new FuzzyClassType(fClassT.getMinimalClass(), fClassT.isConcrete(), fClassT.getArrayDimension() + 1);
            } else {
                final FuzzyPrimitiveType fPrimT = (FuzzyPrimitiveType) f;
                arrayedF = new FuzzyPrimitiveType(fPrimT.getInnermostType().getPrimitiveType(), fPrimT.getArrayDimension() + 1);
            }
            valueArrayTypes.add(arrayedF);
        }
        final AbstractType valueArrayType = new AbstractType(cPath, options, valueArrayTypes);

        /*
         * If some array of the value type is not assignment compatible to
         * arrayType, then the value cannot be stored to that array.
         */
        return valueArrayType.isAssignmentCompatibleTo(arrayType, cPath);
    }

    /**
     * @param cPath The considered class path for this analysis.
     * @return the maximal common supertype of all types collected in this {@link AbstractType}
     */
    public FuzzyType maximalCommonSupertype(final ClassPath cPath) {
        FuzzyType res = null;
        for (final FuzzyType f : this.possibleClasses) {
            if (res == null) {
                res = f;
            } else {
                res = AbstractType.maximalCommonSupertype(cPath, res, f);
            }
        }
        return res;
    }

    /**
     * @return a nice string representation
     */
    @Override
    public String toString() {
        final StringBuilder sb = new StringBuilder();
        this.toString(sb);
        return sb.toString();
    }

    /**
     * Writes a nice string representation to the argument {@link StringBuilder};
     * @param sb some {@link StringBuilder} to write to
     */
    public void toString(final StringBuilder sb) {
        if (this.possibleClasses.size() > 1) {
            sb.append("{");
        }
        boolean notFirst = false;
        int count = 0;
        final int limit = 5;
        for (final FuzzyType f : this.possibleClasses) {
            if (notFirst) {
                sb.append(", ");
            } else {
                notFirst = true;
            }
            if (count > limit && !Globals.DEBUG_NONE) {
                sb.append(" [omitted " + (this.possibleClasses.size() - limit) + " types]");
                break;
            }
            f.toString(sb);
            count++;
        }
        if (this.possibleClasses.size() > 1) {
            sb.append("}");
        }
    }

    /**
     * Take all the fuzzy types out of the given subtypes and create an abstract
     * type as the union out of that.
     * @param cPath The considered class path for this analysis.
     * @param subTypes some abstract types
     * @return the new abstract type
     */
    public static AbstractType union(final ClassPath cPath, final JBCOptions options, final AbstractType... subTypes) {
        final Set<FuzzyType> possibleClasses = new LinkedHashSet<>();
        assert (subTypes.length > 0);
        for (final AbstractType at : subTypes) {
            possibleClasses.addAll(at.possibleClasses);
        }
        final AbstractType result = new AbstractType(cPath, options, possibleClasses);
        return result;
    }

    /**
     * Take all the fuzzy types out of the given subtypes and create an abstract
     * type as the union out of that.
     * @param cPath The considered class path for this analysis.
     * @param subTypes some abstract types
     * @return the new abstract type
     */
    public static AbstractType union(final ClassPath cPath, final JBCOptions options, final Collection<AbstractType> subTypes) {
        final Set<FuzzyType> possibleClasses = new LinkedHashSet<>();
        assert (!subTypes.isEmpty());
        for (final AbstractType at : subTypes) {
            possibleClasses.addAll(at.possibleClasses);
        }
        final AbstractType result = new AbstractType(cPath, options, possibleClasses);
        return result;
    }

    /**
     * Take all the fuzzy types out of the given subtypes and create an abstract type as the intersection out of that.
     * @param cPath The considered class path for this analysis.
     * @param subTypes some abstract types
     * @return the new abstract type or <code>null</code> if the intersection is empty
     */
    public static AbstractType intersection(final ClassPath cPath, final JBCOptions options, final List<AbstractType> subTypes) {
        return AbstractType.intersection(cPath, options, subTypes.toArray(new AbstractType[subTypes.size()]));
    }

    /**
     * Take all the fuzzy types out of the given subtypes and create an abstract type as the intersection out of that.
     * @param cPath The considered class path for this analysis.
     * @param subTypes some abstract types
     * @return the new abstract type or <code>null</code> if the intersection is empty
     */
    public static AbstractType intersection(final ClassPath cPath, final JBCOptions options, final AbstractType... subTypesArg) {
        final AbstractType typeCur = subTypesArg[0];
        boolean areEqual = true;
        // do not try to expand the whole type hierarchy...
        FuzzyType fuzzyJlo = FuzzyClassType.FT_JAVA_LANG_OBJECT.toAbstract();
        AbstractType jlo = new AbstractType(cPath, fuzzyJlo);
        List<AbstractType> subTypes = Arrays.asList(subTypesArg).stream().filter(x -> !x.equals(jlo)).collect(toList());
        if (subTypes.isEmpty()) {
            return jlo;
        }
        if (options.avoidExpandingTypeTree()) {
            Set<FuzzyType> allTypes = subTypes.stream().flatMap(x -> x.getPossibleClassesCopy().stream()).collect(toSet());
            while (allTypes.stream().anyMatch(x -> x.isArrayType())) {
                allTypes = allTypes.stream().map(x -> x.isArrayType() ? x.getEnclosedType() : x).collect(toSet());
            }
            if (allTypes.contains(fuzzyJlo)) {
                return typeCur;
            }
        }
        for (final AbstractType type : subTypes) {
            if (!type.equals(typeCur)) {
                areEqual = false;
                break;
            }
        }
        if (areEqual) {
            return typeCur;
        }
        final int length = subTypes.size();
        if (length < 1) {
            throw new IllegalArgumentException();
        }
        /*
         * Outline:
         * 1 Get maximum dimension
         * 2 Expand every type
         * 3 Intersect the expansions
         * 4 Compress
         * 5 Return
         */

        // 1
        final int[] maxDims = new int[length];
        int maxDim = -1;
        for (int i = 0; i < length; i++) {
            final AbstractType subType = subTypes.get(i);
            assert (subType != null);
            for (final FuzzyType fuzzyType : subType.possibleClasses) {
                final int currentDim = fuzzyType.getArrayDimension();
                if (currentDim > maxDims[i]) {
                    maxDims[i] = currentDim;
                }
                if (currentDim > maxDim) {
                    maxDim = currentDim;
                }
            }
        }

        if (Globals.useAssertions) {
            assert maxDim > -1;
        }

        // 2 Expand them
        @SuppressWarnings("unchecked")
        final Set<FuzzyType>[] copies = new Set[length];
        for (int i = 0; i < length; i++) {
            final Set<FuzzyType> copy = subTypes.get(i).getPossibleClassesCopy();
            copies[i] = copy;
            for (int d = 0; d <= maxDim + 1; d++) {
                AbstractType.expand(cPath, options, copy);
            }
        }

        // 3 Intersect them
        final Set<FuzzyType> intersection = new LinkedHashSet<>(copies[0]);
        for (int i = 1; i < length; i++) {
            intersection.retainAll(copies[i]);
        }

        // 3.5 Check for empty result
        if (intersection.isEmpty()) {
            return null;
        }

        // 4 Compress them
        final AbstractType result = new AbstractType(cPath, options, intersection);
        // 5 Return
        return result;
    }

    /**
     * Expand every {@link FuzzyType} in types, and add the result back to
     * types. All added types are <strong>abstract</strong> (unless their
     * represented class has no subtypes).
     * @param cPath The considered class path for this analysis.
     * @param types
     */
    private static void expand(final ClassPath cPath, final JBCOptions options, final Set<FuzzyType> types) {
        final Set<FuzzyType> result = new LinkedHashSet<>();
        for (final FuzzyType type : types) {
            type.expand(result, cPath, options);
        }
        for (final FuzzyType type : result) {
            if (types.contains(type)) {
                continue;
            } else if (type instanceof FuzzyPrimitiveType) {
                types.add(type);
            } else if (type instanceof FuzzyClassType) {
                final FuzzyClassType classType = (FuzzyClassType) type;
                if (classType.isAbstract()) {
                    types.add(classType);
                } else {
                    types.add(classType.toAbstract());
                    // We also want the concrete version.
                    types.add(classType);
                }
            } else {
                assert false : "Class hierarchy of FuzzyType changed unexpected.";
            }
        }
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public int hashCode() {
        final int prime = 31;
        int result = 1;
        result = prime * result + ((this.possibleClasses == null) ? 0 : this.possibleClasses.hashCode());
        return result;
    }

    /**
     * {@inheritDoc}
     */
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
        final AbstractType other = (AbstractType) obj;
        if (this.possibleClasses == null) {
            if (other.possibleClasses != null) {
                return false;
            }
        } else if (!this.possibleClasses.equals(other.possibleClasses)) {
            return false;
        }
        return true;
    }

    /**
     * @return true iff this type contains java.lang.String.
     */
    public boolean containsStringType() {
        for (final FuzzyType ft : this.possibleClasses) {
            if (ft instanceof FuzzyPrimitiveType || ft.getArrayDimension() > 0) {
                continue;
            }
            final FuzzyClassType fct = (FuzzyClassType) ft;
            final ClassName cn = fct.getMinimalClass();
            if (cn.equals(Important.JAVA_LANG_STRING.getClassName())) {
                return true;
            } else if (fct.isAbstract()) {
                if (cn.equals(Important.JAVA_LANG_OBJECT.getClassName())) {
                    return true;
                } else if (cn.equals(Important.JAVA_IO_SERIALIZABLE.getClassName())) {
                    return true;
                } else if (cn.equals(Important.JAVA_LANG_CHARSEQUENCE.getClassName())) {
                    return true;
                } else if (cn.equals(Important.JAVA_LANG_COMPARABLE.getClassName())) {
                    return true;
                }
            }
        }
        return false;
    }

    /**
     * @return true iff this type contains java.lang.Class.
     */
    public boolean containsClassType() {
        for (final FuzzyType ft : this.possibleClasses) {
            if (ft instanceof FuzzyPrimitiveType || ft.getArrayDimension() > 0) {
                continue;
            }
            final FuzzyClassType fct = (FuzzyClassType) ft;
            final ClassName cn = fct.getMinimalClass();
            if (cn.equals(Important.JAVA_LANG_CLASS.getClassName())) {
                return true;
            } else if (fct.isAbstract()) {
                if (cn.equals(Important.JAVA_LANG_OBJECT.getClassName())) {
                    return true;
                } else if (cn.equals(Important.JAVA_IO_SERIALIZABLE.getClassName())) {
                    return true;
                } else if (cn.equals(Important.JAVA_LANG_REFLECT_ANNOTATEDELEMENT.getClassName())) {
                    return true;
                } else if (cn.equals(Important.JAVA_LANG_REFLECT_GENERICDECLARATION.getClassName())) {
                    return true;
                } else if (cn.equals(Important.JAVA_LANG_REFLECT_TYPE.getClassName())) {
                    return true;
                }
            }
        }
        return false;
    }

    /**
     * @return true only if this AbstracType describes all types (jlO...)
     */
    public boolean isAbstractJLO() {
        FuzzyType jlo = FuzzyClassType.FT_JAVA_LANG_OBJECT.toAbstract();
        return possibleClasses.contains(jlo);
    }

    /**
     * @return true only if this AbstracType describes all types (jlO...) or a corresponding array type ([jlO..., [[jlO..., etc.)
     */
    public boolean isAbstractJLOLike() {
        FuzzyType jlo = FuzzyClassType.FT_JAVA_LANG_OBJECT.toAbstract();
        for (FuzzyType t: possibleClasses) {
            if (t.isArrayType()) {
                t = t.getInnermostType();
            }
            if (jlo.equals(t)) {
                return true;
            }
        }
        return false;
    }
}
