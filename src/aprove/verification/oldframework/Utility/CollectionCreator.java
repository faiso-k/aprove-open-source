package aprove.verification.oldframework.Utility;

import java.lang.reflect.Constructor;
import java.lang.reflect.InvocationTargetException;
import java.util.*;

public interface CollectionCreator<T, C extends Collection<T>> {
    C create();
    C create(Collection<T> collection);

    //interface ends here, anything below are some standard implementations

    //Implementations for all the common collections, due to erasure defining one per collection is enough, but we need to suppress some warnings
    @SuppressWarnings("rawtypes")
    CollectionCreator LINKED_LIST = new CollectionCreator () {
        @Override
        public Collection create() {return new LinkedList();}
        @SuppressWarnings("unchecked")
        @Override
        public Collection create(Collection collection) {return new LinkedList(collection);}
    };

    @SuppressWarnings("rawtypes")
    CollectionCreator ARRAY_LIST = new CollectionCreator () {
        @Override
        public Collection create() {return new ArrayList();}
        @SuppressWarnings("unchecked")
        @Override
        public Collection create(Collection collection) {return new ArrayList(collection);}
    };

    @SuppressWarnings("rawtypes")
    CollectionCreator HASH_SET = new CollectionCreator () {
        @Override
        public Collection create() {return new HashSet();}
        @SuppressWarnings("unchecked")
        @Override
        public Collection create(Collection collection) {return new HashSet(collection);}
    };

    @SuppressWarnings("rawtypes")
    CollectionCreator LINKED_HASH_SET = new CollectionCreator () {
        @Override
        public Collection create() {return new LinkedHashSet<>();}
        @SuppressWarnings("unchecked")
        @Override
        public Collection create(Collection collection) {return new LinkedHashSet(collection);}
    };

    @SuppressWarnings("rawtypes")
    CollectionCreator CONCURRENT_HASH_SET = new CollectionCreator () {
        @Override
        public Collection create() {return Collection_Util.createConcurrentHashSet();}
        @SuppressWarnings("unchecked")
        @Override
        public Collection create(Collection collection) {return Collection_Util.createConcurrentHashSet(collection);}
    };

    //now some typed static methods to access them without warnings
    @SuppressWarnings("unchecked")
    static <T>CollectionCreator<T, LinkedList<T>> linkedList() {return LINKED_LIST;}
    @SuppressWarnings("unchecked")
    static <T>CollectionCreator<T, ArrayList<T>> arrayList() {return ARRAY_LIST;}
    @SuppressWarnings("unchecked")
    static <T>CollectionCreator<T, HashSet<T>> hashSet() {return HASH_SET;}
    @SuppressWarnings("unchecked")
    static <T>CollectionCreator<T, LinkedHashSet<T>> linkedHashSet() {return LINKED_HASH_SET;}
    @SuppressWarnings("unchecked")
    static <T>CollectionCreator<T, ? extends Set<T>> concurrentHashSet() {return CONCURRENT_HASH_SET;}

    //reflection based implementation
    class ByReflection<T, C extends Collection<T>> implements CollectionCreator<T, C> {
        /**
         * The class used to construct the collection.
         */
        private Constructor<C> emptyConstructor;
        private Constructor<C> collectionConstructor;

        public ByReflection(Class<C> collectionType) throws NoSuchMethodException, SecurityException {
            this.emptyConstructor = collectionType.getConstructor(); //must exist, otherwise throw
            try {
                this.collectionConstructor = collectionType.getConstructor(Collection.class);
            } catch (NoSuchMethodException | SecurityException e) {
                this.collectionConstructor = null; //we can use a work around
            }
        }

        @Override
        public C create() {
            try {
                return emptyConstructor.newInstance();
            } catch (InstantiationException | IllegalAccessException | IllegalArgumentException | InvocationTargetException e) {
                throw new RuntimeException(e);
            }
        }

        @Override
        public C create(Collection<T> collection) {
            if (collectionConstructor == null) {
                C result = create();
                result.addAll(collection);
                return result;
            } else {
                try {
                    return collectionConstructor.newInstance(collection);
                } catch (InstantiationException | IllegalAccessException | IllegalArgumentException | InvocationTargetException e) {
                    throw new RuntimeException(e);
                }
            }
        }

        @Override
        public int hashCode() {
            final int prime = 31;
            int result = 1;
            result = prime * result + ((collectionConstructor == null) ? 0 : collectionConstructor.hashCode());
            result = prime * result + ((emptyConstructor == null) ? 0 : emptyConstructor.hashCode());
            return result;
        }

        @SuppressWarnings("rawtypes")
        @Override
        public boolean equals(Object obj) {
            if (this == obj)
                return true;
            if (obj == null)
                return false;
            if (getClass() != obj.getClass())
                return false;
            ByReflection other = (ByReflection) obj;
            if (collectionConstructor == null) {
                if (other.collectionConstructor != null)
                    return false;
            } else if (!collectionConstructor.equals(other.collectionConstructor))
                return false;
            if (emptyConstructor == null) {
                if (other.emptyConstructor != null)
                    return false;
            } else if (!emptyConstructor.equals(other.emptyConstructor))
                return false;
            return true;
        }
    }
}