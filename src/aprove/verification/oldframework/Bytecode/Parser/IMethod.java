package aprove.verification.oldframework.Bytecode.Parser;

import java.util.*;

import org.json.*;

import aprove.input.Programs.jbc.*;
import aprove.verification.oldframework.Bytecode.*;
import aprove.verification.oldframework.Bytecode.Utils.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

public interface IMethod extends HasAccessFlags {

    /**
     * Returns an over-approximation of the methods which are possibly called by
     * this method. This includes only directly called methods, i.e, no
     * recursion. Furthermore, calls to initializers of exceptions thrown by the
     * JVM are not returned. The same holds for all class initializers.
     * @return possibly local called methods
     */
    Set<Pair<Integer, MethodIdentifier>> getLocalMethodCalls();

    /**
     * @return transitive closure of methods called by this method
     */
    Collection<MethodIdentifier> getMethodCallsRecursively();

    /**
     * @return true if a rough approximation of the call graph indicates that
     *  this method may eventually call itself.
     */
    boolean isRecursive();

    /**
     * @param methodId some method identifier
     * @return number of calls to code <param>methodId</param>
     */
    int getNumberOfMethodCalls(MethodIdentifier methodId);

    /**
     * @return number of non-constructor method calls in a method.
     */
    int getNumberOfMethodCalls();

    /**
     * @return number of goto instructions in a method (usually corresponding
     *  to number of loops).
     */
    int getNumberOfLoops();

    /**
     * @return number of calls that occur in loop-like constructs.
     */
    int getNumberOfCallsInLoops();

    /**
     * @return number of !goto jump instructions in a method (usually
     *  corresponding to number of if/else constructs).
     */
    int getNumberOfBranches();

    /**
     * @return true if a method writes to objects
     */
    boolean writesObjects();

    /**
     * @return true if a method reads to objects
     */
    boolean readsObjects();

    /**
     * @return true if a method contains an int in something that looks like
     *  a loop condition.
     */
    boolean hasIntLoop();

    /**
     * @return true if a method from a class called Random is called.
     */
    boolean usesRandom();

    /**
     * @param pos some instruction position in the method
     * @return true if we suspect that this position is part of a loop body.
     */
    boolean isInLoop(int pos);

    /**
     * @return Parsed descriptor of this method
     */
    ParsedMethodDescriptor getDescriptor();

    /**
     * @return Name of the method.
     */
    String getName();

    /**
     * @return The maximal length of the local variable array in this method.
     */
    int getVarArrayLength();

    /**
     * @return The maximal height of the operand stack in this method.
     */
    int getOpStackHeight();

    /**
     * @return Name of the enclosing class.
     */
    @Override
    ClassName getClassName();

    /**
     * @return unique method identifier of this method.
     */
    MethodIdentifier getMethodIdentifier();

    default FuzzyType getReturnType() {
        return getMethodIdentifier().getDescriptor().getReturnType();
    }

    /**
     * @return Parsed representation of the enclosing class.
     */
    IClass getIClass();

    /**
     * @param index Some bytecode index.
     * @return the Opcode at that index in the opcode table.
     */
    OpCode getOpcodeAt(int index);

    /**
     * @return the first opcode of this method.
     */
    OpCode getStart();

    /**
     * @return String representation of all opcodes in this method.
     */
    public default String getCodeString() {
        final StringBuilder r = new StringBuilder();
        OpCode t = this.getStart();
        while (t != null) {
            r.append((t.getPos() + 1) + ": " + t.toString() + "\n");
            t = t.getNextOp();
        }
        return r.toString();
    }

    /**
     * @param localVarIndex Some index in the local variable array
     * @param position Some position in the bytecode array
     * @return the name stored in the debug information for this method, if
     * available. NULL otherwise.
     */
    String getLocalVariableName(int localVarIndex, int position);

    /**
     * @param position Some bytecode position.
     * @return A list of local variable registers which are in use at <code>
     *  position</code>
     * .
     */
    public default Collection<Integer> getActiveVariables(final int position) {
        final Collection<Integer> ret = new LinkedList<>();
        for (int i = 0; i < this.getVarArrayLength(); i++) {
            if (variableUsedAt(i, position)) {
                ret.add(i);
            }
        }
        return ret;
    }

    boolean variableUsedAt(int varIndex, int pos);

    /**
     * @return true iff this method is marked as static
     */
    @Override
    boolean isStatic();

    /**
     * @return true iff this method is marked as strictfp
     */
    boolean isStrictFP();

    /**
     * @return true iff this method is marked as synchronized
     */
    boolean isSynchronized();

    /**
     * @return true iff this method is marked as native
     */
    boolean isNative();

    /**
     * @return true iff this method is marked as abstract.
     */
    boolean isAbstract();

    /**
     * @return true iff this method is marked as final.
     */
    boolean isFinal();

    /**
     * @return true iff this method is marked as protected.
     */
    @Override
    boolean isProtected();

    /**
     * @return true iff this method is marked as private.
     */
    @Override
    boolean isPrivate();

    /**
     * @return true iff this method is marked as public.
     */
    @Override
    boolean isPublic();

    /**
     * @return true iff this method is not marked with an access flag (public
     * etc.)
     */
    boolean isDefaultAccess();

    /**
     * @return true iff this method is some instance initializer
     */
    boolean isInstanceInitializer();

    /**
     * @return true iff this method is the class initializer
     */
    boolean isClassInitializer();

    /**
     * @return a human readable string describing this method
     */
    @Override
    String toString();

    /**
     * This will create a shortest identifier for this method.
     * @return
     */
    default String toShortestIdentifier(ClassPath cPath) {
        final boolean defaultPackage = getClassName().getPkgName().length() == 0;
        final boolean nameUnique;
        final boolean nameArgUnique;
        final boolean classNameUnique;
        final boolean classNameArgUnique;
        boolean packageClassNameUnique = true;
        if (cPath == null) {
            // We don't know which classes exist.
            // Assume worst case, which means we need package + class
            // Since we will include the method name always,
            // the only remaining question are the arguments
            nameUnique = false;
            nameArgUnique = false;
            classNameUnique = false;
            classNameArgUnique = false;

            // Check for name unique in this class
            boolean nameFound = false;
            for (final IMethod parsedMethod : getIClass().getMethods()) {
                if (parsedMethod.getName().equals(this.getName())) {
                    if (!nameFound) {
                        nameFound = true;
                    } else {
                        packageClassNameUnique = false;
                        break;
                    }
                }
            }
        } else {
            int nameFound = 0;
            int classNameFound = 0;
            int nameArgFound = 0;
            int classNameArgFound = 0;
            int packageClassNameFound = 0;

            // Loop over every class in the program
            for (final ClassName className : cPath.getClasses()) {
                final IClass pClass = cPath.getClass(className);
                final String currentClassName = className.getClassName();
                final String thisClassName = this.getClassName().getClassName();
                final boolean sameClass = currentClassName.equals(thisClassName);
                final String currentPackage = className.getPkgName('.');
                final String thisPackage = this.getClassName().getPkgName('.');
                final boolean samePackage = currentPackage.equals(thisPackage);
                // Loop over every method in the class
                for (final IMethod parsedMethod : pClass.getMethods()) {
                    // Check whether each part is the same as this
                    final boolean sameName = parsedMethod.getName().equals(this.getName());
                    final String currentArgs = parsedMethod.getDescriptor().toString();
                    final String thisArgs = this.getDescriptor().toString();
                    final boolean sameArgs = currentArgs.equals(thisArgs);
                    // Count combinations of matching
                    if (sameName) {
                        nameFound++;
                    }
                    if (sameClass && sameName) {
                        classNameFound++;
                    }
                    if (sameName && sameArgs) {
                        nameArgFound++;
                    }
                    if (sameClass && sameName && sameArgs) {
                        classNameArgFound++;
                    }
                    if (samePackage && sameClass && sameName) {
                        packageClassNameFound++;
                    }
                }
            }
            assert nameFound > 0;
            nameUnique = nameFound == 1;
            assert classNameFound > 0;
            classNameUnique = classNameFound == 1;
            assert nameArgFound > 0;
            nameArgUnique = nameArgFound == 1;
            assert classNameArgFound > 0;
            classNameArgUnique = classNameArgFound == 1;
            assert packageClassNameFound > 0;
            packageClassNameUnique = packageClassNameFound == 1;
        }

        // Now return based on what is unique
        final String name = this.getName();
        if (nameUnique) {
            return name;
        }
        final String desc = this.getDescriptor().toString();
        if (nameArgUnique) {
            return name + desc;
        }
        final String className = this.getClassName().getClassName() + ".";
        if (classNameUnique) {
            return className + name;
        }
        if (classNameArgUnique) {
            return className + name + desc;
        }
        final String packageName = defaultPackage ? "" : this.getClassName().getPkgName('.') + ".";
        if (packageClassNameUnique) {
            return packageName + className + name;
        }
        return packageName + className + name + desc;
    }

    /**
     * @return true if this is a method "public static void main(String[] args)"
     */
    boolean isMain();

    /**
     * @return true if this method is signature polymorphic according to JVMS 2.9
     */
    boolean isSignaturePolymorphic();

    /**
     * @return true iff the ACC_VARARGS flag is set
     */
    boolean isVarArgs();

    JSONObject toJSON() throws JSONException;

    void dumpMethodInfo(String fileName);

    void setAccessible(ClassName containingClass);

}
