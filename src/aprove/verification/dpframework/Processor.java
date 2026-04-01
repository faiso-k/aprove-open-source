/*
 * Created on 13.04.2005
 */
package aprove.verification.dpframework;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.oldframework.IntTRS.SafetyRedPair.Tools.Debug.*;


/**
 * Implementors are required to be thread-safe. This means that they
 * must not have any attributes that are obligation-dependent.
 * However, attributes that store information regarding the processor
 * configuration are allowed.
 *
 * This can be accomplished in several ways:
 *
 * 1) Do not use global attributes to store obligation-dependent
 *    information, but use local variables instead.
 *
 * 2) In case 1) would cause too many problems, you can wrap the
 *    actual computation inside objects of an inner class instead.
 *    Then, the inner class can hold such global information.
 *
 * Reason:
 * There are processors that output several obligations that all have
 * to be fulfilled (e.g. the one that computes the Dependency Graph).
 * Then, there is only one instance of the next Processor for all
 * obligations (the same config is used for all obligations at this
 * point of execution, so it was decided that only a single instance
 * be created instead of several ones that would have held the same
 * config info). This instance can then be accessed by several
 * threads, possibly concurrently.
 *
 * @version $Id$
 */
public interface Processor {

    /**
     * Computes the result of this processor applied on obl.
     * @param obl - the basic obligation that should be processed
     * @param oblNode - the position of the basic obligation in the obligation tree
     * @param aborter - the aborter, that should be checked many times against timeouts/aborts, ...
     * @param rti - the runtime information should only be used to build new executable strategies
     *              for the result. This information can be ignored for all processors that deliver
     *              only Success or Fail as resulting strategies.
     *
     * @return the result of this processor
     * @throws AbortionException
     */
    Result process(BasicObligation obl, BasicObligationNode oblNode, Abortion aborter, RuntimeInformation rti) throws AbortionException;

    /**
     * this is a short test whether this processor can in general handle this
     * kind of basic obligation. This information will be used for two things.
     * First, if the processor says that it is not applicable, it will not be tried with process.
     * (Hence, all input passed to process will be checked with isApplicable)
     * Second, in an interactive mode, this method can be used to determine which
     * processors may be applied to the currently selected obligation.
     */
    boolean isApplicable(BasicObligation obl);

    abstract class ProcessorSkeleton implements Processor {
        protected ProcessorSkeleton() {
            Log.report(Thread.currentThread().getStackTrace()[2].getClassName(), "");
        }

        // There used to be implementations of interface methods here.
        // They have been moved since.

        /**
         * This method has been removed.
         *
         * Do not call. Do not override/implement.
         * This placeholder will disappear soon.
         *
         * Processors are no longer responsible for tracking their own name.
         * @param length unused.
         */
        @Deprecated
        public final Exportable getDescription(final NameLength length) {
            throw new UnsupportedOperationException("Method going away!");
        }
    }

}
