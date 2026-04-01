package aprove.strategies.ExecutableStrategies;

import java.util.*;

import aprove.prooftree.Obligations.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.ExecutableStrategies.impl.*;
import aprove.strategies.Parameters.*;
import aprove.strategies.UserStrategies.*;

public interface Machine {
    /**
     * starts execution of given strategy on several ObligationNodes
     *
     * Only those parameters explicitly allowed here to be null can be null,
     * but probably should if you don't have anything useful for them.
     *
     * @param strategy if null, the value of strategy variable "main" is used from program
     * @param program source for strategy variables - may be null if strategy contains no variables
     * @param positions the ObligationNodes we should start on
     * @param metadata extra information that may be used by processors - may be null
     */
    public StrategyExecutionHandle start(
        UserStrategy strategy,
        StrategyProgram program,
        List<BasicObligationNode> positions,
        Map<Metadata, Object> metadata);

    /**
     * starts execution of given strategy on a single ObligationNode from inside a processor
     *
     * Only those parameters explicitly allowed here to be null can be null,
     * but probably should if you don't have anything useful for them.
     *
     * Note: If you want to stop the (sub)machine, run handle.stop. If you want the (sub)machine to stop after some
     * (CPU)time, just provide a corresponding clock and, when it rings, call handle.stop. If you want the submachine if
     * some outer abortion throws an AbortionException, check for that exception and call handle.stop.
     *
     * @param strategy if null, the value of strategy variable "main" is used from program
     * @param program source for strategy variables - may be null if strategy contains no variables
     * @param position the single ObligationNode we should start on
     * @param metadata extra information that may be used by processors - may be null
     * @param clocks the clocks to account our CPU time to
     * @param checkProofs should proofs be checked, if online certification is enabled
     */
    public StrategyExecutionHandle startSubMachine(
        UserStrategy strategy,
        StrategyProgram program,
        BasicObligationNode position,
        Map<Metadata, Object> metadata,
        List<Clock> clocks,
        boolean checkProofs);

    /**
     * starts execution of given strategy on several ObligationNodes from inside a processor
     *
     * Only those parameters explicitly allowed here to be null can be null,
     * but probably should if you don't have anything useful for them.
     *
     * @param strategy if null, the value of strategy variable "main" is used from program
     * @param program source for strategy variables - may be null if strategy contains no variables
     * @param positions the ObligationNodes we should start on
     * @param metadata extra information that may be used by processors - may be null
     * @param clocks the clocks we should account our CPU time to
     * @param checkProofs should proofs be checked, if online certification is enabled
     */
    public StrategyExecutionHandle startSubMachine(
        UserStrategy strategy,
        StrategyProgram program,
        List<BasicObligationNode> positions,
        Map<Metadata, Object> metadata,
        List<Clock> clocks,
        boolean checkProofs);

    /**
     * stops all currently executed strategies.
     * Note that after the stopAll command, new strategies may be started!
     * @param reason must be non null
     */
    public void stopAll(String reason);

    public static final Machine theMachine = new DefaultMachine();
}
