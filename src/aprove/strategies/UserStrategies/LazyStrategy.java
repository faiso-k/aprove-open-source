package aprove.strategies.UserStrategies;

import java.io.*;
import java.util.*;
import java.util.logging.*;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.strategies.Parameters.*;
import aprove.strategies.Util.*;
import aprove.verification.dpframework.*;

public class LazyStrategy extends UserStrategy implements EagerlyCheckable {
    private static final Logger LOG = Logger.getLogger(LazyStrategy.class.getName());

    private final FuncValue fromStrategy;

    private UserStrategy backend = null;
    private Exception failure = null;

    public LazyStrategy(FuncValue value) {
        this.fromStrategy = value;
    }

    @Override
    public void check(StrategyProgram program) {
        this.init(program);
        if (this.failure != null) {
            program.reportProblem(this.errorAsString());
        }
        List<UserStrategy> subStrategies = this.fromStrategy.getParams().getSubStrategies();
        if (subStrategies != null) {
            for(UserStrategy sub: subStrategies) {
                if (sub instanceof EagerlyCheckable) {
                    ((EagerlyCheckable)sub).check(program);
                }
            }
        }
    }

    @Override
    public String export(Export_Util o) {
        return o.escape(this.fromStrategy.toString());
    }

    @Override
    public ExecutableStrategy getExecutableStrategy(BasicObligationNode pos,
            RuntimeInformation rti) {
        this.init(rti.getProgram());
        if (this.backend != null ) {
            return this.backend.getExecutableStrategy(pos, rti);
        } else {
            // This should only happen in competition mode.
            // User-friendly messages are emitted by the mechanism calling check(), instead.
            LazyStrategy.LOG.warning("Strategy instantiation failed for " + this.fromStrategy);
            LazyStrategy.LOG.info(this.errorAsString());
            return new Fail("Failed to instantiate " + this.fromStrategy);
        }
    }

    private synchronized void init(StrategyProgram program) {
        if (this.backend != null || this.failure != null) {
            return; // Already initialized
        }

        try {
            final Object object = this.fromStrategy.get(program);
            this.backend = this.toUserStrat(object);

            // This actually semi-intentionally catches RuntimeException too,
            // since shooting up the machine thread is very bad manners,
            // and this is called from there.
        } catch (Exception e) {
            this.failure = e;
        }
    }

    private UserStrategy toUserStrat(final Object object) {
        if (object instanceof UserStrategy) {
            return (UserStrategy) object;
        } else if (object instanceof Processor) {
            return new ProcessorStrategy((Processor) object,
                    this.fromStrategy.getName(), this.fromStrategy.getParams().toString());
        }
        throw new IllegalArgumentException("Machine told to execute a " +
                object.getClass().getName() +
                " as a strategy, but I don't know how!");
    }

    private String errorAsString() {
        if (this.failure instanceof ParameterManagerException) {
            return ((ParameterManagerException) this.failure).getUserTrace();
        }

        StringWriter buf = new StringWriter();
        this.failure.printStackTrace(new PrintWriter(buf));
        return buf.toString();
    }

}
