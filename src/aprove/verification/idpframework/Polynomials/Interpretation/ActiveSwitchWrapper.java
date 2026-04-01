package aprove.verification.idpframework.Polynomials.Interpretation;

import aprove.verification.idpframework.Core.SemiRings.*;


/**
 *
 * @author MP
 */
public class ActiveSwitchWrapper<R extends SemiRing<R>> {

    private final PolyContextSwitchPair<R> contextSwitch;
    private volatile boolean forbidWildContext;
    private volatile boolean forceEncoding;

    public ActiveSwitchWrapper(final PolyContextSwitchPair<R> contextSwitch, final boolean forbidWildContext, final boolean forceEncoding) {
        this.contextSwitch = contextSwitch;
        this.forbidWildContext = forbidWildContext;
        this.forceEncoding = forceEncoding;
    }

    public void forbidWildContext() {
        this.forbidWildContext = true;
    }

    public boolean isWildContextForbidden() {
        return this.forbidWildContext;
    }

    public boolean isForceEncoding() {
        return this.forceEncoding;
    }

    public PolyContextSwitchPair<R> getContextSwitch() {
        return this.contextSwitch;
    }

    public void forceEncoding() {
        this.forceEncoding = true;
    }

    @Override
    public ActiveSwitchWrapper<R> clone() {
        return new ActiveSwitchWrapper<R>(this.contextSwitch.clone(), this.forbidWildContext, this.forceEncoding);
    }


}