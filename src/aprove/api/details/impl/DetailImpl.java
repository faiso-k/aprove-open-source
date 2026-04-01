package aprove.api.details.impl;

import java.util.*;

import aprove.api.details.*;

public class DetailImpl implements Detail {

    public static DetailImpl valid(Capability capability, String detail) {
        return new DetailImpl(capability, Optional.of(detail));
    }

    public static DetailImpl invalid(Capability capability) {
        return new DetailImpl(capability, Optional.empty());
    }

    private final Capability capability;
    private final Optional<String> detail;

    public DetailImpl(Capability capability, Optional<String> detail) {
        this.capability = capability;
        this.detail = detail;
    }

    @Override
    public Capability getCapability() {
        return capability;
    }

    @Override
    public Optional<String> getDetailString() {
        return detail;
    }
}
