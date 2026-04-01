package aprove.api.details.impl;

import aprove.verification.dpframework.*;

class SourceDetails extends BaseDetails<ExternUsable> {

    public SourceDetails() {
        super(ExternUsable.class);
    }

    @Override
    protected String details(ExternUsable t) {
        try {
            return t.toExternString();
        } catch (NotExternUsableInstanceException e) {
            return "(Conversion error: " + e.getMessage() + ")";
        }
    }
}
