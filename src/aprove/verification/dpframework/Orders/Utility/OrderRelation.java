package aprove.verification.dpframework.Orders.Utility;

import aprove.prooftree.Export.Utility.*;

public enum OrderRelation implements Exportable {

    EQ {

        @Override
        public String export(Export_Util o) {
            return "=";
        }

    },

    GE {

        @Override
        public String export(Export_Util o) {
            return o.geSign();
        }

    },

    GR {

        @Override
        public String export(Export_Util o) {
            return o.gtSign();
        }

    },

    NGE {

        @Override
        public String export(Export_Util o) {
            return "not " + o.geSign();
        }

    },

    GENGR {

        @Override
        public String export(Export_Util o) {
            return o.geSign() + " not " + o.gtSign();
        }

    };

    @Override
    public abstract String export(Export_Util o);

}
