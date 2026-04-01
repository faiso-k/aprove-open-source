package aprove.verification.dpframework.MCSProblem.mcnp;

public class Constants {
    public enum UnaryBinary {
        UNARY, BINARY;
    }

    public enum HighLow {
        HIGH("hi"), LOW("lo");

        String repr;

        HighLow(final String string) {
            this.repr = string;
        }

        /**
         * {@inheritDoc}
         */
        @Override
        public String toString() {
            return this.repr;
        }
    }

    public static final String TOP_TO_BOTTOM = "tb";
    public static final String BOTTOM_TO_TOP = "bt";
    public static final String TOP_TO_TOP = "tt";
    public static final String BOTTOM_TO_BOTTOM = "bb";

    public static final String MAX_ORDERING = "max";
    public static final String MIN_ORDERING = "min";
    public static final String MS_ORDERING = "ms";
    public static final String DMS_ORDERING = "dms";
    public static final String MAX_GT_MIN_ORDERING = "max_gt_min";
    public static final String MIN_GT_MAX_ORDERING = "min_gt_max";

    // --- unit orderings ---
    public static final String GRAPH_MAX_ORDERING = "max_ord";
    public static final String GRAPH_MIN_ORDERING = "min_ord";
    public static final String GRAPH_MS_ORDERING = "ms_ord";
    public static final String GRAPH_DMS_ORDERING = "dms_ord";


    // --- tripple orderings ---
    // SW - Strict/Weak; WS - Weak/Strict
    // First ordering is increasing part, Second - decreasing; Third decreasing >= increasing

    //tripple orderings increase strict, decrease weak
    //max/ms , max/ms
    public static final String GRAPH_SW_MAX_MAX_MAX_ORDERING = "sw_max_max_max_ord";
    public static final String GRAPH_SW_MS_MS_MAX_ORDERING = "sw_ms_ms_max_ord";
    public static final String GRAPH_SW_MS_MAX_MAX_ORDERING = "sw_ms_max_max_ord";
    public static final String GRAPH_SW_MAX_MS_MAX_ORDERING = "sw_max_ms_max_ord";
    //dms , max
    public static final String GRAPH_SW_DMS_MAX_MAX_ORDERING = "sw_dms_max_max_ord";
    //min , min
    public static final String GRAPH_SW_MIN_MIN_MIN_ORDERING = "sw_min_min_min_ord";
    //min , max/ms
    public static final String GRAPH_SW_MIN_MAX_MAXMIN_ORDERING = "sw_min_max_maxmin_ord";
    public static final String GRAPH_SW_MIN_MS_MAXMIN_ORDERING = "sw_min_ms_maxmin_ord";
    //max/ms/dms , min | min>=max
    public static final String GRAPH_SW_MAX_MIN_MINMAX_ORDERING = "sw_max_min_minmax_ord";
    public static final String GRAPH_SW_MS_MIN_MINMAX_ORDERING = "sw_ms_min_minmax_ord";
    public static final String GRAPH_SW_DMS_MIN_MINMAX_ORDERING = "sw_dms_min_minmax_ord";
    //max , ms/dms | min>=max
    public static final String GRAPH_SW_MAX_MS_MINMAX_ORDERING = "sw_max_ms_minmax_ord";
    public static final String GRAPH_SW_MAX_DMS_MINMAX_ORDERING = "sw_max_dms_minmax_ord";
    //min , ms/dms
    public static final String GRAPH_SW_MIN_MS_MIN_ORDERING = "sw_min_ms_min_ord";
    public static final String GRAPH_SW_MIN_DMS_MIN_ORDERING = "sw_min_dms_min_ord";

    //tripple orderings increase weak, decrease strict
    //max/ms , max/ms
    public static final String GRAPH_WS_MAX_MAX_MAX_ORDERING = "ws_max_max_max_ord";
    public static final String GRAPH_WS_MS_MS_MAX_ORDERING = "ws_ms_ms_max_ord";
    public static final String GRAPH_WS_MS_MAX_MAX_ORDERING = "ws_ms_max_max_ord";
    public static final String GRAPH_WS_MAX_MS_MAX_ORDERING = "ws_max_ms_max_ord";
    //dms , max
    public static final String GRAPH_WS_DMS_MAX_MAX_ORDERING = "ws_dms_max_max_ord";
    //min , min
    public static final String GRAPH_WS_MIN_MIN_MIN_ORDERING = "ws_min_min_min_ord";
    //min , max/ms
    public static final String GRAPH_WS_MIN_MAX_MAXMIN_ORDERING = "ws_min_max_maxmin_ord";
    public static final String GRAPH_WS_MIN_MS_MAXMIN_ORDERING = "ws_min_ms_maxmin_ord";
    //max/ms/dms , min | min>=max
    public static final String GRAPH_WS_MAX_MIN_MINMAX_ORDERING = "ws_max_min_minmax_ord";
    public static final String GRAPH_WS_MS_MIN_MINMAX_ORDERING = "ws_ms_min_minmax_ord";
    public static final String GRAPH_WS_DMS_MIN_MINMAX_ORDERING = "ws_dms_min_minmax_ord";
    //max , ms/dms | min>=max
    public static final String GRAPH_WS_MAX_MS_MINMAX_ORDERING = "ws_max_ms_minmax_ord";
    public static final String GRAPH_WS_MAX_DMS_MINMAX_ORDERING = "ws_max_dms_minmax_ord";
    //min , ms/dms
    public static final String GRAPH_WS_MIN_MS_MIN_ORDERING = "ws_min_ms_min_ord";
    public static final String GRAPH_WS_MIN_DMS_MIN_ORDERING = "ws_min_dms_min_ord";
}
