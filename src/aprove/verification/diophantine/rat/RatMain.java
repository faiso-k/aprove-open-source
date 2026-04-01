package aprove.verification.diophantine.rat;

import aprove.cli.Generic.*;
import aprove.exit.*;

public class RatMain {

    public static void main(String[] args) {
        try {
            doMain(args);
        } catch (KillAproveException e) {
            e.runSystemExit();
        }
    }

    private static void doMain(String[] args) throws KillAproveException {
        GenericMain.doMain(args, new RatOptions());
    }
}
