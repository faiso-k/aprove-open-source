package aprove.input.Programs.llvm.utils;

import java.util.*;

/**
 * Comparator for comparing variable names in LLVM.
 * @author cryingshadow
 * @version $Id$
 */
public class LLVMNameComparator implements Comparator<String> {

    @Override
    public int compare(String o1, String o2) {
        if ((o1.startsWith("%") && o2.startsWith("%")) || (o1.startsWith("v") && o2.startsWith("v"))) {
            try {
                return
                    Integer.compare(Integer.parseInt(o1.substring(1)), Integer.parseInt(o2.substring(1)));
            } catch (NumberFormatException e) {
                // do nothing
            }
        }
        return o1.compareTo(o2);
    }

}
