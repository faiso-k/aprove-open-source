package aprove.input.Programs.prolog;

import java.util.*;

import aprove.input.Generated.prolog.analysis.*;
import aprove.input.Generated.prolog.node.*;

/**
 * LayoutPass.<br><br>
 * Extract the layout text from a Prolog program.
 *
 * Created: Sep 28, 2006<br>
 * Last modified: Feb 04, 2013
 *
 * @author cryingshadow
 * @version $Id$
 */
public class LayoutPass extends DepthFirstAdapter {

    /**
     * The layout text as list of Strings.
     */
    private final ArrayList<String> layout;

    /**
     * A constructor is a constructor is a constructor...
     */
    public LayoutPass() {
        this.layout = new ArrayList<String>();
    }

    @Override
    public void caseAEmptyProgram(final AEmptyProgram node) {
        this.inAEmptyProgram(node);
        if (node.getLayoutText() != null) {
            final String text = node.getLayoutText().getText().trim();
            if (!"".equals(text)) {
                this.layout.add(text);
            }
        }
        this.outAEmptyProgram(node);
    }

    @Override
    public void caseASentence(final ASentence s) {
        this.inASentence(s);
        final List<PAny> list = s.getAny();
        for (final PAny any : list) {
            if (any instanceof ATokenAny) {
                final PToken token = ((ATokenAny) any).getToken();
                if (token instanceof ALayoutToken) {
                    final String text = ((ALayoutToken) token).getLayoutText().getText().trim();
                    if (!"".equals(text)) {
                        this.layout.add(text);
                    }
                }
            }
        }
        final String fullstopText = s.getFullstop().getText().substring(1).trim();
        if (!"".equals(fullstopText)) {
            this.layout.add(fullstopText);
        }
        this.outASentence(s);
    }

    /**
     * @return The layout text as list of Strings.
     */
    public ArrayList<String> getLayout() {
        return this.layout;
    }

}
