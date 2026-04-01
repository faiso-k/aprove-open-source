package aprove.input.Programs.newTrs;

import java.awt.*;
import java.awt.event.*;

import javax.swing.*;

/**
 * Dialog to ask the user for an analysis goal for a TRS.
 * @author cryingshadow
 * @version $Id$
 */
public class TRSDialog extends JDialog {

    /**
     * For serialization.
     */
    private static final long serialVersionUID = -3153530969491537951L;

    /**
     * Analyze termination or complexity?
     */
    private boolean complexity;

    /**
     * Notification of whether the user has entered his query.
     */
    private boolean done;

    /**
     * Creates a TRSDialog.
     */
    public TRSDialog() {
        super((Dialog)null, "Analysis Goal for TRS", false);
        this.complexity = false;
        this.done = false;
        this.setDefaultCloseOperation(WindowConstants.DO_NOTHING_ON_CLOSE);
        this.setLayout(new GridLayout(0,1));
        this.add(new JTextField("Choose the analysis goal:"));
        final JComboBox<String> purposeBox =
            new JComboBox<String>(new String[]{"Universal Termination", "Innermost Runtime Complexity"});
        this.add(purposeBox);
        JButton okButton = new JButton("OK");
        okButton.addActionListener(new ActionListener() {

            /* (non-Javadoc)
             * @see java.awt.event.ActionListener#actionPerformed(java.awt.event.ActionEvent)
             */
            @Override
            public void actionPerformed(ActionEvent arg0) {
                switch (purposeBox.getSelectedIndex()) {
                    case 1:
                        TRSDialog.this.complexity = true;
                        break;
                    default:
                        TRSDialog.this.complexity = false;
                }
                TRSDialog.this.done = true;
                synchronized (TRSDialog.this) {
                    TRSDialog.this.notify();
                }
            }

        });
        this.add(okButton);
        this.pack();
        this.setLocationRelativeTo(null);
    }


    /**
     * @return True if we want to analyze complexity. False otherwise.
     */
    public boolean analyzeComplexity() {
        return this.complexity;
    }

    /**
     * @return True if the user has entered his query.
     */
    public boolean isDone() {
        return this.done;
    }

}
