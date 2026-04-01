package aprove.input.Programs.prolog;

import java.awt.*;
import java.awt.event.*;

import javax.swing.*;

import aprove.input.Programs.prolog.structure.*;
import aprove.verification.oldframework.BasicStructures.*;

/**
 * Dialog to ask the user for a PrologQuery depending on the predicates in a PrologProgram.
 * @author cryingshadow
 * @version $Id$
 */
public class PrologQueryDialog extends JDialog {

    /**
     * For serialization.
     */
    private static final long serialVersionUID = 5668812388523123071L;

    /**
     * The query.
     */
    private PrologQuery query;

    /**
     * Contains JCheckBoxes for each argument of the currently selected predicate.
     */
    private JPanel checkPanel;

    /**
     * Notification of whether the user has entered his query.
     */
    private boolean done;

    /**
     * Creates a PrologQueryDialog depending on the predicates in the specified PrologProgram.
     * @param prog The program.
     */
    public PrologQueryDialog(PrologProgram prog) {
        super((Dialog)null, "Prolog Query", false);
        this.query = null;
        this.checkPanel = new JPanel(new GridLayout(1,0));
        this.done = false;
        this.setDefaultCloseOperation(WindowConstants.DO_NOTHING_ON_CLOSE);
        this.setLayout(new GridLayout(0,1));
        this.add(new JTextField("Choose the analysis goal:"));
        final JComboBox<String> purposeBox =
            new JComboBox<String>(new String[]{"Termination", "Complexity", "Determinacy"});
        this.add(purposeBox);
        this.add(new JTextField("Choose the predicate:"));
        final ButtonGroup predicateGroup = new ButtonGroup();
        JPanel radioPanel = new JPanel(new GridLayout(0,3));
        boolean first = true;
        for (FunctionSymbol predicate : prog.createSetOfDefinedPredicates()) {
            final int arity = predicate.getArity();
            JRadioButton radio = new JRadioButton(predicate.getName()+"/"+arity);
            if (first) {
                radio.setSelected(true);
                first = false;
                for (int i = 0; i < arity; i++) {
                    JCheckBox box = new JCheckBox(""+(i+1));
                    box.setActionCommand(""+i);
                    PrologQueryDialog.this.checkPanel.add(box);
                }
            }
            radio.setActionCommand(predicate.getName());
            radio.addActionListener(new ActionListener() {

                /* (non-Javadoc)
                 * @see java.awt.event.ActionListener#actionPerformed(java.awt.event.ActionEvent)
                 */
                @Override
                public void actionPerformed(ActionEvent e) {
                    int count = PrologQueryDialog.this.checkPanel.getComponentCount();
                    while (count > arity) {
                        count--;
                        PrologQueryDialog.this.checkPanel.remove(count);
                    }
                    while (count < arity) {
                        count++;
                        JCheckBox box = new JCheckBox(""+count);
                        box.setActionCommand(""+(count-1));
                        PrologQueryDialog.this.checkPanel.add(box);
                    }
                    PrologQueryDialog.this.checkPanel.validate();
                }

            });
            predicateGroup.add(radio);
            radioPanel.add(radio);
        }
        this.add(radioPanel);
        this.add(new JTextField("Choose the moding (checked arguments are ground):"));
        this.add(this.checkPanel);
        JButton okButton = new JButton("OK");
        okButton.addActionListener(new ActionListener() {

            /* (non-Javadoc)
             * @see java.awt.event.ActionListener#actionPerformed(java.awt.event.ActionEvent)
             */
            @Override
            public void actionPerformed(ActionEvent arg0) {
                final PrologPurpose purpose;
                switch (purposeBox.getSelectedIndex()) {
                    case 1:
                        purpose = PrologPurpose.COMPLEXITY;
                        break;
                    case 2:
                        purpose = PrologPurpose.DETERMINACY;
                        break;
                    default:
                        purpose = PrologPurpose.TERMINATION;
                }
                Boolean[] moding = new Boolean[PrologQueryDialog.this.checkPanel.getComponentCount()];
                for (Component c : PrologQueryDialog.this.checkPanel.getComponents()) {
                    if (c instanceof JCheckBox) {
                        JCheckBox box = (JCheckBox)c;
                        moding[Integer.parseInt(box.getActionCommand())] = box.isSelected();
                    } else {
                        throw new IllegalStateException("Found component in checkPanel which should not be there!");
                    }
                }
                PrologQueryDialog.this.query =
                    new PrologQuery(predicateGroup.getSelection().getActionCommand(), moding, purpose);
                PrologQueryDialog.this.done = true;
                synchronized (PrologQueryDialog.this) {
                    PrologQueryDialog.this.notify();
                }
            }

        });
        this.add(okButton);
        this.pack();
        this.setLocationRelativeTo(null);
    }


    /**
     * @return True if the user has entered his query.
     */
    public boolean isDone() {
        return this.done;
    }

    /**
     * @return The query.
     */
    public PrologQuery getQuery() {
        return this.query;
    }

}
