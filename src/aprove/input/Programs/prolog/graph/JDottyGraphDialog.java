package aprove.input.Programs.prolog.graph;

import java.awt.*;
import java.awt.event.*;
import java.io.*;
import java.util.logging.*;

import javax.swing.*;

import aprove.verification.oldframework.Utility.Graph.*;

/**
 * @author nowonder
 * @version $Id$
 */
@SuppressWarnings("serial")
public class JDottyGraphDialog extends JDialog implements ActionListener {

    public final static double SCALE = 1.0;

    protected static Logger log = Logger.getLogger("aprove.GraphUserInterface.Utility.JDottyGraphDialog");

    public JPanel buttonpanel;
    public JButton close;
    public String descr;
    public JButton saveas;
    public JComboBox<String> selector;
    JDottyGraphArea jDottyGraphArea;
    JPanel panel;

    private JDottyGraphDialog(final JDialog parent, final String title, final String descr) {
        super(parent, title, false);
        this.init_graph(parent, descr);
        JDottyGraphDialog.correctSizeOfWith(this, parent);
    }

    private JDottyGraphDialog(final JFrame parent, final String title, final String descr) {
        super(parent, title, false);
        this.init_graph(parent, descr);
        JDottyGraphDialog.correctSizeOfWith(this, parent);
        this.setVisible(true);
    }

    private JDottyGraphDialog(final String title, final String descr) {
        super();
        this.setTitle(title);
        this.init_graph(descr);
        this.setVisible(true);
    }

    private JDottyGraphDialog(final String title, final String descr, final Point location) {
        this(title, descr);
        this.setLocation(location);
    }

    public static void correctSizeOfWith(final Window win, final Window wwin) {
        final Dimension pdim = wwin.getSize();
        final Dimension mdim = win.getSize();
        win.setSize(
            JDottyGraphDialog.min(pdim.getWidth(), mdim.getWidth()),
            JDottyGraphDialog.min(pdim.getHeight(), mdim.getHeight()));

    }

    public static JDottyGraphDialog create(final String title, final String descr) {
        return new JDottyGraphDialog(title, descr);
    }

    public static JDottyGraphDialog create(final String title, final String descr, final Point location) {
        return new JDottyGraphDialog(title, descr, location);
    }

    public static JDottyGraphDialog create(final Window parent, final String title, final Graph<?, ?> g) {
        return JDottyGraphDialog.create(parent, title, g.toDOT());
    }

    public static JDottyGraphDialog create(final Window parent, final String title, final String descr) {
        if (parent instanceof JFrame) {
            return new JDottyGraphDialog((JFrame) parent, title, descr);
        } else if (parent instanceof JDialog) {
            return new JDottyGraphDialog((JDialog) parent, title, descr);
        } else {
            return new JDottyGraphDialog(title, descr);
        }
    }

    private static int min(final double a, final double b) {
        return a < b ? (int) a : (int) b;
    }

    @Override
    public void actionPerformed(final ActionEvent e) {
        if (e.getSource() == this.close) {
            this.dispose();
            synchronized (this) {
                this.notify();
            }
        } else if (e.getSource() == this.saveas) {
            File f = new File("");
            f = new FileDialogManager(this).showSaveAsDialog("SAVEGRAPH", "Save As ..", f, true);
            if (f != null) {
                PrintWriter pw = null;
                try {
                    pw = new PrintWriter(f);
                    pw.println(this.descr);
                } catch (final FileNotFoundException e1) {
                } finally {
                    if (pw != null) {
                        pw.close();
                    }
                }
            }
        } else if (e.getSource() == this.selector) {
            System.err.println(e.getActionCommand());
            //            this.center((String) this.selector.getSelectedItem());
        }
    }

    public void waitForClose() {
        try {
            synchronized (this) {
                this.wait();
            }
        } catch (final InterruptedException e) {
        }
    }

    //    public void center(String id) {
    //        this.jDottyGraphArea.center(id);
    //    }

    protected void init_graph(final Component parent, final String descr) {
        this.setLocationRelativeTo(parent);
        this.init_graph(descr);
    }

    protected void init_graph(final String descr) {
        this.descr = descr;
        this.setDefaultCloseOperation(WindowConstants.DO_NOTHING_ON_CLOSE);
        this.panel = new JPanel(new BorderLayout());
        this.setContentPane(this.panel);
        //        this.jDottyGraphArea = new JDottyGraphArea(descr);
        this.panel.add(this.jDottyGraphArea, BorderLayout.CENTER);
        this.buttonpanel = new JPanel(new GridLayout(3, 1));
        //        this.selector =
        //                new JComboBox<String>(this.jDottyGraphArea.getVertexNames());
        //        this.selector.addActionListener(this);
        this.buttonpanel.add(this.selector);
        this.saveas = new JButton("Save As");
        this.saveas.addActionListener(this);
        this.buttonpanel.add(this.saveas);
        this.close = new JButton("Close");
        this.close.addActionListener(this);
        this.buttonpanel.add(this.close);
        this.panel.add(this.buttonpanel, BorderLayout.SOUTH);
        this.pack();
        //        this.center((String) this.selector.getItemAt(0));
        this.repaint(10);

    }
}
