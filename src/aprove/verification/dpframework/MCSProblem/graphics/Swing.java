package aprove.verification.dpframework.MCSProblem.graphics;

import java.awt.*;
import java.util.List;

import javax.swing.*;

import aprove.verification.dpframework.MCSProblem.mcnp.*;


public class Swing extends JFrame {

    private List<MCGraph> _mcGraphs;
    private LevelMapping _levalMapping;


        public Swing(List<MCGraph> mcGraphs,LevelMapping levalMapping)
        {
            this._mcGraphs = mcGraphs;
            this._levalMapping = levalMapping;

            this.setTitle("Monotonicity Constraints");

//            JMenuBar menubar = new JMenuBar();
//            JMenu file = new JMenu("File");
//            file.setMnemonic(KeyEvent.VK_F);
//
//            JMenuItem fileClose = new JMenuItem("Close");
//            fileClose.setMnemonic(KeyEvent.VK_C);
//            fileClose.addActionListener(new ActionListener() {
//                public void actionPerformed(ActionEvent event) {
//                    System.exit(0);
//                }
//            });
//            file.add(fileClose);
//            menubar.add(file);
//            setJMenuBar(menubar);


            JPanel panel = new JPanel();
            Drawer scg = new Drawer(this._mcGraphs,this._levalMapping);
            JScrollPane pane = new JScrollPane(scg);

            pane.setPreferredSize(new Dimension(700, 700));
            panel.add(pane);
            this.add(panel);

            this.pack();

            this.setLocationRelativeTo(null);
            this.setDefaultCloseOperation(JFrame.EXIT_ON_CLOSE);
            this.setVisible(true);
        }

        public Swing(List<MCGraph> mcGraphs)
        {
            this(mcGraphs,null);
        }

        public static void main(String[] args)
        {
//            List<MCGraph> graphs = new ArrayList<MCGraph>();
//            graphs.add(Drawer.getGraph());
//            graphs.add(Drawer.getGraph());
//            graphs.add(Drawer.getGraph());
//
//            LevelMapping levelMapping = null;
//            Swing simple = new Swing(graphs,levelMapping);
//            new Swing(graphs,levelMapping);
        }

}
