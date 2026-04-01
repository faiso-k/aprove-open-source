package aprove.input.Programs.prolog.graph;

import javax.swing.*;

public class JDottyGraphArea extends JPanel {

    //    private static final long serialVersionUID = 8643546187127426896L;
    //
    //    protected static Logger log =
    //        Logger.getLogger("aprove.GraphUserInterface.Interactive.DpGraphDialog");
    //
    //    public final static double SCALE = 1.0;
    //
    //    String descr;
    //    PImage image;
    //    PScrollPane pScrollPane;
    //    PCanvas zoom_graph;
    //    IGraph g;
    //
    //
    //    public JDottyGraphArea(){
    //        super();
    //        this.setLayout(new BorderLayout());
    //        this.setBorder(BorderFactory.createEmptyBorder());
    //        this.zoom_graph = new PCanvas();
    //    this.image = new PImage();
    //        this.zoom_graph.getLayer().addChild(this.image);
    //        this.zoom_graph.getCamera().setScale(SCALE);
    //        this.pScrollPane = new PScrollPane(this.zoom_graph);
    //        this.pScrollPane.setMinimumSize(new Dimension(800,200));
    //        this.add(this.pScrollPane,BorderLayout.CENTER);
    //    }
    //
    //    public JDottyGraphArea(String descr){
    //        this();
    //        setJDottyDescr(descr);
    //    }
    //
    //    public JDottyGraphArea(Graph<?, ?> graph){
    //        this();
    //        setJDottyDescr(graph.toDOT());
    //    }
    //
    //    public Point2D getPos(String id) {
    //        IVertex v = g.getVertex(id);
    //        return (v == null) ? null : (Point2D) v.getAttr("pos");
    //    }
    //
    //    public void center(String id) {
    //        if (id == null) return;
    //        Point2D pos = this.getPos(id);
    //        if (pos == null) return;
    //        JViewport vp = this.pScrollPane.getViewport();
    //        Dimension d = vp.getExtentSize();
    //        int newX = (int)(pos.getX()-d.getWidth()/2);
    //        int newY = (int)(pos.getY()-d.getHeight()/2);
    //        if (newX < 0) newX = 0;
    //        if (newY < 0) newY = 0;
    //        if (newX > this.image.getWidth()) newX = (int) this.image.getWidth();
    //        if (newY > this.image.getHeight()) newY = (int) this.image.getHeight();
    //        vp.setViewPosition(new Point(newX, newY));
    //    }
    //
    //    public void setJDottyDescr(String descr){
    //        this.descr = descr;
    //        // used a StringBufferInputStream before
    //        this.g =
    //            new DotParser(
    //                new ByteArrayInputStream(
    //                    this.descr.getBytes()
    //                ),
    //                "internal"
    //            ).parse().getGraph();
    //        new Dot().layout(g, 0, 2);
    //        GraphPanel gpanel = new GraphPanel(g, SCALE);
    //        Image image = gpanel.getImage();
    //        this.image.setImage(image);
    //        Canvas dummy = new Canvas();
    //        int width = image.getWidth(dummy);
    //        int height = image.getHeight(dummy);
    //        Rectangle max =
    //            GraphicsEnvironment
    //            .getLocalGraphicsEnvironment()
    //            .getMaximumWindowBounds();
    //        if (width > max.getWidth()) {
    //            width = (int)max.getWidth();
    //        }
    //        if (height > max.getHeight()) {
    //            height = (int)max.getHeight();
    //        }
    //        this.pScrollPane.setPreferredSize(new Dimension(width+3, height+3));
    //    }
    //
    //
    //    public static void showDialog(
    //        String title,
    //        Graph<?, ?> g,
    //        boolean mod,
    //        String id
    //    ) {
    //        HDialog dia = new HDialog(title,g,mod,id);
    ////        dia.show();
    //        dia.setVisible(true);
    //
    //        /*JDialog dia = new JDialog();
    //        dia.setModal(true);
    //        dia.setContentPane(new JDottyGraphArea(g.toDOT()));
    //        dia.show();*/
    //
    //        /*try {
    //            DpGraphDialog.create(KefirUI.my, "Cycccccle", g.toDOT()).show();
    //        }
    //        catch (Throwable t) {
    //            throw new RuntimeException(t);
    //            //JOptionPane.showMessageDialog(null, "Error in displaying the Dependency Graph.", "Error", JOptionPane.ERROR_MESSAGE);
    //        }*/
    //    }
    //
    //    public static void showDialog(
    //        String title,
    //        String g,
    //        boolean mod,
    //        String id
    //    ) {
    //        HDialog dia = new HDialog(title,g,mod,id);
    ////        dia.show();
    //        dia.setVisible(true);
    //
    //        /*JDialog dia = new JDialog();
    //        dia.setModal(true);
    //        dia.setContentPane(new JDottyGraphArea(g.toDOT()));
    //        dia.show();*/
    //
    //        /*try {
    //            DpGraphDialog.create(KefirUI.my, "Cycccccle", g.toDOT()).show();
    //        }
    //        catch (Throwable t) {
    //            throw new RuntimeException(t);
    //            //JOptionPane.showMessageDialog(null, "Error in displaying the Dependency Graph.", "Error", JOptionPane.ERROR_MESSAGE);
    //        }*/
    //    }
    //
    //    private static class HDialog extends JDialog implements ActionListener {
    //        private static final long serialVersionUID = 5830914089454121383L;
    //        JButton close;
    //        JPanel panel;
    //        JDottyGraphArea jDottyGraphArea;
    //
    //        public HDialog(String title,Graph<?, ?> g,boolean mod,String id){
    //            super();
    //            this.setModal(mod);
    //            this.setTitle(title);
    //            this.setDefaultCloseOperation(WindowConstants.DISPOSE_ON_CLOSE);
    //            this.panel = new JPanel(new BorderLayout());
    //            this.setContentPane(this.panel);
    //            this.jDottyGraphArea = new JDottyGraphArea(g.toDOT());
    //            this.panel.add(this.jDottyGraphArea, BorderLayout.CENTER);
    //            this.close = new JButton("Close");
    //            this.close.addActionListener(this);
    //            this.panel.add(this.close, BorderLayout.SOUTH);
    //            this.pack();
    //            this.jDottyGraphArea.center(id);
    //            this.repaint(10);
    //        }
    //
    //        public HDialog(String title,String g,boolean mod,String id){
    //            super();
    //            this.setModal(mod);
    //            this.setTitle(title);
    //            this.setDefaultCloseOperation(WindowConstants.DISPOSE_ON_CLOSE);
    //            this.panel = new JPanel(new BorderLayout());
    //            this.setContentPane(this.panel);
    //            this.jDottyGraphArea = new JDottyGraphArea(g);
    //            this.panel.add(this.jDottyGraphArea, BorderLayout.CENTER);
    //            this.close = new JButton("Close");
    //            this.close.addActionListener(this);
    //            this.panel.add(this.close, BorderLayout.SOUTH);
    //            this.pack();
    //            this.jDottyGraphArea.center(id);
    //            this.repaint(10);
    //        }
    //
    //        public void actionPerformed(ActionEvent e) {
    //            if (e.getSource() == close) {
    //                this.dispose();
    //            }
    //        }
    //    }
    //
    //    @SuppressWarnings("unchecked")
    //    public Vector<String> getVertexNames() {
    //        Vector<String> names = new Vector<String>(g.getVertexNameSet());
    //        Collections.sort(names, new Comparator<String>() {
    //            public int compare(String s1, String s2) {
    //                Integer i1 = Integer.parseInt(s1);
    //                Integer i2 = Integer.parseInt(s2);
    //                return i1.compareTo(i2);
    //            }
    //        });
    //        return names;
    //    }
}
