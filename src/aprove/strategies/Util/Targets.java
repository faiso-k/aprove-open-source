package aprove.strategies.Util;

import java.io.*;
import java.util.*;
import java.util.logging.*;

import aprove.verification.oldframework.Input.*;
import aprove.verification.oldframework.Input.TypeAnalyzers.*;

public class Targets extends Vector<Input> {

    protected static Logger log = Logger.getLogger("aprove.strategies.Util.Targets");

    protected String fileName;
    protected boolean modified;
    protected TypeAnalyzer typeAnalyzer;

    public Targets(TypeAnalyzer typeAnalyzer) {
        this(null, typeAnalyzer);
    }

    public Targets(String fileName, TypeAnalyzer typeAnalyzer) {
        this.setFileName(fileName);
        this.setModified(false);
        this.typeAnalyzer = typeAnalyzer;
    }

    public Input getInput() {
        return (this.size() == 1 ? this.iterator().next() : null);
    }

    @Override
    public String toString() {
        StringBuffer temp = new StringBuffer("");
        Iterator i = this.iterator();
        while (i.hasNext()) {
            Input input = (Input)i.next();
            temp.append(input.toString()+(i.hasNext() ? "\n" : ""));
        }
        return temp.toString();
    }

    public void setFileName(String fileName) {
        this.fileName = fileName;
    }

    public String getFileName() {
        return this.fileName;
    }

    @Override
    public boolean add(Input o) {
        this.setModified(true);
        return super.add(o);
    }

    @Override
    public void clear() {
        if (this.size()>0) {
            Targets.log.log(Level.INFO, "  {0} file(s) removed\n", this.size()+"");
        }
        super.clear();
        this.setFileName(null);
        this.setModified(true);
    }

    public boolean getModified() {
        return this.modified;
    }

    public void setModified(boolean val) {
        this.modified = val;
    }

    public void save(String fileName) {
        this.setFileName(fileName);
        BufferedWriter writer;
        try {
            writer = new BufferedWriter(new OutputStreamWriter(new FileOutputStream(new File(fileName))));
        } catch (FileNotFoundException e) {
            return;
        }
        Iterator i = this.iterator();
        try {
            while (i.hasNext()) {
                Input in = (Input)i.next();
                if (in instanceof FileInput) {
                    writer.write(in.getPath());
                    writer.newLine();
                }
            }
            writer.close();
        } catch (IOException e) {
            return;
        }
        this.setModified(false);
    }

    public int load(String fileName, String protoAnnotation) throws ParserErrorsSourceException {
        return this.load(fileName, new HashSet(), protoAnnotation);
    }
    public int load(String fileName, Set done, String protoAnnotation) throws ParserErrorsSourceException {
        int count = 0;
        Targets.log.log(Level.INFO, "Parsing {0} ...\n", fileName);
        boolean wasEmpty = this.size() == 0;
        this.setFileName(fileName);
        BufferedReader reader;
        try {
            reader = new BufferedReader(new InputStreamReader(new FileInputStream(new File(fileName))));
        } catch (FileNotFoundException e) {
            return 0;
        }
        List lines = new Vector();
        try {
            String line = reader.readLine();
            while (line != null) {
                lines.add(line);
                line = reader.readLine();
            }
            reader.close();
        } catch (IOException e) {
            this.setModified(true);
            return 0;
        }
        if (done.contains(lines)) {
            Targets.log.log(Level.WARNING, "Detected infitinite recursion in {0}. Skipping.\n", fileName);
        } else {
            Set newDone = new HashSet(done);
            newDone.add(lines);
            Iterator i = lines.iterator();
            while (i.hasNext()) {
                String line = (String)i.next();
                count = count + this.addTargets(new File[] {new File(line)}, newDone, protoAnnotation);
            }
        }
        this.setModified(!wasEmpty);
        return count;
    }

    public int addTargets(File[] files, String protoAnnotation) throws ParserErrorsSourceException {
        return this.addTargets(files, new HashSet(), protoAnnotation);
    }

    public int replaceTargets(File[] files, String protoAnnotation) throws ParserErrorsSourceException {
        this.clear();
        this.setFileName(null);
        this.setModified(true);
        return this.addTargets(files, new HashSet(), protoAnnotation);
    }

    public int addTargets(File[] files, Set done, String protoAnnotation) throws ParserErrorsSourceException {
        int count = 0;
        for (int i = 0; i < files.length; i++) {
            File f = files[i];
            if (f.isFile()) {
                if (f.getName().endsWith(".apl")) {
                    try {
                        count = count + this.load(f.getCanonicalPath(), done, protoAnnotation);
                    } catch(IOException e) {}
                } else {
                    try {
                        Targets.log.log(Level.INFO, "Adding: {0}\n", f.getCanonicalPath());
                        this.setFileName(f.getCanonicalPath());
                        this.add(new FileInput(f, null, protoAnnotation));
                    } catch (IOException e) {}
                    count++;
                }
            } else if (f.isDirectory()) {
                count = count + this.addTargets(f.listFiles(new FileFilters("BATCH")), protoAnnotation);
            }
        }
        return count;
    }

    public TypeAnalyzer getTypeAnalyzer() {
        return this.typeAnalyzer;
    }

}
