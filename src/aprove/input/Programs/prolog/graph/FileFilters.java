package aprove.input.Programs.prolog.graph;

import java.io.*;
import java.util.*;

import javax.swing.*;

import aprove.verification.oldframework.Utility.*;

public class FileFilters
extends javax.swing.filechooser.FileFilter
implements java.io.FileFilter {


    private static Map<String, String[]> name2types;
    private static Map<String, String> type2desc;
    private static Map<String, String[]> type2exts;

    private String  type;
    private String[] suffixes;
    private String description;
    private boolean allowDirs;

    public static Vector<FileFilters> createFor(String name){
        Vector<FileFilters> res = new Vector<FileFilters>();
        String[] types = (String[]) FileFilters.name2types.get(name);
        for (int i=0;i<types.length;i++){
             res.add(new FileFilters(types[i]));
        }
        return res;
    }

    public FileFilters(String type) {
        this.type = type;
        this.suffixes = (String[])FileFilters.type2exts.get(type);
        if (this.suffixes == null) {
            throw new RuntimeException(
                "FileFilters: filetype " + type + " unknown"
            );
        }
        this.description = (String) FileFilters.type2desc.get(type);
        this.allowDirs = true;
    }

    public FileFilters(String type, String[] suffixes, String description) {
        this.type = type;
        this.suffixes = suffixes;
        this.description = description;
        this.allowDirs = true;
    }

    @Override
    public boolean accept(File f) {
        if (f == null) { return false; }
        if (f.isFile()) {
            String name = f.getName();
            for (int i = 0; i < this.suffixes.length; i++) {
                if (FileFilters.suffix(name, this.suffixes[i])) {
                    return true;
                }
            }
            return false;
        } else if (f.isDirectory()) {
            return this.allowDirs;
        } else {
            return false;
        }
    }

    public String getType(){
        return this.type;
    }

    private static boolean suffix(String name, String suffix) {
        if (name == null) { return false; }
        if (suffix == null) { return true; }
        String[] parts = name.split("\\.");
        if (parts.length == 0) {
            return false;
        }
        return parts[parts.length-1].equals(suffix);
    }

    public String getStandardExtension(){
        return this.suffixes[0];
    }

    @Override
    public String getDescription() {
        return this.description;
    }

    private static void loadProperties() {
            FileFilters.type2desc = new HashMap<String, String>();
            FileFilters.type2exts = new HashMap<String, String[]>();
            FileFilters.name2types = new HashMap<String, String[]>();
            Properties defaultprops = new Properties();
            try {
                PropertyLoader.fromResource(
                    defaultprops,
                    JPanel.class,
                    "filefilters.properties"
                );
            } catch (IOException e) {
                System.err.println(e.getMessage());
                throw new RuntimeException("Where are my default props? D'oh!");
            }
            Properties props = new Properties(defaultprops);
            for (
                    Enumeration<?> en = props.propertyNames();
                    en.hasMoreElements() ;

            ) {
                String pname = (String) en.nextElement();
                if (pname.startsWith("_")){
                    String list = props.getProperty(pname);
                    FileFilters.name2types.put(pname.substring(1),list.split("\\s+"));
                } else {
                    String descext = props.getProperty(pname);
                    String dc[] = descext.split("\\:");
                    String desc = dc[0];
                    String[] exts = dc[1].split("\\s+");
                    FileFilters.type2desc.put(pname,desc);
                    FileFilters.type2exts.put(pname,exts);
                }
            }
            FileFilters.type2desc.put("ALL","All Files");
            FileFilters.type2exts.put("ALL",new String[]{null});
    }

    static {
        FileFilters.loadProperties();
    }
}
