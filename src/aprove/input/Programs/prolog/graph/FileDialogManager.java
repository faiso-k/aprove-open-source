package aprove.input.Programs.prolog.graph;
//import aprove.verification.oldframework.Rewriting.*;
import java.awt.*;
import java.io.*;
import java.util.*;

import javax.swing.*;

public class FileDialogManager {

    private static final int DISCARD = 0;
    public static final int SAVE = 1;
    public static final int CANCEL = 2;
    public static final int CONTINUE = 3;

    public static final int ALL_FILES = 0;
    public static final int APROVE_FILES = 1;
    public static final int FOLLIST_FILES = 4;
    public static final int HTML_FILES = 5;
    public static final int LATEX_FILES = 6;

    private JFileChooser fileChooser;
  //  private JFileChooser dirfileChooser;
    private Component parent;
  //  private Set filters;
    private File lastFile;
    private File[] lastFiles;
    private FileFilters givenFilter;

    public FileDialogManager(Component parent, String desc, String ext){
        this.parent = parent;
        this.lastFile = null;
        this.lastFiles = null;
        this.givenFilter = new FileFilters("",new String[]{ext},desc);
        this.fileChooser = new JFileChooser();
 //       this.dirfileChooser = null;
//        this.fileChooser.setAcceptAllFileFilterUsed(false);
    }

    public FileDialogManager(Component parent){
        this.parent = parent;
        this.lastFile = null;
        this.lastFiles = null;
//        this.dirfileChooser = null;
        this.fileChooser = new JFileChooser();
//        this.fileChooser.setAcceptAllFileFilterUsed(false);
    }

    public JFileChooser getFileChooser(){
        return this.fileChooser;
    }

    private void setFilters(Vector<?> filters,String currenttype,File f){
        this.fileChooser.resetChoosableFileFilters();
        Iterator<?> it = filters.iterator();
        FileFilters filter = null;
        FileFilters curFilter = null;
        while (it.hasNext()){
            filter = (FileFilters) it.next();
            this.fileChooser.addChoosableFileFilter(filter);
            if ((filter.accept(f)) || (filter.getType().equals(currenttype))) {
                curFilter = filter;
            }
        }
        if (curFilter == null) {
            curFilter = filter;
        }
        this.fileChooser.setFileFilter(curFilter);
    }

    private void makeFilters(String name,String type,File f){
        this.fileChooser.setAcceptAllFileFilterUsed(false);
        if (name != null) {
            this.setFilters(FileFilters.createFor(name),type,f);
        } else {
            this.fileChooser.setFileFilter(this.givenFilter);
        }
    }

    public void showWarningDialog(String warning){
        Object[] options = new Object[1];
        options[0] = "Ok";
        JOptionPane.showOptionDialog(this.parent,
                                     warning,
                                     "Warning",
                                     JOptionPane.DEFAULT_OPTION,
                                     JOptionPane.WARNING_MESSAGE,
                                     null, options, options[0]);
    }

    private File addExtension(File f){
        if (f == null) {
            return null;
        }
        javax.swing.filechooser.FileFilter ff = this.fileChooser.getFileFilter();
        if (!(ff instanceof FileFilters)) {
            return f;
        }
        FileFilters filter = (FileFilters) ff;
        String name = f.getName();
        int i = name.lastIndexOf(".");
    if (i<0) {
            String ext = filter.getStandardExtension();
            if (ext != null) {
                return new File(f.getAbsolutePath() + "." + ext);
            }
    }
    return f;
    }

    private File cutExtension(File f){
        if (f == null) {
            return null;
        }
        javax.swing.filechooser.FileFilter ff = this.fileChooser.getFileFilter();
        if (!(ff instanceof FileFilters)) {
            return f;
        }
 //       FileFilters filter = (FileFilters) ff;
        String path = f.getAbsolutePath();
        int i = path.lastIndexOf(".");
    if (i<0) {
            return f;
    }
    return new File(path.substring(0,i));
    }


    public File showSaveAsDialog(String name, String title, File curfile, boolean autoExt){
        return this.showSaveAsDialog(name,title,curfile,autoExt,false);
    }

    public File showSaveAsDialog(String name, String title, File curfile, boolean autoExt,boolean repExt){
        this.fileChooser = new JFileChooser();
        if (repExt){
            this.makeFilters(name,null,null);
        } else {
            if (curfile == null) { curfile = this.lastFile; }
            this.makeFilters(name,null,curfile);
            if (curfile == null) { curfile = new File(""); }
        }
        this.fileChooser.setFileSelectionMode(JFileChooser.FILES_ONLY);
        this.fileChooser.setMultiSelectionEnabled(true);
        this.fileChooser.setMultiSelectionEnabled(false);
        if (repExt){
             curfile = this.addExtension(this.cutExtension(curfile));
        }
        this.fileChooser.setSelectedFile(curfile);
        int res = this.fileChooser.showDialog(this.parent, title);
        File f = this.fileChooser.getSelectedFile();
        if (autoExt) {
            f = this.addExtension(f);
        }
        if (f != null){this.lastFile = f;}
        boolean doSave = res == JFileChooser.APPROVE_OPTION;
        if (doSave){
            if (f.exists()) {
                int OVERWRITE = 0;
                int CANCEL = 1;
                Object[] options = new Object[2];
                options[OVERWRITE] = "Overwrite";
                options[CANCEL]    = "Cancel";
                int i = JOptionPane.showOptionDialog(this.parent,
                                                     "File " +f.getName() + " already exists!",
                                                     "Warning",
                                                     JOptionPane.DEFAULT_OPTION,
                                                     JOptionPane.WARNING_MESSAGE,
                                                     null, options, options[0]);
                doSave = (OVERWRITE == i);
            }
        }
        if (!doSave) {
            return null;
        }
        return f;
    }

    /**
     *
     * @param name Name of file filter
     */
    public File[] showOpenDialog(String name){
       return this.showOpenDialog(true,name);
    }

    /**
     *
     * @param name Name of file filter
     */
    public File showSingleOpenDialog(String name){
        File[] files = this.showOpenDialog(false,name);
        if (files == null) {
            return null;
        }
        if (files.length > 1) {
            return null;
        }
        if (files.length < 1) {
            return null;
        }
        if (files[0] != null) {
            this.lastFile = files[0];
        }
        return files[0];
    }

    private File[] showOpenDialog(boolean multi,String name){
        return this.showOpenDialog(multi,"Open",name,false);
    }

    /**
     *
     * @param name Name of file filter
     */
    public File[] showOpenDialog(boolean multi,String title, String name){
        return this.showOpenDialog(multi,title,name,false);
    }

    /**
     *
     * @param name Name of file filter
     */
    public File[] showOpenDialog(boolean multi,String title, String name, boolean dirs){
        this.fileChooser = new JFileChooser();
        File returnValue[];
        this.makeFilters(name,null,null);
        if (dirs) {
            this.fileChooser.setFileSelectionMode(JFileChooser.FILES_AND_DIRECTORIES);
            // System.err.println();
        } else {
            this.fileChooser.setFileSelectionMode(JFileChooser.FILES_ONLY);
        }
        this.fileChooser.setMultiSelectionEnabled(multi);
        this.fileChooser.setSelectedFile(null);
        this.fileChooser.setSelectedFiles(null);
        if (multi){
            if (this.lastFiles != null) {
                this.fileChooser.setSelectedFiles(this.lastFiles);
            }
        } else {
            if (this.lastFile != null) {
                this.fileChooser.setSelectedFile(this.lastFile);
            }
        }
        int res = this.fileChooser.showDialog(this.parent,title);
        if (res == JFileChooser.APPROVE_OPTION) {
            if( multi ) {
            returnValue = this.fileChooser.getSelectedFiles();
                this.lastFiles = returnValue;
            }else {
                returnValue = new File[1];
                returnValue[0]=this.fileChooser.getSelectedFile();
            }
            this.showEventuallyWarningDialogForNotExistingFiles(returnValue);
            return returnValue;
        } else {
            return null;
        }

    }

    public void showEventuallyWarningDialogForNotExistingFiles(File[] files){
         String out = "Could not found following file(s):\n  ";
         boolean show = false;
         for (int i=0;i<files.length;i++){
             if (!files[i].exists()) {
                out = out + files[i].getPath()+"\n  ";
                show = true;
             }
         }
         if (show) {
             this.showWarningDialog(out);
         }
    }

    public int showEventuallyDiscardDialog(boolean modified, String text){
        if (modified){
            Object[] options = new Object[3];
            options[FileDialogManager.DISCARD] = "Discard";
            options[FileDialogManager.SAVE]    = "Save";
            options[FileDialogManager.CANCEL]  = "Cancel";
            int i = JOptionPane.showOptionDialog(this.parent,
                                                 text+" has been modified!",
                                                 "Warning",
                                                 JOptionPane.DEFAULT_OPTION,
                                                 JOptionPane.WARNING_MESSAGE,
                                                 null, options, options[0]);

            switch (i) {
                case DISCARD : return FileDialogManager.CONTINUE;
                case SAVE    : return FileDialogManager.SAVE;
                case CANCEL: return FileDialogManager.CANCEL;
                default:     return FileDialogManager.CANCEL;
            }

        }
        return FileDialogManager.CONTINUE;
    }

    /**
     * Methode returns file extension of the given file as a string
     * @param file file of which extension should be determined
     * @return file extension
     */
    public String getFileExtension(File file) {

        String fileName;

        fileName = file.getName();
        return fileName.substring( fileName.lastIndexOf(".")+1);

    }

}
