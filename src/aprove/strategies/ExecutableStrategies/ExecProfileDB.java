package aprove.strategies.ExecutableStrategies;

import java.io.*;
import java.sql.*;
import java.util.*;
import java.util.logging.*;

import aprove.prooftree.Obligations.*;
import aprove.strategies.UserStrategies.*;

/**
 * Profiler for strategies. Executes a given strategy and writes the needed time
 * to the given database.
 * @author Andreas Kelle-Emden
 */
public class ExecProfileDB extends ExecutableStrategy {
    private static final Logger log =
        Logger.getLogger("aprove.strategies.ExecutableStrategies.ExecProfileDB");

    private ExecutableStrategy exStr;
    private boolean isWaiting = false;
    private long time = 0;
    private String procName;
    private static Connection conn = null;
    private static Map<String, Integer> knownIDs = null;
    private static Object synch = new Object();

    public static final String PROFILETABLE = "profiling";
    public static final String INDEXTABLE   = "profilingindex";

    private String read(FileInputStream stream) {
        String output = "";
        char c = '\0';
        do {
            try {
                if (stream.available() > 0) {
                    c = (char)stream.read();
                } else {
                    c = ':';
                }
            }
            catch (IOException e) {
                c = ':';
            }
            if (!":\n\0".contains(String.valueOf(c))) {
                output += c;
            }
        } while (c != ':');
        return output;
    }

    public ExecProfileDB(String procName, UserStrategy str, BasicObligationNode pos, RuntimeInformation rti) throws UnableToConnectToDatabaseException {
        super(rti);

        boolean createTable = false;

        this.exStr = str.getExecutableStrategy(pos, rti);
        this.procName = procName;
        // Init DB
        synchronized(ExecProfileDB.synch) {
            if (ExecProfileDB.conn == null) {
                try {
                    FileInputStream stream = null;
                    try {
                        stream = new FileInputStream(System.getProperty("user.home")+"/.bench.db");
                    } catch (IOException e) {
                        ExecProfileDB.log.log(Level.SEVERE, "Could not find ~/.bench.db; cannot procceed.");
                        ExecProfileDB.log.log(Level.SEVERE, "Please create this file with the following form:");
                        ExecProfileDB.log.log(Level.SEVERE, "<hostname>:<name of db>:<your username>:<your password>");
                        throw new UnableToConnectToDatabaseException();
                    }
                    Class.forName("org.postgresql.Driver");

                    String host = this.read(stream);
                    String dbname = this.read(stream);
                    String user = this.read(stream);
                    String password = this.read(stream);

                    String url = "jdbc:postgresql://" + host + "/" + dbname;
                    Properties dbprops = new Properties();
                    dbprops.setProperty("user", user);
                    dbprops.setProperty("password", password);
                    //dbprops.setProperty("ssl","false");
                    ExecProfileDB.conn = DriverManager.getConnection(url, dbprops);
                } catch (ClassNotFoundException ex) {
                    // This should never happen.
                } catch (SQLException ex) {
                    ExecProfileDB.log.log(Level.SEVERE, "Could not connect to database; cannot proceed.");
                    ExecProfileDB.log.log(Level.SEVERE, ex.toString());
                    throw new UnableToConnectToDatabaseException();
                } catch (RuntimeException ex) {
                    ExecProfileDB.log.log(Level.SEVERE, ex.toString()+ "; cannot proceed.");
                    ExecProfileDB.log.log(Level.SEVERE, ex.toString());
                    throw new UnableToConnectToDatabaseException();
                }
                try{
                    PreparedStatement ps = ExecProfileDB.conn.prepareStatement("SELECT relname FROM pg_class WHERE relname = ?");
                    ps.setString(1, ExecProfileDB.INDEXTABLE);
                    ResultSet rs = ps.executeQuery();
                    if (rs.next()) {
                        rs.getString("relname");
                    } else {
                        createTable = true;
                    }
                }
                catch(SQLException e) {
                    // Something went wrong while checking the database - probably we have to create the tables here
                    ExecProfileDB.log.log(Level.WARNING, e.toString());
                    createTable = true;
                }

                if (createTable) {
                    try{
                        PreparedStatement ps = ExecProfileDB.conn.prepareStatement("CREATE TABLE " + ExecProfileDB.INDEXTABLE + " (idindex SERIAL PRIMARY KEY, idstring varchar(100))");
                        ps.execute();
                    }
                    catch(SQLException e) {
                        ExecProfileDB.log.log(Level.WARNING, e.toString());
                    }
                    try{
                        PreparedStatement ps = ExecProfileDB.conn.prepareStatement("CREATE TABLE " + ExecProfileDB.PROFILETABLE + " (idindex integer REFERENCES " + ExecProfileDB.INDEXTABLE + "(idindex) ON DELETE CASCADE, milis INT, result varchar(100))");
                        ps.execute();
                    }
                    catch(SQLException e) {
                        ExecProfileDB.log.log(Level.WARNING, e.toString());
                    }

                }
                ExecProfileDB.knownIDs = new LinkedHashMap<String, Integer>();
            }
        }
    }

    @Override
    ExecutableStrategy exec() {
        ExecutableStrategy retVal;
        if (!this.exStr.isNormal()) {
            if (!this.isWaiting) {
                this.time = -System.currentTimeMillis();
                this.isWaiting = true;
            }
            ExecutableStrategy newEx = this.exStr.exec();
            if (newEx != null) {
                this.time += System.currentTimeMillis();
                //String sOut = time + "\t" + s + "\t" + newEx + "\n";
                int procID = 0;
                ResultSet rs = null;
                boolean indexExists = true;
                if (ExecProfileDB.knownIDs.containsKey(this.procName)) {
                    procID = ExecProfileDB.knownIDs.get(this.procName).intValue();
                } else {
                    try{
                        PreparedStatement ps = ExecProfileDB.conn.prepareStatement("SELECT idindex FROM " + ExecProfileDB.INDEXTABLE + " WHERE idstring = ? LIMIT 1");
                        ps.setString(1, this.procName);
                        rs = ps.executeQuery();
                        if (!rs.next()) {
                            indexExists = false;
                        }
                    }
                    catch(SQLException e) {
                        ExecProfileDB.log.log(Level.WARNING, e.toString());
                        indexExists = false;
                    }
                    if (indexExists) {
                        try {
                            procID = rs.getInt("idindex");
                            ExecProfileDB.knownIDs.put(this.procName, procID);
                        }
                        catch (SQLException e) {
                            ExecProfileDB.log.log(Level.WARNING, e.toString());
                        }
                    } else {
                        try{
                            String s = ExecProfileDB.INDEXTABLE + "_idindex_seq";
                            PreparedStatement ps = ExecProfileDB.conn.prepareStatement("SELECT nextval(?)");
                            ps.setString(1, s);
                            rs = ps.executeQuery();
                            rs.next();
                            procID = rs.getInt("nextval");
                            ps = ExecProfileDB.conn.prepareStatement("INSERT INTO " + ExecProfileDB.INDEXTABLE + " (idindex, idstring) VALUES (?, ?)");
                            //ps.setString(1, INDEXTABLE);
                            ps.setInt(1, procID);
                            ps.setString(2, this.procName);
                            ps.execute();
                            ExecProfileDB.knownIDs.put(this.procName, procID);
                        }
                        catch (SQLException e) {
                            ExecProfileDB.log.log(Level.WARNING, e.toString());
                        }

                    }
                }
                try{
                    PreparedStatement ps = ExecProfileDB.conn.prepareStatement("INSERT INTO " + ExecProfileDB.PROFILETABLE + " (idindex, milis, result) VALUES (?, ?, ?)");
                    ps.setInt(1, procID);
                    ps.setLong(2, this.time);
                    ps.setString(3, newEx.toString());
                    ps.execute();
                }
                catch (SQLException e) {
                    ExecProfileDB.log.log(Level.WARNING, e.toString());
                }

                this.isWaiting = false;
            }
            if (newEx == null) {
                retVal =  null;
            } else {
                this.exStr = newEx;
                retVal =  this;
            }
        } else {
            retVal =  this.exStr;
        }
        return retVal;
    }

    @Override
    void stop(String reason) {
    }

    @Override
    public String toString() {
        return "Profile("+this.exStr+")";
    }

}