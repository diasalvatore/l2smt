package com.thore.L2SMT;

import com.thore.input.*;
import com.thore.output.*;
import com.thore.language.*;
import org.antlr.v4.runtime.*;
import org.w3c.dom.*;
import javax.xml.parsers.*;
import java.io.*;
import java.util.*;
import org.apache.commons.cli.CommandLine;
import org.apache.logging.log4j.core.config.*;
import org.apache.logging.log4j.core.LoggerContext;
import org.apache.logging.log4j.*;
import org.fusesource.jansi.AnsiConsole;
import static org.fusesource.jansi.Ansi.*;
import static org.fusesource.jansi.Ansi.Color.*;

public class L2SMTMain {
    private Logger logger = LogManager.getFormatterLogger(L2SMTMain.class.getName());    
    public static boolean DEBUG = false;
    public static boolean SUPERDEBUG = false;
    public static String  DIR  = "tmp/";
    public static String  NAME = "request";

    public static String getFilename() {
        return DIR+NAME;
    }

    public static void main(final String[] args) throws Exception {
        LCommandLineParser clp = new LCommandLineParser();
        CommandLine cmd = clp.parse(args);
        AnsiConsole.systemInstall();


        for (String file : cmd.getArgList()) {
            boolean xmlParsing = (  cmd.hasOption("xml") 
                                    || (cmd.hasOption("f") && cmd.getOptionValue("f").toLowerCase().equals("xml"))
                                    || file.toLowerCase().endsWith("xml")
                                 );
            boolean lParsing =   (  cmd.hasOption("l") 
                                    || (cmd.hasOption("f") && cmd.getOptionValue("f").toLowerCase().equals("l"))
                                    || file.toLowerCase().endsWith("l")
                                 );

            if (!xmlParsing && !lParsing) {
                System.err.println("Cannot recognize input file format for: "+file+". Please specify --xml or --l or provide filename with extension");
                System.exit(-1);
            }

            if (cmd.hasOption("o")) {
                NAME = cmd.getOptionValue("o");
            }

            // debug
            if (cmd.hasOption("d")) {
                LoggerContext ctx = (LoggerContext) LogManager.getContext(false);
                Configuration config = ctx.getConfiguration();
                LoggerConfig loggerConfig = config.getLoggerConfig(LogManager.ROOT_LOGGER_NAME); 
                loggerConfig.setLevel(Level.DEBUG);
                ctx.updateLoggers();
                DEBUG = true;
            }

            if (cmd.hasOption("dd")) {
                SUPERDEBUG = true;
            }
            // XML -> L
            String[] l_sources = new String[0];
            if (xmlParsing) { 
                Request request = XMLRequestParser.parseFile(file);
                l_sources = new String[] { request.toL() };
            }

            // L -> SMT
            for (int i=0; i<l_sources.length; i++) {
                String l_source = l_sources[i];
                if (SUPERDEBUG) {
                    PrintStream out;
                    out = new PrintStream(new FileOutputStream(DIR+"request.l"));
                    out.print(l_source);                   
                    System.out.println(ansi().render("@|magenta \n\nTranslation of request: "+DIR+"request.l |@"));
                }
                L2SMTLexer lexer = new L2SMTLexer(new ANTLRInputStream(l_source));
                L2SMTParser l2smt_parser = new L2SMTParser(new CommonTokenStream(lexer));
                l2smt_parser.program(); // root production
                List<SystemState> sss = l2smt_parser.getSystemStates();

                // output
                for (int j=0; j<sss.size(); j++) {
                    SystemState ss = sss.get(j);
                    // if (cmd.hasOption("dd")) {
                    //     System.out.println("\n\n\n---------============ "+i+"."+j+".1 L ============---------");
                    //     printWithNumbers(l_source.split("\n"));
                    // }
                    
                    String smt_source = ss.getSMT();

                }

                // execution
                if (cmd.hasOption("z3")) {
                    SystemStateExecutor exec = new SystemStateExecutor(sss);
                    TheoremProver z3 = new Z3();
                    exec.setTheoremProver(z3);

                    exec.solve();
                    if (cmd.hasOption("o")) {
                        i = 0;
                        PrintStream out;
                        out = new PrintStream(new FileOutputStream(cmd.getOptionValue("o")+".l"));
                        out.print(l_source);                          

                        for (SystemStateExecutor.ExecState e : exec.getStack()) {
                            String output_filename = cmd.getOptionValue("o") + (i>0?i:"");
                              
                            out = new PrintStream(new FileOutputStream(output_filename+".smt"));
                            out.print(e.getResolvedState().getSMT());
                            i++;
                        }
                    } 

                }

            }

        }
    }

    public static void printWithNumbers(String[] lines) {
        int i = 1;
        for (String line : lines) {
            System.out.println((i++)+": "+line);
        } 
    }
}
