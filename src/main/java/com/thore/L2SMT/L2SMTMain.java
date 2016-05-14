package com.thore.L2SMT;

import com.thore.input.*;
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


public class L2SMTMain {
    private Logger logger = LogManager.getFormatterLogger(L2SMTMain.class.getName());    

    public static void main(final String[] args) throws Exception {
        LCommandLineParser clp = new LCommandLineParser();
        CommandLine cmd = clp.parse(args);

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

            // debug
            if (cmd.hasOption("d")) {
                LoggerContext ctx = (LoggerContext) LogManager.getContext(false);
                Configuration config = ctx.getConfiguration();
                LoggerConfig loggerConfig = config.getLoggerConfig(LogManager.ROOT_LOGGER_NAME); 
                loggerConfig.setLevel(Level.DEBUG);
                ctx.updateLoggers();
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
                L2SMTLexer lexer = new L2SMTLexer(new ANTLRInputStream(l_source));
                L2SMTParser l2smt_parser = new L2SMTParser(new CommonTokenStream(lexer));
                l2smt_parser.program(); // root production
                SystemState ss = l2smt_parser.getSystemState();

                for (int j=0; j<ss.getStepCount(); j++) {
                    if (cmd.hasOption("dd")) {
                        System.out.println("\n\n\n---------============ "+i+"."+j+".1 L ============---------");
                        printWithNumbers(l_source.split("\n"));
                    }
                    
                    String smt_source = ss.getSMT(j);

                    // output
                    if (!cmd.hasOption("q")) {
                        if (cmd.hasOption("o")) {
                            String output_filename = cmd.getOptionValue("o") + (i>0?i:"") + (j>0?"-"+j:"");

                            
                            PrintStream out = new PrintStream(new FileOutputStream(output_filename+".l"));
                            out.print(l_source);                          
                              
                            out = new PrintStream(new FileOutputStream(output_filename+".smt"));
                            out.print(smt_source);
                        } else { // stdout
                            if (!cmd.hasOption("d")) {
                                System.out.println(smt_source);
                            }
                        }
                    }


                    if (cmd.hasOption("dd")) {
                        System.out.println("\n\n\n---------============ "+i+"."+j+".2 SMT ============---------");
                        printWithNumbers(smt_source.split("\n"));
                    }            

                    // execute
                    if (cmd.hasOption("z3")) {
                        // System.out.println("Verifying set of constraints: { "+ls.getOrderedLabels(i) + "}");
                        ProcessExecutor p = new ProcessExecutor("z3 -in");
                        Z3OutputParser z3_out = new Z3OutputParser(Arrays.asList(smt_source.split("\n")), p.run(smt_source));

                        // printWithNumbers(smt_source.split("\n"));
                        if (cmd.hasOption("dd")) System.out.println(z3_out.raw());
                        System.out.println(z3_out.toString());
                        
                        if (!z3_out.isSat() && !cmd.hasOption("i")) {
                            System.exit(-1);
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
