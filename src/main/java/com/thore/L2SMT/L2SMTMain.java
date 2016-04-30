package com.thore.L2SMT;

import com.thore.input.*;
import org.antlr.v4.runtime.*;
import org.w3c.dom.*;
import javax.xml.parsers.*;
import java.io.*;
import java.util.*;
import org.apache.commons.cli.CommandLine;


public class L2SMTMain {
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

            // XML -> L
            String[] l_sources = new String[0];
            if (xmlParsing) { 
                Request request = XMLRequestParser.parseFile(file);
                l_sources = new String[] { request.toL() };
            }

            // L -> SMT
            for (int i=0; i<l_sources.length; i++) {
                String l_source = l_sources[i];


                if (cmd.hasOption("d")) {
                    System.out.println("\n\n\n---------============ "+i+".1 L ============---------");
                    printWithNumbers(l_source.split("\n"));
                }
                
                L2SMTLexer lexer = new L2SMTLexer(new ANTLRInputStream(l_source));
                L2SMTParser l2smt_parser = new L2SMTParser(new CommonTokenStream(lexer));
                l2smt_parser.program(); // root production
                String smt_source = l2smt_parser.getSMT();

                // output
                if (!cmd.hasOption("q")) {
                    if (cmd.hasOption("o")) {
                        String output_filename = cmd.getOptionValue("o") + (i>0?i:"");

                        PrintStream out = new PrintStream(new FileOutputStream(output_filename));
                        out.print(smt_source);
                    } else { // stdout
                        System.out.println(smt_source);
                    }
                }


                if (cmd.hasOption("d")) {
                    // System.out.println("---------============ "+i+".0 XML ============---------");
                    // printWithNumbers(xml.split("\n"));

                    System.out.println("\n\n\n---------============ "+i+".1 L ============---------");
                    printWithNumbers(l_source.split("\n"));

                    System.out.println("\n\n\n---------============ "+i+".2 SMT ============---------");
                    printWithNumbers(smt_source.split("\n"));
                }            

                // execute
                if (cmd.hasOption("z3")) {
                    // System.out.println("Verifying set of constraints: { "+ls.getOrderedLabels(i) + "}");
                    ProcessExecutor p = new ProcessExecutor("z3 -in");
                    Z3OutputParser z3_out = new Z3OutputParser(Arrays.asList(smt_source.split("\n")), p.run(smt_source));

                    // printWithNumbers(smt_source.split("\n"));
                    System.out.println(z3_out.raw());
                    System.out.println(z3_out.toString());
                    
                    if (!z3_out.isSat() && !cmd.hasOption("i")) {
                        System.exit(-1);
                    }
                } 

            }

        }
    }

    public static void main2(final String[] args) throws Exception {
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
                System.err.println("Cannot recognize input file format. Please specify --xml or --l or provide filename with extension");
                System.exit(1);
            }

            // XML -> L
            String xml = new Scanner(new File(file)).useDelimiter("\\Z").next();

            String[] l_sources;
            LabeledSource ls = new LabeledSource();
            if (xmlParsing) {
                XMLParser xmlParser = new XMLParser(file);
                ls = xmlParser.parse();
                if (ls.getOrderedSize() > 0) {
                    l_sources = new String[ls.getOrderedSize()+1];

                    for (int i=0; i<=ls.getOrderedSize(); i++) {
                        l_sources[i] = ls.getOrderedCode(i);
                    } 
                } else {
                    l_sources = new String[] { ls.toString() };    
                }
            } else {
                l_sources = new String[] { new Scanner(new File(file)).useDelimiter("\\Z").next() };
            }

            // L -> SMT
            for (int i=0; i<l_sources.length; i++) {
                String l_source = l_sources[i];
                L2SMTLexer lexer = new L2SMTLexer(new ANTLRInputStream(l_source));
                L2SMTParser l2smt_parser = new L2SMTParser(new CommonTokenStream(lexer));
                l2smt_parser.program(); // root production
                String smt_source = l2smt_parser.getSMT();

                // output
                if (!cmd.hasOption("q")) {
                    if (cmd.hasOption("o")) {
                        String output_filename = cmd.getOptionValue("o") + (i>0?i:"");

                        PrintStream out = new PrintStream(new FileOutputStream(output_filename));
                        out.print(smt_source);
                    } else { // stdout
                        System.out.println(smt_source);
                    }
                }


                if (cmd.hasOption("d")) {
                    System.out.println("---------============ "+i+".0 XML ============---------");
                    printWithNumbers(xml.split("\n"));

                    System.out.println("\n\n\n---------============ "+i+".1 L ============---------");
                    printWithNumbers(l_source.split("\n"));

                    System.out.println("\n\n\n---------============ "+i+".2 SMT ============---------");
                    printWithNumbers(smt_source.split("\n"));
                }            

                // execute
                if (cmd.hasOption("z3")) {
                    System.out.println("Verifying set of constraints: { "+ls.getOrderedLabels(i) + "}");
                    ProcessExecutor p = new ProcessExecutor("z3 -in");
                    Z3OutputParser z3_out = new Z3OutputParser(Arrays.asList(smt_source.split("\n")), p.run(smt_source));

                    System.out.println(z3_out.toString());
                    
                    if (!z3_out.isSat() && !cmd.hasOption("i")) {
                        System.exit(-1);
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
