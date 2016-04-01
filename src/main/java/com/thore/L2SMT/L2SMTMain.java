package com.thore.L2SMT;

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
                System.err.println("Cannot recognize input file format. Please specify --xml or --l or provide filename with extension");
                System.exit(1);
            }

            // XML -> L
            String xml = new Scanner(new File(file)).useDelimiter("\\Z").next();

            String l_source;
            if (xmlParsing) {
                XMLParser xmlParser = new XMLParser(file);
                l_source = xmlParser.parse();
            } else {
                l_source = new Scanner(new File(file)).useDelimiter("\\Z").next();
            }

            // L -> SMT
            L2SMTLexer lexer = new L2SMTLexer(new ANTLRInputStream(l_source));
            L2SMTParser l2smt_parser = new L2SMTParser(new CommonTokenStream(lexer));
            l2smt_parser.program(); // root production
            String smt_source = l2smt_parser.getSMT();

            // output
            if (!cmd.hasOption("q")) {
                if (cmd.hasOption("o")) {
                    String output_filename = cmd.getOptionValue("o");

                    PrintStream out = new PrintStream(new FileOutputStream(output_filename));
                    out.print(smt_source);
                } else { // stdout
                    System.out.println(smt_source);
                }
            }


            if (cmd.hasOption("d")) {
                System.out.println("---------============ 0. XML ============---------");
                printWithNumbers(xml.split("\n"));

                System.out.println("\n\n\n---------============ 1. L ============---------");
                printWithNumbers(l_source.split("\n"));

                System.out.println("\n\n\n---------============ 2. SMT ============---------");
                printWithNumbers(smt_source.split("\n"));
            }            

            // execute
            if (cmd.hasOption("z3")) {
                ProcessExecutor p = new ProcessExecutor("z3 -in");
                Z3OutputParser z3_out = new Z3OutputParser(Arrays.asList(smt_source.split("\n")), p.run(smt_source));

                System.out.println(z3_out.toString());
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
