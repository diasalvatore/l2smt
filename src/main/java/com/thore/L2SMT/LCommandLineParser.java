package com.thore.L2SMT;

import org.apache.commons.cli.*;

@SuppressWarnings( "deprecation" )
public class LCommandLineParser {
    private Options options = new Options();
    private CommandLineParser parser = new BasicParser();
    private CommandLine cmd = null;

    public LCommandLineParser() {
        options.addOption("d", "debug", false, "Show debug informations");
        options.addOption("dd", "extradebug", false, "Show translations");
        options.addOption("h", "help", false, "Prints this help");
        options.addOption("o", "output", true, "Writes output in specified files (default is stdout)");
        options.addOption("q", "quiet", false, "Don't show output (it should be used with -z3 or -x)");
        options.addOption("i", "ignore-unsat", false, "Ignore unsat and don't stop when a formula is unsat (useful with -z3 and incremental verification) ");
        options.addOption("x", "execute", true, "Execute command on SMT output");
        options.addOption("z3", null, false, "Runs z3 on SMT output");
        options.addOption("f", "format", true, "Specifies input format (xml or l), default is auto guessing base on file extension (.xml or .l)");
        options.addOption(null, "xml", false, "Force parsing as XML file");
        options.addOption(null, "l", false, "Force parsing as L file");
    }

    public CommandLine parse(String args[]) {
        if (args.length == 0) help();

        try {
            cmd = parser.parse(options, args);

            if (cmd.hasOption("h")) help();
        } catch (ParseException e) {
            help();
        }

        return cmd;
    }

    public void help() {
        HelpFormatter formatter = new HelpFormatter();
        formatter.printHelp("l2smt [options] file1 [file2] ...", options);
        System.exit(0);
    }
}
