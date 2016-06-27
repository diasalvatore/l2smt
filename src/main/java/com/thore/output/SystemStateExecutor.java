package com.thore.output;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.OutputStream;
import java.io.OutputStreamWriter;
import java.util.Scanner;
import java.util.*;
import com.thore.language.*;
import com.thore.L2SMT.*;
import org.apache.logging.log4j.*;
import java.io.*;
import static org.fusesource.jansi.Ansi.*;
import static org.fusesource.jansi.Ansi.Color.*;

public class SystemStateExecutor {
    private Logger logger = LogManager.getFormatterLogger(getClass().getName());
    private List<SystemState> states;
    private TheoremProver tp;
    private Stack<ExecState> stack = new Stack<>();
    private int step;
    private int execCounter = 0;

    public class ExecState {
        public SystemState state;
        public Map<String, String> allVars = new HashMap<>();
        public Map<String, String> stateVars = new HashMap<>();
        public Map<String, String> noVars = new HashMap<>();
        private String label;

        public ExecState(SystemState state, Map<String, String> allVars) {
            this.state = state;

            for (Map.Entry<String, String> entry : allVars.entrySet()) {
                this.allVars.put(entry.getKey(), entry.getValue());
            }
        }

        public boolean hasVar(String var) {
            return stateVars.keySet().contains(var);
        }

        public void setStateVars(Map<String, String> stateVars) {
            for (Map.Entry<String, String> entry : stateVars.entrySet()) {
                this.stateVars.put(entry.getKey(), entry.getValue());
            }
        }

        public void unluckyGuess(String var) {
            noVars.put(var, stateVars.get(var));
            stateVars.remove(var);
        }

        public SystemState getResolvedState() {
            SystemState res = state.clone();

            for (Map.Entry<String, String> entry : allVars.entrySet()) {
                logger.debug(String.format("Adding resolved: %s -> %s", entry.getKey(), entry.getValue()));
                res.addResolved(entry.getKey(), entry.getValue());
            }

            for (Map.Entry<String, String> entry : noVars.entrySet()) {
                logger.debug(String.format("No: %s -> %s", entry.getKey(), entry.getValue()));
                res.addNoVar(entry.getKey(), entry.getValue());
            }

            return res;
        }
        
        public void setLabel(String label) {
            this.label = label;
        }

        public String toString() {
            return "*** STATE "+label+ " ***\n" + 
                    "vars:  " + allVars.toString() + "\n" + 
                    "myVar: " + stateVars.toString();
        }
    }

    public Stack<ExecState> getStack() {
        return stack;
    }

    public List<SystemState> getStates() {
        return states;
    }

    public SystemStateExecutor(List<SystemState> states) {
        this.states = states;
    }
    
    public void setTheoremProver(TheoremProver tp) {
        this.tp = tp;
    }

    public void solve() {
        step = 0;
        boolean impossible = false;
        boolean rollback = false;
        Map<String, String> allVar = new HashMap<>();

        while (!impossible && step < states.size()) {
            ExecState   e   = new ExecState(states.get(step), allVar);
            boolean     sat = false;

            sat = executeState(e, allVar);
            if (!sat) { // rollback
                String wrongvar = tp.getWrongVar();
                print("    the previous resolution of @|yellow "+wrongvar+"|@ makes the formula unsatisfable, rolling back");
                
                if (rollback) { // I was already rolling back
                    impossible = true;
                } else {
                    ExecState lastGoodState = null;
                    boolean found = false;
                    while (!found && !stack.isEmpty()) { // looking for the state which set the wrong var
                        lastGoodState = stack.pop();
                        step--;
                        if (lastGoodState.hasVar(wrongvar)) {
                            found = true;
                            print("@|red <-- Rolling Back! \n |@");
                        }
                    }
                    
                    if (found) { // found that state
                        lastGoodState.unluckyGuess(wrongvar); // avoid that the variable will resolved with the wrong one again
                        
                        // ri-executing the state
                        impossible = !executeState(lastGoodState, allVar);
                    } else {
                        impossible = true;
                    }                    
                }
            }
        }

        // for (ExecState e : stack) {
        //     print(e.toString());
        // }
    }


    public boolean executeState(ExecState e, Map<String, String> allVar) {
        execCounter++;
        print("@|cyan ==> Executing Step: "+step+"|@");

        SystemState s = e.getResolvedState(); // this substitutes all unknown variable in state and get a new state
        if (L2SMTMain.SUPERDEBUG) {
            PrintStream out;
            try {
                String filename = L2SMTMain.getFilename()+execCounter+".in.z3";
                out = new PrintStream(new FileOutputStream(filename));
                out.print(s.getSMT());              
                print("    @|magenta SMT request: "+filename+" |@");                
            } catch (Exception ex) {
                System.err.println(ex.toString());
            }
        }

        Map<String, String> stateVar = new HashMap<>();
    
        e.setLabel(String.valueOf(step));

        // stack
        stack.push(e);

        // solving
        tp.solve(s);

        if (L2SMTMain.SUPERDEBUG) {
            PrintStream out;
            try {
                String filename = L2SMTMain.getFilename()+execCounter+".out.z3";
                out = new PrintStream(new FileOutputStream(filename));
                out.print(tp.getRawOutput());              
                print("    @|magenta SMT response: "+filename+" |@");                
            } catch (Exception ex) {
                System.err.println(ex.toString());
            }
        }

        if (tp.isSat()) {
            print("@|green :)  SAT|@isfable!\n");    
        } else {
            print("@|red :(  UNSAT|@isfable!");
        }

        
        // updating resolved variable
        stateVar = tp.getResolved(); 
        for (Map.Entry<String, String> entry : stateVar.entrySet()) {
            allVar.put(entry.getKey(), entry.getValue());
        }
        if (stateVar.size() > 0) {
            print("    the following variables have been resolved: @|yellow "+stateVar.toString()+"|@");
        }
        e.setStateVars(stateVar);

        step++;
        return tp.isSat();
    }


    public void print(String s) {
        // if (L2SMTMain.DEBUG) {
            System.out.println(ansi().render(s));
        
    }
}
