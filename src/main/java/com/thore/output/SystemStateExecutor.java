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


public class SystemStateExecutor {
    private List<SystemState> states;
    private TheoremProver tp;

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
        int step = 0;
        boolean solved = false;
        Map<String, String> r = new HashMap<>();

        while (!solved && step < states.size()) {
            SystemState s = states.get(step);

            log(String.format("Executing step %d", step));
            log(r.toString());

            // subs
            for (Map.Entry<String, String> entry : r.entrySet()) {
                s.addResolved(entry.getKey(), entry.getValue());
            }

            tp.solve(s);
            r = tp.getResolved();

            log(tp.toString());

            step++;
        }
    }

    public void log(String s) {
        if (L2SMTMain.DEBUG) {
            System.out.println(s);
        }
    }
}
