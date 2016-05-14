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

    public SystemStateExecutor(List<SystemState> states) {
        this.states = states;
    }
    
    public void setTheoremProver(TheoremProver tp) {
        this.tp = tp;
    }

    public void solve() {
        int step = 0;
        boolean solved = false;

        while (!solved && step < states.size()) {
            SystemState s = states.get(step);

            log(String.format("Executing step %d", step));
            tp.solve(s);
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
