package com.thore.output;

import java.util.*;
import java.util.regex.*;
import org.apache.commons.lang3.math.*;
import com.thore.language.*;



public interface TheoremProver {
    void    solve(SystemState s);
	String  getRawOutput();
	boolean isSat();
	Map<String, String> getResolved();
	String  getWrongVar();
}