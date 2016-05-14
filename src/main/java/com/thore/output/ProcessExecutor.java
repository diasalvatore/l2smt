package com.thore.output;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.OutputStream;
import java.io.OutputStreamWriter;
import java.util.Scanner;
import java.util.*;

public class ProcessExecutor {
    private String cmd;

    public ProcessExecutor(String cmd) {
        this.cmd = cmd;
    }
    
    public List<String> run(String input) {
        List<String> output = new LinkedList<>();
        
        try {
            Process process = Runtime.getRuntime().exec(cmd+"  ");
            BufferedWriter writer = new BufferedWriter(new OutputStreamWriter(process.getOutputStream()));
            writer.write(input);
            writer.close();

            BufferedReader reader = new BufferedReader(new InputStreamReader(
                    process.getInputStream()));
            
            String line;
            while ((line = reader.readLine()) != null) {
                output.add(line);
            }
            reader.close();
            
            BufferedReader errorReader = new BufferedReader(
                    new InputStreamReader(process.getErrorStream()));
            while ((line = errorReader.readLine()) != null) {
                output.add(line);
            }
            errorReader.close();
        } catch (IOException e) {
            System.out.println(e);
        }

        return output;
    }
}
