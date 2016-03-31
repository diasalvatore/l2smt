package com.thore.L2SMT;

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


    private static void runCommandAndGetOutput() {
        String command = "ping www.codejava.net";

        try {
            Process process = Runtime.getRuntime().exec(command);

            BufferedReader reader = new BufferedReader(new InputStreamReader(
                    process.getInputStream()));
            String line;
            while ((line = reader.readLine()) != null) {
                System.out.println(line);
            }
            reader.close();
            
        } catch (IOException e) {
            e.printStackTrace();
        }
    }
    
    private static void runCommandAndWait() {
        String command = "ping www.codejava.net";
        
        try {
            Process process = Runtime.getRuntime().exec(command);
            
            BufferedReader reader = new BufferedReader(new InputStreamReader(
                    process.getInputStream()));
            String line;
            while ((line = reader.readLine()) != null) {
                System.out.println(line);
            }
            reader.close();
            
            int exitValue = process.waitFor();
            if (exitValue != 0) {
                System.out.println("Abnormal process termination");
            }
            
        } catch (IOException e) {
            e.printStackTrace();
        } catch (InterruptedException ex) {
            ex.printStackTrace();
        }
    }
    
    private static void runCommandTypically() {
        String command = "ping www.codejava.net";
        
        try {
            Process process = Runtime.getRuntime().exec(command);
            
            BufferedReader reader = new BufferedReader(new InputStreamReader(
                    process.getInputStream()));
            String line;
            while ((line = reader.readLine()) != null) {
                System.out.println(line);
            }
            reader.close();
            
            process.destroy();
            if (process.exitValue() != 0) {
                System.out.println("Abnormal process termination");
            }
            
        } catch (IOException e) {
            e.printStackTrace();
        }
    }
    
    private static void runCommandAndSendInput() {
        String command = "cmd /c date";
        
        try {
            Process process = Runtime.getRuntime().exec(command);
            
            BufferedWriter writer = new BufferedWriter(
                    new OutputStreamWriter(process.getOutputStream()));
            writer.write("09-20-14");
            writer.close();
            
            BufferedReader reader = new BufferedReader(new InputStreamReader(
                    process.getInputStream()));
            String line;
            while ((line = reader.readLine()) != null) {
                System.out.println(line);
            }
            reader.close();
        } catch (IOException e) {
            e.printStackTrace();
        }
    }

    private static void runCommandAndGetErrorOutput() {
        String command = "cmd /c verr";

        try {
            Process process = Runtime.getRuntime().exec(command);

            BufferedReader reader = new BufferedReader(new InputStreamReader(
                    process.getInputStream()));
            String line;
            while ((line = reader.readLine()) != null) {
                System.out.println(line);
            }
            reader.close();

            System.out.println("ERROR:");
            
            BufferedReader errorReader = new BufferedReader(
                    new InputStreamReader(process.getErrorStream()));
            while ((line = errorReader.readLine()) != null) {
                System.out.println(line);
            }
            errorReader.close();

        } catch (IOException e) {
            e.printStackTrace();
        }
    }

    private static void runCommandArray() {
        String commandArray[] = {"cmd", "/c", "dir", "C:\\Program Files"};

        try {
            Process process = Runtime.getRuntime().exec(commandArray);

            BufferedReader reader = new BufferedReader(new InputStreamReader(
                    process.getInputStream()));
            String line;
            while ((line = reader.readLine()) != null) {
                System.out.println(line);
            }
            reader.close();
            
        } catch (IOException e) {
            e.printStackTrace();
        }
    }
}
