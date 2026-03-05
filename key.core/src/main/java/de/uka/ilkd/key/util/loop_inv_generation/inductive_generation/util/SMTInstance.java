package de.uka.ilkd.key.util.loop_inv_generation.inductive_generation.util;

import de.uka.ilkd.key.java.Services;
import org.key_project.prover.sequent.Sequent;

import java.io.*;
import java.util.HashMap;
import java.util.Map;
import java.util.concurrent.*;

public class SMTInstance {

    private final Sequent sequent;
    private final Services services;
    private SMTResult result;

    public SMTInstance(Sequent sequent, Services services) {
        this.sequent = sequent;
        this.services = services;
    }

    public void processSMTProblem() {
        SMTTranslator translator = new SMTTranslator(services);
        String smtProblem = translator.translateSequent(sequent);

        try {
            ProcessBuilder processBuilder = new ProcessBuilder("cvc5", "--lang=smt2");
            processBuilder.redirectErrorStream(true); // Redirect errors to the output stream
            Process process = processBuilder.start();

            // Write the smtProblem to the cvc5 process
            try (BufferedWriter writer = new BufferedWriter(new OutputStreamWriter(process.getOutputStream()))) {
                writer.write(smtProblem);
                writer.flush();
            }

            // Read the output of the cvc5 process
            StringBuilder resultBuffer = new StringBuilder();
            try (BufferedReader reader = new BufferedReader(new InputStreamReader(process.getInputStream()))) {
                String line;
                while ((line = reader.readLine()) != null) {
                    resultBuffer.append(line).append(System.lineSeparator());
                }
            }

            // Ensure the process finishes execution
            process.waitFor(10, TimeUnit.SECONDS);

            processResult(resultBuffer.toString());
        } catch (IOException | InterruptedException e) {
            System.err.println("An error occurred while processing the SMT problem: " + e.getMessage());
            e.printStackTrace();
        }
    }

    private void processResult(String resultString) {
        String[] resultLines = resultString.split("\n");
        String satResultLine = resultLines[0];
        String counterexampleLine = resultLines[1].substring(2, resultLines[1].length() - 2);

        boolean valid = satResultLine.endsWith("unsat");
        Map<String, Integer> counterexample = new HashMap<>();
        if (!valid) {
            for (String counterexampleAssignment : counterexampleLine.split("\\) \\(")) {
                String[] splitCounterexample = counterexampleAssignment.split(" ");
                counterexample.put(splitCounterexample[0], Integer.parseInt(splitCounterexample[1]));
            }
        }

        result = new SMTResult(valid, counterexample);
    }

    public SMTResult result() {
        return result;
    }
}
