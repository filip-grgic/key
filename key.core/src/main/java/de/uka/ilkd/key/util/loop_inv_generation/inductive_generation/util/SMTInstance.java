package de.uka.ilkd.key.util.loop_inv_generation.inductive_generation.util;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.settings.DefaultSMTSettings;
import de.uka.ilkd.key.settings.NewSMTTranslationSettings;
import de.uka.ilkd.key.settings.ProofIndependentSMTSettings;
import de.uka.ilkd.key.smt.SMTProblem;
import de.uka.ilkd.key.smt.SMTSettings;
import de.uka.ilkd.key.smt.SMTSolverResult;
import de.uka.ilkd.key.smt.SolverLauncher;
import de.uka.ilkd.key.smt.solvertypes.SolverType;
import de.uka.ilkd.key.smt.solvertypes.SolverTypeImplementation;
import de.uka.ilkd.key.smt.solvertypes.SolverTypes;
import org.key_project.prover.sequent.Sequent;
import org.key_project.util.collection.Pair;

import java.io.*;
import java.util.*;
import java.util.concurrent.*;

public class SMTInstance {

    private final Sequent sequent;
    private final Services services;
    private SMTResult result;

    private final SolverType smtSolver = SolverTypes.getSolverTypes().stream()
            .filter(it -> it.getClass().equals(SolverTypeImplementation.class)
                    && it.getName().equals("cvc5"))
            .findFirst().orElse(null);

    public SMTInstance(Sequent sequent, Services services) {
        this.sequent = sequent;
        this.services = services;
    }

    public void processSMTProblem() {

        SMTProblem keySmtProblem = new SMTProblem(sequent, services);

        SolverLauncher launcher = getSolverLauncher();
        launcher.launch(keySmtProblem, services, smtSolver);

        if (keySmtProblem.getFinalResult().isValid().equals(SMTSolverResult.ThreeValuedTruth.VALID)) {
            result = new SMTResult(true, new HashMap<>(), new HashMap<>());
            return;
        }

        SMTTranslator translator = new SMTTranslator(services);
        String smtProblem = "";
        try {
            smtProblem = translator.translateSequent(sequent);
        } catch (IllegalArgumentException e) {
            result = new SMTResult(false, new HashMap<>(), new HashMap<>());;
            return;
        }

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
        String counterexampleLine = resultLines[1].substring(1, resultLines[1].length() - 1);

        Map<String, String> counterexampleAssignments = parseCounterexample(counterexampleLine);

        boolean valid = satResultLine.endsWith("unsat");
        Map<String, Integer> counterexampleConstants = new HashMap<>();
        Map<String, List<Pair<Integer, Integer>>> counterexampleArrays = new HashMap<>();
        if (!valid) {
            for (String ceVariable : counterexampleAssignments.keySet()) {
                if (counterexampleAssignments.get(ceVariable).contains("as const (Array")) {
                    counterexampleArrays.put(ceVariable, parseArray(counterexampleAssignments.get(ceVariable)));
                } else {
                    String valueString = counterexampleAssignments.get(ceVariable).replaceAll("[() ]", "");
                    counterexampleConstants.put(ceVariable, Integer.parseInt(valueString));
                }
            }
        }

        result = new SMTResult(valid, counterexampleConstants, counterexampleArrays);
    }

    private List<Pair<Integer, Integer>> parseArray(String arrayString) {

        SortedMap<Integer, Integer> arrayValues = new TreeMap<>();

        while (!arrayString.startsWith("((as const (Array")) {
            int spaceIndex = arrayString.indexOf(" ");

            String parameterString = arrayString.substring(spaceIndex + 1, arrayString.length() - 1);

            List<String> parameters = new ArrayList<>();
            StringBuilder current = new StringBuilder();
            int openedAmount = 0;
            for (char c: parameterString.toCharArray()) {
                current.append(c);
                if (c == '(') {
                    openedAmount++;
                } else if (c == ')') {
                    openedAmount--;
                } else if (c == ' ' && openedAmount == 0) {
                    parameters.add(current.toString().trim());
                    current = new StringBuilder();
                }
            }
            parameters.add(current.toString().trim());

            int index = Integer.parseInt(parameters.get(1).replaceAll("[() ]", ""));
            int value = Integer.parseInt(parameters.get(2).replaceAll("[() ]", ""));

            arrayValues.put(index, value);

            arrayString = parameters.get(0);
        }

        int max = 0;
        for (int key : arrayValues.keySet()) {
            if (key > max) {
                max = key;
            }
        }

        List<Pair<Integer, Integer>> result = new ArrayList<>();

        arrayValues.forEach((k, v) -> result.add(new Pair<>(k, v)));

        return result;
    }

    private Map<String, String> parseCounterexample(String counterexampleLine) {
        Map<String, String> result = new HashMap<>();
        int openedAmount = 0;

        StringBuilder current = new StringBuilder();

        for (char c: counterexampleLine.toCharArray()) {
            current.append(c);
            if (c == '(') {
                openedAmount++;
            } else if (c == ')') {
                openedAmount--;
                if (openedAmount == 0) {
                    String counterexample = current.toString().trim();
                    counterexample = counterexample.substring(1, counterexample.length() - 1);
                    int spaceIndex = counterexample.indexOf(" ");
                    String variableName = counterexample.substring(0, spaceIndex);
                    String value = counterexample.substring(spaceIndex + 1);
                    result.put(variableName, value);
                    current = new StringBuilder();
                }
            }
        }

        return result;
    }

    private SolverLauncher getSolverLauncher() {
        ProofIndependentSMTSettings piSettings = ProofIndependentSMTSettings.getDefaultSettingsData();

        SMTSettings smtSettings = new DefaultSMTSettings(
                services.getProof().getSettings().getSMTSettings(),
                piSettings,
                new NewSMTTranslationSettings(),
                services.getProof()
        );

        return new SolverLauncher(smtSettings);
    }

    public SMTResult result() {
        return result;
    }
}
