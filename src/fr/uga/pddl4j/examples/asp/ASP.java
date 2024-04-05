package fr.uga.pddl4j.examples.asp;

import fr.uga.pddl4j.heuristics.state.StateHeuristic;
import fr.uga.pddl4j.parser.DefaultParsedProblem;
import fr.uga.pddl4j.parser.Expression;
import fr.uga.pddl4j.parser.Parser;
import fr.uga.pddl4j.parser.RequireKey;
import fr.uga.pddl4j.parser.Symbol;
import fr.uga.pddl4j.parser.TypedSymbol;

import fr.uga.pddl4j.parser.Expression;
import fr.uga.pddl4j.plan.AbstractPlan;
import fr.uga.pddl4j.plan.Plan;
import fr.uga.pddl4j.plan.SequentialPlan;
import fr.uga.pddl4j.planners.AbstractPlanner;
import fr.uga.pddl4j.planners.Planner;
import fr.uga.pddl4j.planners.PlannerConfiguration;
import fr.uga.pddl4j.planners.ProblemNotSupportedException;
import fr.uga.pddl4j.planners.SearchStrategy;
import fr.uga.pddl4j.planners.statespace.search.StateSpaceSearch;
import fr.uga.pddl4j.problem.DefaultProblem;
import fr.uga.pddl4j.problem.Problem;
import fr.uga.pddl4j.problem.State;
import fr.uga.pddl4j.problem.operator.Action;
import fr.uga.pddl4j.problem.operator.ConditionalEffect;
import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import picocli.CommandLine;

import fr.uga.pddl4j.parser.Message;
import fr.uga.pddl4j.parser.NamedTypedList;
import fr.uga.pddl4j.parser.ParsedAction;
import fr.uga.pddl4j.parser.ParsedDerivedPredicate;
import fr.uga.pddl4j.parser.ParsedMethod;

import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;
import java.io.PrintWriter;
import java.util.Comparator;
import java.util.HashSet;
import java.util.List;
import java.util.PriorityQueue;
import java.util.Set;
import java.util.regex.Pattern;
import java.util.ArrayList;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.LinkedList;
import java.util.Map;
import java.util.Objects;
import java.util.regex.Matcher;
// import java.util.concurrent.TimeoutException;

import java.util.regex.Pattern;

import org.sat4j.core.VecInt;
import org.sat4j.reader.DimacsReader;
import org.sat4j.reader.ParseFormatException;
import org.sat4j.specs.ContradictionException;
import org.sat4j.specs.IConstr;
import org.sat4j.specs.IProblem;
import org.sat4j.specs.ISolver;
import org.sat4j.minisat.SolverFactory;
import org.sat4j.specs.IVecInt;
import org.sat4j.specs.TimeoutException;
import org.sat4j.tools.ModelIterator;

/*
 * The class is an example. It shows how to create a simple A* search planner able to
 * solve an ADL problem by choosing the heuristic to used and its weight.
 *
 * @author D. Pellier
 * @version 4.0 - 30.11.2021
 */
@CommandLine.Command(name = "ASP", version = "ASP 1.0", description = "Solves a specified planning problem using A* search strategy.", sortOptions = false, mixinStandardHelpOptions = true, headerHeading = "Usage:%n", synopsisHeading = "%n", descriptionHeading = "%nDescription:%n%n", parameterListHeading = "%nParameters:%n", optionListHeading = "%nOptions:%n")
public class ASP extends AbstractPlanner {

    /**
     * The weight of the heuristic.
     */
    private double heuristicWeight;

    /**
     * The name of the heuristic used by the planner.
     */
    private StateHeuristic.Name heuristic;

    /**
     * Sets the weight of the heuristic.
     *
     * @param weight the weight of the heuristic. The weight must be greater than 0.
     * @throws IllegalArgumentException if the weight is strictly less than 0.
     */
    @CommandLine.Option(names = { "-w",
            "--weight" }, defaultValue = "1.0", paramLabel = "<weight>", description = "Set the weight of the heuristic (preset 1.0).")
    public void setHeuristicWeight(final double weight) {
        if (weight <= 0) {
            throw new IllegalArgumentException("Weight <= 0");
        }
        this.heuristicWeight = weight;
    }

    /**
     * Set the name of heuristic used by the planner to the solve a planning
     * problem.
     *
     * @param heuristic the name of the heuristic.
     */
    @CommandLine.Option(names = { "-e",
            "--heuristic" }, defaultValue = "FAST_FORWARD", description = "Set the heuristic : AJUSTED_SUM, AJUSTED_SUM2, AJUSTED_SUM2M, COMBO, "
                    + "MAX, FAST_FORWARD SET_LEVEL, SUM, SUM_MUTEX (preset: FAST_FORWARD)")
    public void setHeuristic(StateHeuristic.Name heuristic) {
        this.heuristic = heuristic;
    }

    /**
     * Returns the name of the heuristic used by the planner to solve a planning
     * problem.
     *
     * @return the name of the heuristic used by the planner to solve a planning
     *         problem.
     */
    public final StateHeuristic.Name getHeuristic() {
        return this.heuristic;
    }

    /**
     * Returns the weight of the heuristic.
     *
     * @return the weight of the heuristic.
     */
    public final double getHeuristicWeight() {
        return this.heuristicWeight;
    }

    /**
     * The class logger.
     */
    private static final Logger LOGGER = LogManager.getLogger(ASP.class.getName());

    /**
     * Instantiates the planning problem from a parsed problem.
     *
     * @param problem the problem to instantiate.
     * @return the instantiated planning problem or null if the problem cannot be
     *         instantiated.
     */
    @Override
    public Problem instantiate(DefaultParsedProblem problem) {
        final Problem pb = new DefaultProblem(problem);
        pb.instantiate();
        return pb;
    }

    /**
     * Retrieving objects and initial state (predicates) from the parsed problem
     *
     * @param propositionVariables List of the propositions
     * @param parsedProblem        PDDL problem
     * @param Step                 Step of the plan
     * @return
     */
    public int addPropositionVariable(List<String> propositionVariables, DefaultParsedProblem parsedProblem, int Step) {
        final List<TypedSymbol<String>> objects = parsedProblem.getObjects();
        final List<NamedTypedList> InitialState = parsedProblem.getPredicates();
        int nbNewVariables = 0;
        for (NamedTypedList proposition : InitialState) {
            List<TypedSymbol<String>> arguments = proposition.getArguments();
            final int size = arguments.size();
            if (size == 1) {
                for (TypedSymbol<String> object : objects) {
                    // System.out.println(argument.getTypes());
                    // System.out.println(objet.getTypes());
                    if (parsedProblem.isSubType(object, arguments.get(0))) {
                        propositionVariables
                                .add(Step + " " + "(" + proposition.getName() + " " + object.getValue() + ")"); // variable
                                                                                                                // représentée
                                                                                                                // sous
                                                                                                                // la
                                                                                                                // forme:
                                                                                                                // 1 (at
                                                                                                                // robot
                                                                                                                // room)
                        nbNewVariables++;
                        // System.out.print("\n( "+proposition.getName()+" "+object.getValue() + "
                        // )\n");
                    }
                }
            }
            if (size == 2) {
                for (TypedSymbol<String> object : objects) {
                    for (TypedSymbol<String> object2 : objects) {
                        // System.out.println(argument.getTypes());
                        // System.out.println(objet.getTypes());
                        if (parsedProblem.isSubType(object, arguments.get(0))) {
                            if (parsedProblem.isSubType(object2, arguments.get(1))) {
                                propositionVariables.add(Step + " " + "(" + proposition.getName() + " "
                                        + object.getValue() + " " + object2.getValue() + ")");
                                nbNewVariables++;
                                // System.out.print("\n("+proposition.getName()+" "+object.getValue()+ "
                                // "+object2.getValue() + ")\n");
                            }
                        }
                    }
                }
            }
            if (size == 3) {
                for (TypedSymbol<String> object : objects) {
                    for (TypedSymbol<String> object2 : objects) {
                        for (TypedSymbol<String> object3 : objects) {

                            // System.out.println(argument.getTypes());
                            // System.out.println(objet.getTypes());
                            if (parsedProblem.isSubType(object, arguments.get(0))) {
                                if (parsedProblem.isSubType(object2, arguments.get(1))) {
                                    if (parsedProblem.isSubType(object3, arguments.get(2))) {
                                        propositionVariables
                                                .add(Step + " " + "(" + proposition.getName() + " " + object.getValue()
                                                        + " " + object2.getValue() + " " + object3.getValue() + ")");
                                        nbNewVariables++;
                                    }
                                    // System.out.print("\n("+proposition.getName()+" "+object.getValue()+ "
                                    // "+object2.getValue() + ")\n");
                                }
                            }
                        }
                    }
                }
            }
        }
        return nbNewVariables;
    }

    /**
     * This function iteratively generates action variables
     *
     * @param colonne              Enable recurcive function
     * @param parameters           Parameters needed by the action
     * @param objects              List of all objects used in the problem (ex:
     *                             room1 room2 robot)
     * @param actionStr            Action in form of a string
     * @param parsedProblem        PDDL problem
     * @param action               Parsed action of the problem
     * @param Step                 Step of the plan
     * @param actionArray          List of actions
     * @param propositionVariables List of the propositions
     */
    public void addActionVariables(int colonne, List<TypedSymbol<String>> parameters, List<TypedSymbol<String>> objects,
            String actionStr, DefaultParsedProblem parsedProblem, ParsedAction action, int Step,
            List<List<List<String>>> actionArray, List<String> propositionVariables) {
        if (colonne > parameters.size()) {
            String[] actionSplit = actionStr.split(" "); // split l'action -> en 0 le nom, en 1 la parenthèse et ensuite
                                                         // l'ensemble des paramètres
            String preconditionStr = action.getPreconditions().toString(); // récupére les préconditions
            String effectStr = action.getEffects().toString(); // récupére les effets

            /*
             * Bout de code pour enlever toutes les préconditions pouvant contenir plusieurs
             * fois la même valeur (ex: MOVE Room1 Room1 -> aucun intérêt)
             */
            HashSet<String> multipleVariables = new HashSet<>();
            for (String value : actionSplit) {
                if (!multipleVariables.add(value)) {
                    return;
                }
            }
            /* Remplace les variables X0, X1... par les valeurs des paramètres en entrées */
            for (int kParameters = 0; kParameters < parameters.size(); kParameters++) {
                preconditionStr = preconditionStr.replaceAll("\\?X" + kParameters, actionSplit[2 + kParameters]);// remplace
                                                                                                                 // les
                                                                                                                 // ?X0...
                                                                                                                 // par
                                                                                                                 // les
                                                                                                                 // paramètres
                                                                                                                 // locaux
                effectStr = effectStr.replaceAll("\\?X" + kParameters, actionSplit[2 + kParameters]); // idem
            }

            String pattern = "\\((?!not\\s?\\().*?\\)(?!\\))"; // Regex pour extraire les variables propositionnnelles
            Pattern regex = Pattern.compile(pattern);

            Matcher effectMatcher = regex.matcher(effectStr);
            Matcher preconditionMatcher = regex.matcher(preconditionStr);

            String patternNeg = "\\(not\\s?\\(.*?\\)\\)"; // pattern pour extraires les effets négatifs négatives
            Pattern regexNeg = Pattern.compile(patternNeg);

            Matcher effectMatcherNeg = regexNeg.matcher(effectStr);

            List<String> effectListNeg = new ArrayList<>();
            List<String> effectList = new ArrayList<>();
            List<String> preconditionList = new ArrayList<>();

            List<List<String>> individualAction = new ArrayList<>();
            List<String> nameAction = new ArrayList<>();
            nameAction.add(Step + " " + actionStr + ")");
            individualAction.add(nameAction);

            // System.out.println(actionStr);
            while (effectMatcher.find()) {
                String match = effectMatcher.group();
                String matchStr;
                try {
                    matchStr = match.toString().replaceAll("\\(and\\s", ""); // on enlève les (and (
                } catch (Exception e) {
                    matchStr = match;
                }
                int effectIndex = propositionVariables.indexOf((Step + 1) + " " + matchStr); // on cherche l'effet dans
                                                                                             // la liste des variables
                                                                                             // propositionnelles
                if (effectIndex == -1) {
                    continue;
                } else {
                    effectList.add("" + effectIndex);
                }

                // System.out.println("not ( "+Step+" "+actionStr+") ) OR "+(Step+1)+" "+match);
            }
            while (effectMatcherNeg.find()) {
                String match = effectMatcherNeg.group();
                String matchStr;
                // System.out.println("Before"+match);
                matchStr = match.toString().replaceAll("\\(not\\s", "").replace("))", ")"); // on enlève le (not XXXXX)
                                                                                            // de l'effet négatif
                // System.out.println("After"+matchStr);
                try {
                    matchStr = matchStr.toString().replaceAll("\\(and\\s", ""); // on enlève les (and (
                } catch (Exception e) {
                }
                int effectIndex = propositionVariables.indexOf((Step + 1) + " " + matchStr); // on cherche l'effet dans
                                                                                             // la liste des variables
                                                                                             // propositionnelles
                effectListNeg.add("" + effectIndex); // effet à l'état i+1
            }
            while (preconditionMatcher.find()) {
                String match = preconditionMatcher.group();
                int propositionIndex = propositionVariables.indexOf(Step + " " + match.toString());
                preconditionList.add("" + propositionIndex);
            }
            individualAction.add(preconditionList);
            individualAction.add(effectList);
            individualAction.add(effectListNeg);
            // System.out.println(individualAction);
            actionArray.add(individualAction);

            // action="";
        } else {
            for (int ligne = 0; ligne < objects.size(); ligne++) {
                // System.out.print("LIGNE " + ligne + " COLONNE " + colonne + " Object = " + objects.get(ligne).getValue()
                //         + " parameters type and object " + parameters.get(colonne - 1).getTypes()
                //         + objects.get(ligne).getTypes() + "\n");
                if (parsedProblem.isSubType(objects.get(ligne), parameters.get(colonne - 1))) {
                    addActionVariables(colonne + 1, parameters, objects,
                            actionStr + "" + objects.get(ligne).getValue() + " ", parsedProblem, action, Step,
                            actionArray, propositionVariables);
                } else {
                    continue;
                } // System.out.print(action+"\n");
            }
        }
    }

    /**
     * This function adds clauses for the initial state to the solver
     *
     * @param nbVariables          number of proposition added for one step
     * @param initialState         Initail state of the pddl problem
     * @param propositionVariables List of the propositions
     * @param solver               SAT Solver
     * @return
     */
    public boolean addInitialStateClause(int nbVariables, List<Expression<String>> initialState,
            List<String> propositionVariables, ISolver solver) {
        for (int k = 1; k <= nbVariables; k++) { // on démarre à 1 car il ne faut pas de 0 dans les clauses
            String proposition = propositionVariables.get(k);

            initloop: {
                for (Expression<String> expression : initialState) {
                    // System.out.println(expression+ " prop"+proposition.substring(1)+ "
                    // "+expression.toString().equals(proposition.substring(2)));
                    if (expression.toString().equals(proposition.substring(2))) {
                        try {
                            int[] clause = { k };

                            // System.out.println("clause "+expression+" "+clause[0]);
                            solver.addClause(new VecInt(clause));
                            // System.out.println("Initial: "+propositionVariables.get(clause[0])+" 0");
                            // System.out.println(clause[0]+" 0");
                        } catch (ContradictionException e) {
                            System.out.println("Error Initial clauses" + " " + e.getMessage());
                            return false;
                        }
                        break initloop;
                    }
                }
                try {
                    int[] clause = { -k };
                    solver.addClause(new VecInt(clause));
                    // System.out.println("Initial: -"+ propositionVariables.get(-clause[0])+" 0");
                    // System.out.println(clause[0]+" 0");
                } catch (ContradictionException e) {
                    System.out.println("Contradiction Error Initial clauses " + e.getMessage());
                    return false;
                }

            }
        }
        return true;
    }
    // System.out.println("CHECK" +solver.nConstraints());

    /**
     * Adds goal state clauses to the solver
     *
     * @param nbVariables          Number of variables during one step
     * @param tpsSimu              Simulation step
     * @param goalState            Goal state from the PDDL problem
     * @param propositionVariables List of the propositions
     * @param solver               SAT Solver
     * @return
     */
    public boolean addGoalStateClause(int nbVariables, int tpsSimu, Expression<String> goalState,
            List<String> propositionVariables, ISolver solver) {

        for (int k = (tpsSimu) * nbVariables + 1; k <= (tpsSimu + 1) * nbVariables; k++) {
            String proposition = propositionVariables.get(k);
            // System.out.println(goalState.toString().indexOf(proposition.substring(2)));
            if (goalState.toString().indexOf(proposition.substring(2)) >= 0) {
                int[] clause = { k };
                try {
                    // System.out.println("\n GOAL proposition "+proposition+ " "+clause[0]);
                    solver.addClause(new VecInt(clause));
                    // System.out.println("Goal: " + propositionVariables.get(clause[0]));
                    // System.out.println(clause[0] + " 0");
                } catch (ContradictionException e) {
                    System.out.println("Erreur Goal " + clause[0] + " " + e.getMessage());
                    return false;
                    // System.out.println("Error Goal clauses"+e.getMessage());
                }
            }

            else {
                int[] clause = { -k };
                try {
                    // System.out.println("\n GOAL proposition not "+proposition+ " "+clause[0]);
                    solver.addClause(new VecInt(clause));
                    // System.out.println(clause[0]+" 0");
                    // System.out.println("Goal: -"+propositionVariables.get(-clause[0]));
                } catch (ContradictionException e) {
                    System.out.println("Erreur Goal " + clause[0] + " " + e.getMessage());
                    return false;
                    // System.out.println("Error Goal clauses"+e.getMessage());
                }
            }

        }
        return true;
    }

    /**
     * This function adds action clauses to the solver
     *
     * @param actionArray          List of actions
     * @param propositionVariables List of the proposition
     * @param solver               SAT Solver
     * @return
     */
    public boolean addActionClause(List<List<List<String>>> actionArray, List<String> propositionVariables,
            ISolver solver) {

        for (List<List<String>> action : actionArray) {
            int indexAction = (-1 * (propositionVariables.size() + 1 + actionArray.indexOf(action)));
            for (String precondition : action.get(1)) {
                // System.out.println(precondition);
                int[] clause = { indexAction, Integer.parseInt(precondition) };
                try {
                    // System.out.println("\n precondition "+action+ "
                    // "+propositionVariables.get(clause[1]));//+ " "+clause[0]+ " "+clause[1]);
                    solver.addBlockingClause(new VecInt(clause));
                    // System.out.println(clause[0]+" "+clause[1]+" 0");
                    // System.out.println("ACTION CLAUSE: not
                    // "+actionArray.get(-clause[0]-(propositionVariables.size()+1))+ "
                    // "+propositionVariables.get(clause[1]));
                } catch (ContradictionException e) {
                    System.out.println("Contradiction Error precondition clauses");
                    return false;
                }
            }
            for (String effectPos : action.get(2)) {
                int[] clause = { indexAction, Integer.parseInt(effectPos) };
                try {
                    // System.out.println("\n effect "+action+ "
                    // "+propositionVariables.get(clause[1]));//+ " "+clause[0]+ " "+clause[1]);
                    solver.addBlockingClause(new VecInt(clause));
                    // System.out.println(clause[0]+" "+clause[1]+" 0");
                    // System.out.println("Action Effect Pos:
                    // "+actionArray.get(-clause[0]-(propositionVariables.size()+1))+"
                    // "+propositionVariables.get(clause[1])+ " 0");
                } catch (ContradictionException e) {
                    System.out.println("Contradiction Error effect clauses");
                    return false;
                }
            }
            for (String effectNeg : action.get(3)) {
                int[] clause = { indexAction, -1 * Integer.parseInt(effectNeg) };
                try {
                    // System.out.println("\n effect "+action+ "
                    // "+propositionVariables.get(clause[1]));//+ " "+clause[0]+ " "+clause[1]);
                    solver.addBlockingClause(new VecInt(clause));
                    // System.out.println(clause[0]+" "+clause[1]+ " 0");
                    // System.out.println("Action Effect Neg:
                    // "+actionArray.get(-clause[0]-(propositionVariables.size()+1))+"
                    // -"+propositionVariables.get(-clause[1])+ " 0");
                } catch (ContradictionException e) {
                    System.out.println("Contradiction Error effect clauses");
                    return false;
                }
            }
        }
        return true;
    }

    /**
     * This function adds state transitions clauses to the solver
     *
     * @param actionArray          List of actions
     * @param propositionVariables List of the proposition
     * @param solver               SAT Solver
     * @return
     */
    public boolean addStateTransitionsClause(List<List<List<String>>> actionArray, List<String> propositionVariables,
            ISolver solver) {
        for (String propositionVariable : propositionVariables) {
            // System.out.println("propositionVariable: "+ propositionVariable);
            List<Integer> actionPos = new ArrayList<Integer>();
            List<Integer> actionNeg = new ArrayList<Integer>();
            if (propositionVariable.charAt(0) == '0' || propositionVariable.charAt(0) == 'c') { // On cherche les états
                                                                                                // i+1
                // System.out.println(propositionVariable+" Proposition 0");
                continue;
            } else {

                Matcher matcher = Pattern.compile("\\d+").matcher(propositionVariable); // récupére le temps de la
                                                                                        // propositiion
                matcher.find();
                int tps = Integer.valueOf(matcher.group());
                String result = propositionVariable.replaceFirst("\\d+\\s", (tps - 1) + " ");

                int indexEtatI1 = propositionVariables.indexOf(propositionVariable); // index de l'état i+1
                int indexEtatI = propositionVariables.indexOf(result); // index de l'état i

                // System.out.println("SUBSTRING "+propositionVariable+"
                // "+indexEtatI1+"\n"+result+ " "+indexEtatI); // Affiche "(tps-1)
                // (quelquechose)"
                for (List<List<String>> action : actionArray) { // on parcoure toutes les actions (ne contient que les
                                                                // actions de l'état i)
                    for (String effectPos : action.get(2)) {
                        if (effectPos.equals("" + indexEtatI1)) {
                            // System.out.println("POSSSSSSSSSSSSSSSSSSSSSS " +effect+" "+indexEtatI1);
                            int index = propositionVariables.size() + 1 + actionArray.indexOf(action);
                            actionPos.add(index);
                            // System.out.println("Add POS action "+index);
                            // System.out.println(indexEtatI+" "+(-1*indexEtatI1)+"
                            // "+(propositionVariables.size()+actionArray.indexOf(action))); //clause états
                            // positifs
                        }
                    }
                    for (String effectNeg : action.get(3)) {
                        if (effectNeg.equals("" + indexEtatI1)) {
                            // System.out.println("NEGGGGGGGGGGGGG " +effect+" -"+indexEtatI1);
                            // int [] clause={-indexEtatI, indexEtatI1,
                            // propositionVariables.size()+actionArray.indexOf(action)};//clause états
                            // négatifs
                            int index = propositionVariables.size() + 1 + actionArray.indexOf(action);
                            actionNeg.add(index);
                            // System.out.println((-1*indexEtatI)+" "+indexEtatI1+"
                            // "+(propositionVariables.size()+actionArray.indexOf(action))); //clause états
                            // négatifs
                        }
                    }
                }

                int[] clausePos = new int[2 + actionPos.size()];
                clausePos[0] = indexEtatI;
                clausePos[1] = -indexEtatI1;
                for (int i = 0; i < actionPos.size(); i++) {
                    clausePos[i + 2] = actionPos.get(i);
                }

                int[] clauseNeg = new int[2 + actionNeg.size()];
                clauseNeg[0] = -indexEtatI;
                clauseNeg[1] = indexEtatI1;
                for (int i = 0; i < actionNeg.size(); i++) {
                    clauseNeg[i + 2] = actionNeg.get(i);
                }

                try {
                    // System.out.println("\n effect "+propositionVariables.get(clause[0])+" AND
                    // -"+propositionVariables.get(-clause[1])+" -> "+action);//+ " "+clause[0]+ "
                    // "+clause[1]);
                    // solver.addClause(new VecInt(clausePos));
                    solver.addBlockingClause(new VecInt(clauseNeg));
                    // for (int clause : clauseNeg){
                    // System.out.print(" "+clause);
                    // }
                    // System.out.println(" 0");
                    // System.out.println("TransitionState:
                    // -"+propositionVariables.get(-clauseNeg[0])+"
                    // "+propositionVariables.get(clauseNeg[1])+"
                    // "+actionArray.get(clauseNeg[2]-(propositionVariables.size()+1))+ " 0");
                } catch (ContradictionException e) {

                    // System.out.println("Error Transition i+1 clauses POS ");
                    // for (int clause:clausePos){
                    // if (clause>propositionVariables.size()){
                    // System.out.println("ACTION:
                    // "+actionArray.get(clause-propositionVariables.size()));
                    // }
                    // else{
                    // // System.out.print("CLAUSE NEG"+propositionVariables.get(clause));
                    // }
                    // }
                    // System.out.println();
                    // System.out.println("Error Transition i+1 clauses NEG ");
                    for (int clause : clauseNeg) {
                        if (clause > propositionVariables.size()) {
                            System.out.println("ContradictionException ACTION: "
                                    + actionArray.get(clause - (propositionVariables.size() + 1)));
                        } else {
                            // System.out.print("CLAUSE and not action"+propositionVariables.get(clause));
                        }
                    }
                    System.out.println();
                    return false;
                }
                try {
                    // System.out.println("\n effect "+propositionVariables.get(clause[0])+" AND
                    // -"+propositionVariables.get(-clause[1])+" -> "+action);//+ " "+clause[0]+ "
                    // "+clause[1]);
                    solver.addBlockingClause(new VecInt(clausePos));
                    // for (int clause : clausePos){
                    // System.out.print(" "+clause);
                    // }
                    // System.out.println(" 0");
                    // solver.addClause(new VecInt(clauseNeg));
                    // System.out.print("TransitionState: "+propositionVariables.get(clausePos[0])+"
                    // -"+propositionVariables.get(-clausePos[1])+" ");//

                } catch (ContradictionException e) {

                    System.out.println("Error Transition i+1 clauses POS ");
                    for (int clause : clausePos) {
                        if (clause > propositionVariables.size()) {
                            System.out.println("ContradictionException ACTION: "
                                    + actionArray.get(clause - (propositionVariables.size() + 1)));
                        } else {
                            // System.out.print("CLAUSE NEG"+propositionVariables.get(clause));
                        }
                    }
                    return false;
                    // System.out.println();
                    // System.out.println("Error Transition i+1 clauses NEG ");
                    // for (int clause:clauseNeg){
                    // if (clause>propositionVariables.size()){
                    // System.out.println("ACTION:
                    // "+actionArray.get(clause-propositionVariables.size()));
                    // }
                    // else{
                    // // System.out.print("CLAUSE "+propositionVariables.get(clause));
                    // }
                    // }
                    // System.out.println();
                }
            }
        }
        return true;
    }

    /**
     * This function adds disjunction clauses to the solver
     *
     * @param actionArray          List of actions List of action
     * @param propositionVariables List of the propositions
     * @param solver               SAT Solver
     * @return
     */
    public boolean addActionDisjunctionClause(List<List<List<String>>> actionArray, List<String> propositionVariables,
            ISolver solver) {
        for (int kAction = 0; kAction < actionArray.size() - 1; kAction++) {
            for (int iAction = kAction + 1; iAction < actionArray.size(); iAction++) {
                Matcher matcherK = Pattern.compile("\\d+").matcher(actionArray.get(kAction).get(0).get(0).toString()); // récupére
                                                                                                                       // le
                                                                                                                       // temps
                                                                                                                       // de
                                                                                                                       // la
                                                                                                                       // propositiion
                matcherK.find();
                int k = Integer.valueOf(matcherK.group());
                Matcher matcherI = Pattern.compile("\\d+").matcher(actionArray.get(iAction).get(0).get(0).toString()); // récupére
                                                                                                                       // le
                                                                                                                       // temps
                                                                                                                       // de
                                                                                                                       // la
                                                                                                                       // propositiion
                matcherI.find();
                int i = Integer.valueOf(matcherI.group());

                if (k == i) {
                    int[] clause = { -(propositionVariables.size() + 1 + kAction),
                            -(propositionVariables.size() + 1 + iAction) };// clause états négatifs
                    try {
                        // System.out.println(actionArray.get(kAction)+" OR "+actionArray.get(iAction));
                        solver.addBlockingClause(new VecInt(clause));
                        // System.out.println("Clause Disjunction
                        // "+actionArray.get(-clause[0]-propositionVariables.size())+"
                        // "+actionArray.get(-clause[1]-propositionVariables.size()));
                        // System.out.println("Disjonction :
                        // -"+actionArray.get(-clause[0]-propositionVariables.size()-1)+"
                        // -"+actionArray.get(-clause[1]-propositionVariables.size()-1)+" 0");
                        // System.out.println(clause[0]+ " " +clause[1]+" 0");

                    } catch (ContradictionException e) {
                        System.out.println("Error ActionDisjunction clauses" + clause[0] + " " + clause[1] + "    "
                                + actionArray.get(-clause[0] - (propositionVariables.size() + 1)) + " "
                                + actionArray.get(-clause[1] - (propositionVariables.size() + 1)) + e.getMessage());
                        return false;
                    }
                    // System.out.println("NOT("+actionArray.get(kAction).get(0).get(0)+") OR
                    // NOT("+actionArray.get(iAction).get(0).get(0)+") ");
                }
            }
        } // on parcoure toutes les actions (ne contient que les actions de l)
        return true;
    }

    // public int parcourirPreconditions(parametres, index, combinaison_actuelle)
    /**
     * Search a solution plan to a specified domain and problem using A*.
     *
     * @param problem the problem to solve.
     * @return the plan found or null if no plan was found.
     */
    @Override
    public Plan solve(final Problem problem) {

        // Array of all the literal
        List<String> propositionVariables = new ArrayList<>();
        propositionVariables.add("c Unused case 0");

        // Get the problem
        final DefaultParsedProblem parsedProblem = problem.getParsedProblem();

        // System.out.print("\nInit initiales: ");
        int nbVariables = 0;

        boolean isSatisfiable = false;
        // nbVariables=addPropositionVariable(propositionVariables, parsedProblem, 0);
        int tpsSimu = 0;

        nbVariables = addPropositionVariable(propositionVariables, parsedProblem, tpsSimu);
        List<List<List<String>>> actionArray = new ArrayList<>();

        final List<Expression<String>> initialState = parsedProblem.getInit();
        final Expression<String> goalState = parsedProblem.getGoal(); // Ne fonctionne pas si il y a un OU
        final List<TypedSymbol<String>> objects = parsedProblem.getObjects();
        final List<ParsedAction> actions = parsedProblem.getActions();

        final int MAXVAR = 100000;
        final int NBCLAUSES = 50000;
        ISolver solver = SolverFactory.newDefault();
        solver.setTimeout(3600); // 1 hour timeout
        // prepare the solver to accept MAXVAR variables. MANDATORY for MAXSAT solving
        solver.newVar(MAXVAR);
        solver.setExpectedNumberOfClauses(NBCLAUSES);
        IProblem SatProblem = solver;
        SequentialPlan plan2 = new SequentialPlan();

        while (!isSatisfiable) {

            if (tpsSimu > 30) {
                break;
            }
            // System.out.println("unsat "+tpsSimu+" "+isSatisfiable);

            tpsSimu++;
            solver.reset();
            solver.clearLearntClauses();
            nbVariables = addPropositionVariable(propositionVariables, parsedProblem, tpsSimu); // ajoute les nouvelles
                                                                                                // variables pour
                                                                                                // l'instant tpsSimu

            for (ParsedAction action : actions) {
                final List<TypedSymbol<String>> parameters = action.getParameters();
                String actionStr = action.getName().toString() + " ( ";
                addActionVariables(1, parameters, objects, actionStr, parsedProblem, action, tpsSimu - 1, actionArray,
                        propositionVariables);
            }

            if (addActionDisjunctionClause(actionArray, propositionVariables, solver) &&
                    addStateTransitionsClause(actionArray, propositionVariables, solver) &&
                    addActionClause(actionArray, propositionVariables, solver) &&
                    addGoalStateClause(nbVariables, tpsSimu, goalState, propositionVariables, solver) &&
                    addInitialStateClause(nbVariables, initialState, propositionVariables, solver)) {
                SatProblem = solver;
            } else {
                System.out.println("Exception in add Clause:" + tpsSimu);
                continue;
            }

            // SatProblem = solver;
            try {

                isSatisfiable = SatProblem.isSatisfiable();
                if (isSatisfiable) {
                    int[] plan = SatProblem.model();
                    System.out.println("PLAN: ");
                    for (int kSol = 0; kSol < plan.length; kSol++) {
                        // System.out.println(plan[kSol]);
                        if (plan[kSol] > 0) {
                            // System.out.println("Test "+plan[kSol]+' '+propositionVariables.size());
                            if (plan[kSol] < propositionVariables.size()) {
                                // System.out.println("Variable vraie " + propositionVariables.get(plan[kSol]));
                                continue;
                            } else if (plan[kSol] >= propositionVariables.size()) {
                                // String action=actionArray.get((plan[kSol]-(propositionVariables.size()+1))).get(0).get(0);
                                // plan1.add(action.charAt(0),Action(action));
                                String actionStr = actionArray.get((plan[kSol] - (propositionVariables.size() + 1))).get(0).get(0);
                                // System.out.println("Action : " + actionArray.get((plan[kSol] - (propositionVariables.size() + 1))).get(0));
                                Action action = new Action(actionStr.replaceFirst("\\d+\\s", ""),
                                        Integer.parseInt(actionStr.replaceAll("(\\d+).+", "$1")));
                                plan2.add(Integer.parseInt(actionStr.replaceAll("(\\d+).+", "$1")), action);
                                // System.out.println("Action2 " + "      " + plan2.actions().get(0).getName());
                            }
                        } else {
                            if (-plan[kSol] < propositionVariables.size()) {
                                // System.out.println("Variable vraie
                                // NOT"+propositionVariables.get(-plan[kSol]));
                                continue;
                            } else if (-plan[kSol] >= propositionVariables.size()) {
                                // System.out.println("Action NOT:
                                // "+actionArray.get(-plan[kSol]-propositionVariables.size()).get(0));
                            }
                        }
                    }
                }
            } catch (TimeoutException e) {
                System.out.println("Unsat");
            }
        }

        System.out.println("SAT");

        // System.out.println(plan2);
        // StateSpaceSearch search = StateSpaceSearch.getInstance(SearchStrategy.Name.ASTAR,
        //         this.getHeuristic(), this.getHeuristicWeight(), this.getTimeout());
        // LOGGER.info("* Starting A* search \n");
        // // Search a solution
        // Plan plan1 = search.searchPlan(problem);
        // // If a plan is found update the statistics of the planner and log search
        // // information
        // if (plan1 != null) {
        //     LOGGER.info("* A* search succeeded\n");
        //     this.getStatistics().setTimeToSearch(search.getSearchingTime());
        //     this.getStatistics().setMemoryUsedToSearch(search.getMemoryUsed());
        // } else {
        //     LOGGER.info("* A* search failed\n");
        // }
        // Return the plan found or null if the search fails.
        return plan2;

    }

    @Override
    public boolean isSupported(Problem problem) {
        return true;
    }

    /**
     * The main method of the <code>ASP</code> planner.
     *
     * @param args the arguments of the command line.
     */
    public static void main(String[] args) {
        try {
            final ASP planner = new ASP();
            CommandLine cmd = new CommandLine(planner);
            cmd.execute(args);
        } catch (IllegalArgumentException e) {
            LOGGER.fatal(e.getMessage());
        }
    }

}