/*
 * Copyright 2015 United States Government, as represented by the Administrator
 *                of the National Aeronautics and Space Administration. All Rights Reserved.
 *           2017-2021 The jConstraints Authors
 * SPDX-License-Identifier: Apache-2.0
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package gov.nasa.jpf.constraints.solvers.encapsulation;

import static java.lang.System.exit;

import gov.nasa.jpf.constraints.api.ConstraintSolver;
import gov.nasa.jpf.constraints.api.ConstraintSolver.Result;
import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.SolverContext;
import gov.nasa.jpf.constraints.api.UNSATCoreSolver;
import gov.nasa.jpf.constraints.api.Valuation;
import gov.nasa.jpf.constraints.solvers.ConstraintSolverFactory;
import gov.nasa.jpf.constraints.solvers.encapsulation.messages.EnableUnsatCoreTrackingMessage;
import gov.nasa.jpf.constraints.solvers.encapsulation.messages.GetUnsatCoreMessage;
import gov.nasa.jpf.constraints.solvers.encapsulation.messages.Message;
import gov.nasa.jpf.constraints.solvers.encapsulation.messages.SolvingResultMessage;
import gov.nasa.jpf.constraints.solvers.encapsulation.messages.StartSolvingMessage;
import gov.nasa.jpf.constraints.solvers.encapsulation.messages.StopSolvingMessage;
import gov.nasa.jpf.constraints.solvers.encapsulation.messages.TimeOutSolvingMessage;
import gov.nasa.jpf.constraints.solvers.encapsulation.messages.UnsatCoreMessage;
import java.io.BufferedInputStream;
import java.io.IOException;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;
import java.util.List;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.FutureTask;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.TimeoutException;
import java.util.logging.Level;
import java.util.logging.Logger;
import org.apache.commons.cli.CommandLine;
import org.apache.commons.cli.CommandLineParser;
import org.apache.commons.cli.DefaultParser;
import org.apache.commons.cli.Options;
import org.apache.commons.cli.ParseException;

public class SolverRunner {

  public static ExecutorService exec = Executors.newSingleThreadExecutor();
  private static boolean isUnsatCoreChecking = false;

  private static int TIME_OUT_IN_SECONDS = 60;

  public static void main(String[] args) throws IOException {
    silenceTheLogger();
    CommandLineParser parser = new DefaultParser();
    try {
      CommandLine cmd = parser.parse(getOptions(), args);
      if (cmd.hasOption("timeout")) {
        TIME_OUT_IN_SECONDS = Integer.parseInt(cmd.getOptionValue("timeout"));
      }
      solve(cmd.getOptionValue("s"));
      exit(0);
    } catch (IOException
        | ClassNotFoundException
        | ParseException
        | InterruptedException
        | ExecutionException e) {
      ObjectOutputStream err = new ObjectOutputStream(System.err);
      // err.writeObject(e);
      exit(2);
    }
  }

  private static Options getOptions() {
    Options options = new Options();
    options.addRequiredOption("s", "solver", true, "SolverName of encapsulated solver");
    options.addOption("t", "timeout", true, "timeout");
    return options;
  }

  private static void solve(String solverName)
      throws IOException, ClassNotFoundException, InterruptedException, ExecutionException {
    try (BufferedInputStream bin = new BufferedInputStream(System.in);
        ObjectInputStream inStream = new ObjectInputStream(bin);
        ObjectOutputStream out = new ObjectOutputStream(System.out)) {
      SolverContext solver = initCtx(solverName);

      while (true) {
        if (bin.available() > 0) {
          Object read = inStream.readObject();
          if (read instanceof List) {
            List<Expression> expr = (List<Expression>) read;

            out.writeObject(new StartSolvingMessage());
            Valuation val = new Valuation();
            try {
              Result res = solveWithTimeOut(solver, expr, val);
              out.writeObject(new StopSolvingMessage());
              out.writeObject(new SolvingResultMessage(res, val));
              out.flush();
            } catch (TimeoutException e) {
              out.writeObject(new TimeOutSolvingMessage());
              exec.shutdownNow();
              break;
            }
          } else if (read instanceof Message) {
            if (read instanceof StopSolvingMessage) {
              StopSolvingMessage ssm = (StopSolvingMessage) read;
              break;
            } else if (read instanceof EnableUnsatCoreTrackingMessage) {
              isUnsatCoreChecking = true;
              solver = initCtx(solverName);
            } else if (read instanceof GetUnsatCoreMessage && solver instanceof UNSATCoreSolver) {
              UNSATCoreSolver unsatCoreSolver = (UNSATCoreSolver) solver;
              List<Expression<Boolean>> core = unsatCoreSolver.getUnsatCore();
              out.writeObject(new UnsatCoreMessage(core));
            }
          } else {
            throw new UnsupportedOperationException(
                "Cannot interpret this: " + read.getClass().getName());
          }
        } else {
          // Thread.sleep(1);
        }
      }
    }
  }

  private static Result solveWithTimeOut(SolverContext solver, List<Expression> expr, Valuation val)
      throws TimeoutException, ExecutionException, InterruptedException {
    solver.pop();
    solver.push();
    for (Expression e : expr) {
      solver.add(e);
    }
    FutureTask<Result> solverRun = new FutureTask<>(() -> solver.solve(val));
    exec.submit(solverRun);
    try {
      return solverRun.get(TIME_OUT_IN_SECONDS, TimeUnit.SECONDS);
    } catch (TimeoutException e) {
      solverRun.cancel(true);
      exec.shutdown();
      return Result.TIMEOUT;
    }
  }

  private static void silenceTheLogger() {
    Logger logger = Logger.getLogger("constraints");
    logger.getParent().setLevel(Level.OFF);
  }

  private static SolverContext initCtx(String solverName) {
    ConstraintSolver solver = ConstraintSolverFactory.createSolver(solverName);
    if (isUnsatCoreChecking && solver instanceof UNSATCoreSolver) {
      UNSATCoreSolver unsatSolver = (UNSATCoreSolver) solver;
      unsatSolver.enableUnsatTracking();
    }
    SolverContext ctx = solver.createContext();
    ctx.push();
    return ctx;
  }
}
