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

import gov.nasa.jpf.constraints.api.ConstraintSolver;
import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.SolverContext;
import gov.nasa.jpf.constraints.api.UNSATCoreSolver;
import gov.nasa.jpf.constraints.api.Valuation;
import gov.nasa.jpf.constraints.api.ValuationEntry;
import gov.nasa.jpf.constraints.solvers.encapsulation.messages.EnableUnsatCoreTrackingMessage;
import gov.nasa.jpf.constraints.solvers.encapsulation.messages.GetUnsatCoreMessage;
import gov.nasa.jpf.constraints.solvers.encapsulation.messages.SolvingResultMessage;
import gov.nasa.jpf.constraints.solvers.encapsulation.messages.StartSolvingMessage;
import gov.nasa.jpf.constraints.solvers.encapsulation.messages.StopSolvingMessage;
import gov.nasa.jpf.constraints.solvers.encapsulation.messages.TimeOutSolvingMessage;
import gov.nasa.jpf.constraints.solvers.encapsulation.messages.UnsatCoreMessage;
import gov.nasa.jpf.constraints.util.ExpressionUtil;
import java.io.BufferedInputStream;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;
import java.io.OutputStream;
import java.io.StreamCorruptedException;
import java.lang.management.ManagementFactory;
import java.util.LinkedList;
import java.util.List;

public class ProcessWrapperSolver extends ConstraintSolver implements UNSATCoreSolver {

  private final String solverName;
  String javaClassPath;
  private String jConstraintsExtensionsPath;
  private static int TIMEOUT = 60;
  private boolean isUnsatTracking = false;
  private String javaBinary;

  private Process solver;
  private ObjectOutputStream inObject;
  private BufferedInputStream bes;
  private BufferedInputStream bos;
  private ObjectInputStream outObject;

  private int RETRIES = 3;

  public ProcessWrapperSolver(String solver) {
    super.name = solver + "prozess";
    this.solverName = solver;
    inObject = null;
    bes = null;
    bos = null;
    outObject = null;

    List<String> env = ManagementFactory.getRuntimeMXBean().getInputArguments();
    jConstraintsExtensionsPath = "";
    for (String s : env) {
      if (s.startsWith("-Djconstraints.wrapper.timeout")) {
        TIMEOUT = Integer.parseInt(s.split("=")[1]);
      }
    }

    javaClassPath = System.getProperty("java.class.path");
    javaBinary = "java";
  }

  public ProcessWrapperSolver(String solver, String javaBinary) {
    this(solver);
    if (!javaBinary.equals("")) {
      this.javaBinary = javaBinary;
    }
  }

  Result solve(List<Expression<Boolean>> f, Valuation result, int counter) {

    try {
      return runSolverProcess(f, result);
    } catch (IOException | ClassNotFoundException e) {
      logCallToSolver(f);
      e.printStackTrace();
      ++counter;
      if (counter < RETRIES) {
        if (solver != null && solver.isAlive()) {
          solver.destroy();
        }
        solver = null;
        bes = null;
        bos = null;
        inObject = null;
        solve(f, result, counter);
      }
      return Result.DONT_KNOW;
    } catch (InterruptedException e) {
      solver = null;
      outObject = null;
      System.out.println("Restart required");
      return solve(f, result, 0);
    }
  }

  @Override
  public Result solve(Expression<Boolean> f, Valuation result) {
    List<Expression<Boolean>> tmp = new LinkedList<>();
    tmp.add(f);
    return solve(tmp, result, 0);
  }

  @Override
  public SolverContext createContext() {
    ProcessWrapperContext ctx = new ProcessWrapperContext(solverName, javaBinary);
    if (isUnsatTracking) {
      ctx.enableUnsatTracking();
    }
    return ctx;
  }

  private Result runSolverProcess(List<Expression<Boolean>> f, Valuation result)
      throws IOException, InterruptedException, ClassNotFoundException {
    if (solver == null) {
      ProcessBuilder pb = new ProcessBuilder();
      pb.command(
          javaBinary,
          "-ea",
          "-cp",
          javaClassPath,
          "gov.nasa.jpf.constraints.solvers.encapsulation.SolverRunner",
          "-s",
          solverName,
          "-t",
          Integer.toString(TIMEOUT));
      solver = pb.start();
      registerShutdown(solver);

      OutputStream inSolver = solver.getOutputStream();
      inObject = new ObjectOutputStream(inSolver);
      InputStream errSolver = solver.getErrorStream();
      bes = new BufferedInputStream(errSolver);
      InputStream outSolver = solver.getInputStream();
      bos = new BufferedInputStream(outSolver);

      if (isUnsatTracking) {
        inObject.writeObject(new EnableUnsatCoreTrackingMessage());
        inObject.flush();
      }
    }
    if (solver.isAlive()) {
      inObject.writeObject(f);
      inObject.flush();
      while (bos.available() == 0 && bes.available() == 0) {
        // Thread.sleep(5);
      }
      if (!checkBes(bes, f)) {
        if (outObject == null) {
          outObject = new ObjectInputStream(bos);
        }
        Object start = (StartSolvingMessage) outObject.readObject();
      }
      while (bos.available() == 0 && bes.available() == 0) {
        Thread.sleep(1);
      }
      if (!checkBes(bes, f)) {
        Object done = outObject.readObject();
        if (done instanceof StopSolvingMessage) {
          Object o = outObject.readObject();

          if (o instanceof SolvingResultMessage) {
            SolvingResultMessage res = (SolvingResultMessage) o;
            if (res.getResult().equals(Result.SAT) && result != null) {
              for (ValuationEntry e : res.getVal()) {
                result.addEntry(e);
              }
              try {
                Expression completeExpression = ExpressionUtil.and(f);
                assert (Boolean) completeExpression.evaluateSMT(result);
              } catch (UnsupportedOperationException e) {
                // This might happen if something in the expression does not support the valuation.
              }
            }
            return res.getResult();
          }
        } else if (done instanceof TimeOutSolvingMessage) {
          System.out.println("Timeout in process Solver");
          solver.destroyForcibly();
          return Result.TIMEOUT;
        }
      } else {
        return Result.ERROR;
      }
    }
    return Result.DONT_KNOW;
  }

  public void shutdown() throws IOException {
    if (solver != null && solver.isAlive()) {
      StopSolvingMessage ssm = new StopSolvingMessage();
      ObjectOutputStream os = new ObjectOutputStream(solver.getOutputStream());
      os.writeObject(ssm);
      os.flush();
    }
  }

  private void registerShutdown(Process solver) {
    Runtime.getRuntime()
        .addShutdownHook(
            new Thread(
                () -> {
                  try {
                    shutdown();
                  } catch (IOException e) {
                    e.printStackTrace();
                    solver.destroyForcibly();
                  }
                }));
  }

  private boolean checkBes(BufferedInputStream bes, Object f) throws IOException {
    if (bes.available() > 0) {
      try {
        ObjectInputStream errObject = new ObjectInputStream(bes);
        Object err = errObject.readObject();
        Exception e = (Exception) err;
        e.printStackTrace();
      } catch (ClassNotFoundException e) {
        System.out.println("f: " + f);
        logCallToSolver(f);
      } catch (StreamCorruptedException e) {
        System.out.println("There was something on std err, that could not be read");
      }
      return true;
    }
    return false;
  }

  private void logCallToSolver(Object f) {
    String fileName = "/tmp/serialized_" + solverName + Long.toString(System.nanoTime());
    try (FileOutputStream fo = new FileOutputStream(fileName)) {
      ObjectOutputStream oo = new ObjectOutputStream(fo);
      oo.writeObject(f);
    } catch (FileNotFoundException e) {
      e.printStackTrace();
    } catch (IOException e) {
      e.printStackTrace();
    }
    System.out.println("Logged an Object to: " + fileName);
  }

  @Override
  public String getName() {
    return solverName;
  }

  @Override
  public void enableUnsatTracking() {
    isUnsatTracking = true;
  }

  @Override
  public List<Expression<Boolean>> getUnsatCore() {
    if (solver != null) {
      try {
        inObject.writeObject(new GetUnsatCoreMessage());
        inObject.flush();
        while (bos.available() == 0 && bes.available() == 0) {
          // Thread.sleep(5);
        }
        if (!checkBes(bes, null)) {
          UnsatCoreMessage ucm = (UnsatCoreMessage) outObject.readObject();
          return ucm.getUnsatCore();
        }
      } catch (IOException | ClassNotFoundException e) {
        e.printStackTrace();
      }
    }
    return null;
  }
}
