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

package gov.nasa.jpf.constraints.smtlibUtility.export;

import static gov.nasa.jpf.constraints.util.CharsetIO.toNormalizedStringUTF8;
import static gov.nasa.jpf.constraints.util.CharsetIO.wrapInUTF8PrintStream;
import static org.junit.jupiter.api.Assertions.assertEquals;

import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.SolverContext;
import gov.nasa.jpf.constraints.smtlibUtility.smtconverter.SMTLibExportWrapper;
import gov.nasa.jpf.constraints.solvers.dontknow.DontKnowSolver;
import java.io.ByteArrayOutputStream;
import java.io.PrintStream;

public class Util {
  static void runTest(Expression expr, String expected) {
    SolverContext se;
    ByteArrayOutputStream baos;
    PrintStream ps;
    baos = new ByteArrayOutputStream();
    ps = wrapInUTF8PrintStream(baos);
    se = (new SMTLibExportWrapper(new DontKnowSolver(), ps)).createContext();
    se.add(expr);
    String output = toNormalizedStringUTF8(baos);
    assertEquals(output, expected);
  }
}
