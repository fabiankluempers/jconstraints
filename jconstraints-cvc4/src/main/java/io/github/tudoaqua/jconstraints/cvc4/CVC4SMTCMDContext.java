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

package io.github.tudoaqua.jconstraints.cvc4;

import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.UNSATCoreSolver;
import gov.nasa.jpf.constraints.smtlibUtility.smtconverter.SMTLibExportVisitorConfig;
import gov.nasa.jpf.constraints.smtlibUtility.smtsolver.SMTCMDContext;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

public class CVC4SMTCMDContext extends SMTCMDContext implements UNSATCoreSolver {

  public CVC4SMTCMDContext(String[] cmd, SMTLibExportVisitorConfig config) {
    super(cmd, config);
  }

  public CVC4SMTCMDContext(String[] cmd) {
    super(cmd);
  }

  @Override
  public void enableUnsatTracking() {
    super.enableUnsatCore();
    List<String> new_command = new ArrayList<>(Arrays.asList(super.command));
    new_command.add(CVC4SMTCMDSolver.UNSAT_CORE_EXTENSION);
    super.command = new_command.toArray(new String[0]);
  }

  @Override
  public List<Expression<Boolean>> getUnsatCore() {
    return super.getUnsatCore();
  }
}
