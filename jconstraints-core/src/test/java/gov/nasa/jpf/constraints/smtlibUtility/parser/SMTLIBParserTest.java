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

package gov.nasa.jpf.constraints.smtlibUtility.parser;

import static gov.nasa.jpf.constraints.smtlibUtility.parser.utility.ResourceParsingHelper.parseResourceFile;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.Valuation;
import gov.nasa.jpf.constraints.api.Variable;
import gov.nasa.jpf.constraints.expressions.Constant;
import gov.nasa.jpf.constraints.expressions.NumericBooleanExpression;
import gov.nasa.jpf.constraints.expressions.NumericComparator;
import gov.nasa.jpf.constraints.expressions.NumericCompound;
import gov.nasa.jpf.constraints.expressions.StringBooleanExpression;
import gov.nasa.jpf.constraints.expressions.StringBooleanOperator;
import gov.nasa.jpf.constraints.expressions.UnaryMinus;
import gov.nasa.jpf.constraints.smtlibUtility.SMTProblem;
import gov.nasa.jpf.constraints.types.BuiltinTypes;
import java.io.IOException;
import java.math.BigInteger;
import org.junit.jupiter.api.Disabled;
import org.junit.jupiter.api.Tag;
import org.junit.jupiter.api.Test;

@Tag("base")
@Tag("jsmtlib")
public class SMTLIBParserTest {

  @Test
  public void parsingRoundTripPrimeConesTest() throws IOException, SMTLIBParserException {
    final SMTProblem problem = parseResourceFile("test_inputs/prime_cone_sat_15.smt2");

    assertEquals(
        problem.variables.size(),
        15,
        "There are 15 variables declared in the original SMT-Problem,"
            + "hence 15 variables are expected in the parsed problem");
    for (final Variable<?> v : problem.variables) {
      assertEquals(
          v.getType(),
          BuiltinTypes.INTEGER,
          "They are declared as Int in the SMT-problem,"
              + "which is in jConstraint represented as Integer.");
    }
    assertEquals(problem.assertions.size(), 31, "There are 31 assertions in the original problem.");

    final Expression<Boolean> assertion1 = problem.assertions.get(0);
    assertEquals(assertion1.getClass(), NumericBooleanExpression.class);
    final NumericBooleanExpression convertedAssertion1 = (NumericBooleanExpression) assertion1;
    assertEquals(convertedAssertion1.getLeft().getClass(), Variable.class);
    final Variable<?> left = (Variable<?>) convertedAssertion1.getLeft();
    assertEquals(left.getName(), "x_0");
    assertEquals(convertedAssertion1.getRight().toString(), "0");
    assertEquals(((NumericBooleanExpression) assertion1).getComparator(), NumericComparator.GE);

    final Expression<Boolean> assertion30 = problem.assertions.get(29);
    assertEquals(assertion30.getClass(), NumericBooleanExpression.class);
    final NumericBooleanExpression convertedAssertion30 = (NumericBooleanExpression) assertion30;
    assertEquals(convertedAssertion30.getLeft().getClass(), NumericCompound.class);
    final NumericCompound<?> leftPart = (NumericCompound<?>) convertedAssertion30.getLeft();
    assertEquals(leftPart.getRight().getClass(), NumericCompound.class);
    final NumericCompound<?> testTarget = (NumericCompound<?>) leftPart.getRight();
    assertEquals(testTarget.getRight().getClass(), Variable.class);
    final Variable<?> x14 = (Variable<?>) testTarget.getRight();
    assertEquals(x14.getName(), "x_14");
    assertEquals(testTarget.getLeft().getClass(), UnaryMinus.class);
    final UnaryMinus<?> leftTarget = (UnaryMinus<?>) testTarget.getLeft();
    assertEquals(leftTarget.getNegated().getClass(), Constant.class);
    final Constant<?> v282 = (Constant<?>) leftTarget.getNegated();
    assertEquals(v282.getValue(), BigInteger.valueOf(282));
  }

  @Test
  public void parsingRoundTripPRP718Test() throws SMTLIBParserException, IOException {
    final SMTProblem problem = parseResourceFile("test_inputs/prp-7-18.smt2");

    assertEquals(problem.variables.size(), 17);
    assertEquals(problem.assertions.size(), 1);
  }

  @Test
  public void parsingKaluza826Test() throws SMTLIBParserException, IOException {
    final SMTProblem problem = parseResourceFile("test_inputs/kaluza_sat_big_826.smt2");

    assertEquals(problem.variables.size(), 69);
    assertEquals(problem.assertions.size(), 71);
  }

  @Test
  public void parsingPisa000Test() throws SMTLIBParserException, IOException {
    final SMTProblem problem = parseResourceFile("test_inputs/pisa-000.smt2");

    assertEquals(problem.variables.size(), 4);
    assertEquals(problem.assertions.size(), 3);
  }

  @Test
  @Disabled
  public void parsingPisa004Test() throws SMTLIBParserException, IOException {
    final SMTProblem problem = parseResourceFile("test_inputs/pisa-004.smt2");

    assertEquals(problem.variables.size(), 10);
    assertEquals(problem.assertions.size(), 6);
  }

  @Test
  @Disabled
  public void parsingPyEx1Test() throws SMTLIBParserException, IOException {
    final SMTProblem problem = parseResourceFile("test_inputs/pyex_1.smt2");

    assertEquals(problem.variables.size(), 1);
    assertEquals(problem.assertions.size(), 1);
  }

  @Test
  public void parsingJBMCRegression01Test() throws SMTLIBParserException, IOException {
    final SMTProblem problem = parseResourceFile("jbmc-regression_StaticCharMethods06_Main_2.smt2");

    assertEquals(problem.variables.size(), 1);
    assertEquals(problem.assertions.size(), 3);
  }

  @Test
  public void parsingJBMCRegression02Test() throws SMTLIBParserException, IOException {
    final SMTProblem problem =
        parseResourceFile("jbmc-regression_CharSequenceToString_Main_3.smt2");

    assertEquals(problem.variables.size(), 1);
    assertEquals(problem.assertions.size(), 3);
  }

  @Test
  public void parsingRegexUnions() throws SMTLIBParserException, IOException {
    String input =
        "(declare-fun x () String)\n"
            + "(assert (str.in.re x (re.union (str.to.re \"a\") (str.to.re \"b\") (str.to.re \"c\") (str.to.re \"d\") (str.to.re \"e\") (str.to.re \"f\") (str.to.re \"g\") (str.to.re \"h\") (str.to.re \"i\") (str.to.re \"j\") (str.to.re \"k\") (str.to.re \"l\") (str.to.re \"m\") (str.to.re \"n\") )))";
    final SMTProblem parsedProblem = SMTLIBParser.parseSMTProgram(input);
    Expression<Boolean> problem = parsedProblem.getAllAssertionsAsConjunction();
    Valuation val = new Valuation();
    val.setValue(Variable.create(BuiltinTypes.STRING, "x"), "n");
    assertTrue(problem.evaluate(val));
    assertTrue(problem.toString().contains("(str.to.re c)"));
  }

  @Test
  public void parsingSuffixOf() throws SMTLIBParserException, IOException {
    String input = "(declare-fun a () String)\n" + "(assert (str.suffixof a \"b\"))";
    final SMTProblem parsedProblem = SMTLIBParser.parseSMTProgram(input);
    Expression<Boolean> problem = parsedProblem.getAllAssertionsAsConjunction();
    Valuation val = new Valuation();
    val.setValue(Variable.create(BuiltinTypes.STRING, "a"), "b");
    assertTrue(problem.evaluate(val));
    StringBooleanExpression expr = (StringBooleanExpression) parsedProblem.assertions.get(0);
    assertEquals(expr.getOperator(), StringBooleanOperator.SUFFIXOF);
  }

  @Test
  public void jdartExample1Test() throws SMTLIBParserException, IOException {
    final SMTProblem problem =
        parseResourceFile("jbmc-regression_CharSequenceToString_Main_10.smt2");

    assertEquals(problem.variables.size(), 1);
    assertEquals(problem.assertions.size(), 4);
  }

  @Test
  public void jdartExample2Test() throws SMTLIBParserException, IOException {
    final SMTProblem problem =
        parseResourceFile("jbmc-regression_CharSequenceToString_Main_8.smt2");

    assertEquals(problem.variables.size(), 1);
    assertEquals(problem.assertions.size(), 4);
  }

  @Test
  public void jdartExample3Test() throws SMTLIBParserException, IOException {
    final SMTProblem problem = parseResourceFile("jbmc-regression_StaticCharMethods02_Main_8.smt2");

    assertEquals(problem.variables.size(), 1);
    assertEquals(problem.assertions.size(), 4);
  }

  @Test
  public void stringExample1CommentTest() throws SMTLIBParserException, IOException {
    final SMTProblem problem = parseResourceFile("6381_7979.corecstrs.readable.smt2");

    assertEquals(problem.variables.size(), 129);
    assertEquals(problem.assertions.size(), 110);
  }

  @Test
  public void stringExample2CommentTest() throws SMTLIBParserException, IOException {
    final SMTProblem problem = parseResourceFile("17165_replace-010.smt2");

    assertEquals(problem.variables.size(), 3);
    assertEquals(problem.assertions.size(), 2);
  }

  @Test
  public void stringExample3CommentTest() throws SMTLIBParserException, IOException {
    final SMTProblem problem = parseResourceFile("16985_regex-042.smt2");

    assertEquals(problem.variables.size(), 4);
    assertEquals(problem.assertions.size(), 3);
  }

  @Test
  public void operatorMod01Test() throws SMTLIBParserException, IOException {
    final SMTProblem problem =
        parseResourceFile("2008_5735c9082c3f9cd487c6376032029bb499ba1f87113dc9ca03adc6bc.smt2");

    assertEquals(problem.variables.size(), 1);
    assertEquals(problem.assertions.size(), 1);
  }

  @Test
  public void multipleCheckSatTest() throws SMTLIBParserException, IOException {
    String input =
        "(declare-fun x () String)\n"
            + "(declare-fun y () String)\n"
            + "(assert (= x \"hallo\"))\n"
            + "(assert (str.in.re x (re.* (re.range \"a\" \"u\"))))\n"
            + "(check-sat)\n"
            + "(check-sat)";
    SMTProblem problem = SMTLIBParser.parseSMTProgram(input);
    assertEquals(problem.variables.size(), 2);
    assertEquals(problem.assertions.size(), 2);
  }

  @Test
  public void encodingError1Test() throws SMTLIBParserException, IOException {
    final SMTProblem problem = parseResourceFile("5062_htmlCleaner13.smt2");

    assertEquals(problem.variables.size(), 16464);
    assertEquals(problem.assertions.size(), 14530);
  }
}
