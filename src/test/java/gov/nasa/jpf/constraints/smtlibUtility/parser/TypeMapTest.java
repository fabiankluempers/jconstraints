package gov.nasa.jpf.constraints.smtlibUtility.parser;

import gov.nasa.jpf.constraints.types.BuiltinTypes;
import org.testng.annotations.Test;

import static org.testng.Assert.assertEquals;

public class TypeMapTest {

    @Test
    public void integerMapTest(){
        assertEquals(TypeMap.getType("int"), BuiltinTypes.INTEGER);
        assertEquals(TypeMap.getType("InT"), BuiltinTypes.INTEGER);
        assertEquals(TypeMap.getType("iNT"), BuiltinTypes.INTEGER);
        assertEquals(TypeMap.getType("Int"), BuiltinTypes.INTEGER);
        assertEquals(TypeMap.getType("INT"), BuiltinTypes.INTEGER);
    }
}
