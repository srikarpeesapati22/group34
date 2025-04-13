package comp0012.target;

import org.junit.Test;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;

/**
 * Test constant variable folding
 */
public class ConstantVariableFoldingTest {

    ConstantVariableFolding cvf = new ConstantVariableFolding();

    @Test
    public void testMethodOne(){
        assertEquals(3650, cvf.methodOne());
    }

    @Test
    public void testMethodTwo(){
        assertEquals(1.67, cvf.methodTwo(), 0.001);
    }

    @Test
    public void testMethodThree(){
        assertEquals(false, cvf.methodThree());
    }
    
    @Test
    public void testMethodFour(){
        assertEquals(true, cvf.methodFour());
    }
    
    @Test
    public void testMethodFive() {
        // x = 50, y = 47, return 50 + 47 = 97
        assertEquals(97, cvf.methodFive());
    }

    @Test
    public void testMethodSix() {
        // x = 45, y = 50, z = 95, return 45 + 50 + 95 = 190
        assertEquals(190, cvf.methodSix());
    }

    @Test
    public void testMethodSeven() {
        // x = true, y = false, z = x == y = false
        assertFalse(cvf.methodSeven());
    }

    @Test
    public void testMethodEight() {
        // z = 1.67 + 2.05 = 3.72
        assertEquals(3.72, cvf.methodEight(), 0.0001);
    }

}
