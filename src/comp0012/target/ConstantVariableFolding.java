package comp0012.target;

public class ConstantVariableFolding
{
    public int methodOne(){
        int a = 62;
        int b = (a + 764) * 3;
        return b + 1234 - a;
    }

    public double methodTwo(){
        double i = 0.67;
        int j = 1;
        return i + j;
    }

    public boolean methodThree(){
        int x = 12345;
        int y = 54321;
        return x > y;
    }

    public boolean methodFour(){
        long x = 4835783423L;
        long y = 400000;
        long z = x + y;
        return x > y;
    }

    public int methodFive(){
        int x = 45;
        int y = 47;
        x = 50;
        return x + y;
    }

    public int methodSix(){
        int x = 45;
        int y = 50;
        int z = x + y;
        return x + y + z;
    }

    public boolean methodSeven(){
        boolean x = true;
        boolean y = false;
        boolean z = x == y;
        return z;
    }

    public double methodEight(){
        double x = 1.67;
        double y = 2.05;
        double z = 1.67 + 2.05;
        return z;
    }
}