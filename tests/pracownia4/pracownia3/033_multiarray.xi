main():int { 
    xs:int[2][3];
    xs[0][0] = 1;
    xs[0][1] = 2;
    xs[0][2] = 3;
    xs[1][0] = 10;
    xs[1][1] = 20;
    xs[1][2] = 30;
    return xs[0][0] + xs[0][1] + xs[0][2] + xs[1][0] + xs[1][1] + xs[1][2];
}

//@PRACOWNIA
//@out Exit code: 66
