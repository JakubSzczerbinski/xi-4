f(a0:int, a1:int, a2:int, a3:int, a4:int, a5:int, a6:int): int, int, int, int, int, int, int
{
    return a0, a1, a2, a3, a4, a5, a6
}

main():int {
    a0:int, a1:int, a2:int, a3:int, a4:int, a5:int, a6:int = f(10,20,30,40,50,60,70)
    return a0+a1+a2+a3+a4+a5+a6
}

//@PRACOWNIA
//@out Exit code: 280
