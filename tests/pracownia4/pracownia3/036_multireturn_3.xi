f(): int, int, int
{
    return 10, 15, 20
}

main():int {
    x:int, y:int, z:int = f()
    return x + y + z;
}

//@PRACOWNIA
//@out Exit code: 45
