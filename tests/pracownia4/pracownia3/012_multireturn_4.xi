f(): int, int, int, int
{
    return 10, 15, 20, 25
}

main():int {
    x:int, y:int, z:int, v:int = f()
    return x + y + z + v;
}

//@PRACOWNIA
//@out Exit code: 70
