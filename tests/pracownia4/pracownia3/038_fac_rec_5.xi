fac(x:int):int
{
    if (x == 0) {
        return 1
    }
    return fac(x-1)*x
}

main():int
{
    return fac(5)
}

//@PRACOWNIA
//@out Exit code: 120