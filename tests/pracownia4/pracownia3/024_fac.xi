fac(x:int):int
{
    res:int = 1
    while (x > 0) {
        res = x*res
        x = x - 1
    }
    return res
}

main():int
{
    return fac(5)
}

//@PRACOWNIA
//@out Exit code: 120