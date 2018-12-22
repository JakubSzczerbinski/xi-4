printInt(x:int)

sumtab(xs:int[]):int {
    sum:int = 0
    i:int = 0
    n:int = length(xs)
    while (i < n) {
        sum = sum + xs[i]
        i = i + 1
    }
    return sum
}

main():int
{
    xs:int[] = { 0, 1, 2, 3, 4, 5, 6, 7, 8, 9 }
    printInt(sumtab(xs))
    return 0
}

//@PRACOWNIA
//@out 45
//@out Exit code: 0