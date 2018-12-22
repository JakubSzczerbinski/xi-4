printString(xs:int[])

flatten_easy(xss:int[][]):int[]
{
    xs:int[] = {}
    n:int = length(xss)
    i:int = 0
    while (i < n) {
        xs = xs + xss[i]
        i = i + 1
    }

    return xs
}

main():int
{
    xss:int[][] = { 
        "Uniwersytet",
        " ",
        "Wroclawski"
    }

    printString(flatten_easy(xss))

    return 0
}

//@PRACOWNIA
//@out Uniwersytet Wroclawski
//@out Exit code: 0