printString(xs:int[])

flatten_hard(xss:int[][]):int[]
{
    xs:int[] = {}
    n:int = length(xss)
    i:int = 0
    while (i < n) {
        m:int = length(xss[i])
        j:int = 0
        while (j < m) {
            xs = xs + {xss[i][j]}
            j = j + 1
        }
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

    printString(flatten_hard(xss))

    return 0
}

//@PRACOWNIA
//@out Uniwersytet Wroclawski
//@out Exit code: 0