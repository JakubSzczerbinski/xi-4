main():int
{
    i:int = 0;
    n:int = 10;
    sum:int = 0;
    while (i < n) {
        j:int = 0
        while (j < n) {
            sum = sum + j
            j = j + 1
        }
        i = i + 1
    }
    return sum
}

//@PRACOWNIA
//@out Exit code: 450