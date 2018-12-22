printString(x:int[])

sort(a: int[]) {
  i:int = 0
  n:int = length(a)
  while (i < n) {
      j:int = i
      while (j > 0) {
        if (a[j-1] > a[j]) {
            swap:int = a[j]
            a[j] = a[j-1]
            a[j-1] = swap
        }
        j = j-1
      }
      i = i+1
  }
}


main():int
{
    x:int[] = "Wroclaw"
    sort(x)
    printString(x)
    return 1
}

//@PRACOWNIA
//@out Waclorw
//@out Exit code: 1