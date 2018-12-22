pred():bool
{
    return false
}

main():int
{
    x:bool = true
    result:int = 13
    while x | pred() {
        result = 100
        x = false 
    }
    return result
}

//@PRACOWNIA
//@out Exit code: 100
