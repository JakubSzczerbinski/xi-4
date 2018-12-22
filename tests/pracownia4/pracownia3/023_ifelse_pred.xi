pred():bool
{
    return true
}

main():int
{
    result:int = 13
    if pred() {
        result = 100
    } else {
        result = 1
    }
    return result
}

//@PRACOWNIA
//@out Exit code: 100
