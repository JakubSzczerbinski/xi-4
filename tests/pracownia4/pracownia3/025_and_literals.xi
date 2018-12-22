convert(b:bool):int
{
    if b {
        return 1
    } else {
        return 0
    }
}

main():int
{
    return convert(true & false)
}

//@PRACOWNIA
//@out Exit code: 0
