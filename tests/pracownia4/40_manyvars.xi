f(values:int[]):int
{
    r0:int = values[0]
    r1:int = values[1]
    r2:int = values[2]
    r3:int = values[3]
    r4:int = values[4]
    r5:int = values[5]
    r6:int = values[6]
    r7:int = values[7]
    r8:int = values[8]
    r9:int = values[9]
    r10:int = values[10]
    r11:int = values[11]
    r12:int = values[12]
    r13:int = values[13]
    r14:int = values[14]
    r15:int = values[15]
    r16:int = values[16]
    r17:int = values[17]
    r18:int = values[18]
    r19:int = values[19]
    r20:int = values[20]
    r21:int = values[21]
    r22:int = values[22]
    r23:int = values[23]
    r24:int = values[24]
    r25:int = values[25]
    r26:int = values[26]
    r27:int = values[27]
    r28:int = values[28]
    r29:int = values[29]
    r30:int = values[30]
    r31:int = values[31]
    r32:int = values[32]
    r33:int = values[33]
    r34:int = values[34]
    r35:int = values[35]
    r36:int = values[36]
    r37:int = values[37]
    r38:int = values[38]
    r39:int = values[39]
    return r0 + r1 + r2 + r3 + r4 + r5 + r6 + r7 + r8 + r9 + r10 + r11 + r12 + r13 + r14 + r15 + r16 + r17 + r18 + r19 + r20 + r21 + r22 + r23 + r24 + r25 + r26 + r27 + r28 + r29 + r30 + r31 + r32 + r33 + r34 + r35 + r36 + r37 + r38 + r39
}
prepare_values(n:int):int[]
{
    result:int[] = {}
    i:int = 0
    while (i < n) {
        result = result + {i*10}
        i = i + 1
    }
    return result
}

main():int
{
    values:int[] = prepare_values(40)
    return f(values)
}

//@PRACOWNIA
//@out Exit code: 7800
    
