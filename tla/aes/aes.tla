---- MODULE aes ----
EXTENDS Naturals, Sequences, Integers

VARIABLES state, roundKey, round, Nb, Nk, Nr, encrypt

SBox == [i \in 1..4 |-> [j \in 1..4 |-> ((i * j) + 50) % 256]]

Multiply(a, b) ==
    LET result == IF b = 1 THEN a ELSE IF b = 2 THEN (a * 2) % 256 ELSE (a * 3) % 256
    IN result

SubBytes(s) ==
    [i \in 1..Nb |-> [j \in 1..Nk |-> 
        SBox[(s[i][j] % 4) + 1][(s[i][j] % 4) + 1] ]]

ShiftRows(s) ==
    [i \in 1..Nb |-> 
        IF i = 1 THEN s[i]
        ELSE [j \in 1..Nk |-> s[i][((j + i - 2) % Nk) + 1]] ]
InvShiftRows(s) ==
    [i \in 1..Nb |-> 
        IF i = 1 THEN s[i]
        ELSE [j \in 1..Nk |-> s[i][((j - i + Nk) % Nk) + 1]] ]


MixColumns(s) ==
    [i \in 1..Nk |-> 
        LET s0 == s[1][i]
            s1 == s[2][i]
            s2 == s[3][i]
            s3 == s[4][i]
        IN [j \in 1..Nb |-> 
            IF j = 1 THEN (Multiply(s0, 2) + Multiply(s1, 3) + s2 + s3) % 256
            ELSE IF j = 2 THEN (s0 + Multiply(s1, 2) + Multiply(s2, 3) + s3) % 256
            ELSE IF j = 3 THEN (s0 + s1 + Multiply(s2, 2) + Multiply(s3, 3)) % 256
            ELSE (Multiply(s0, 3) + s1 + s2 + Multiply(s3, 2)) % 256]]

InvMixColumns(s) ==
    [i \in 1..Nk |-> 
        LET s0 == s[1][i]
            s1 == s[2][i]
            s2 == s[3][i]
            s3 == s[4][i]
        IN [j \in 1..Nb |-> 
            IF j = 1 THEN (Multiply(s0, 14) + Multiply(s1, 11) + Multiply(s2, 13) + Multiply(s3, 9)) % 256
            ELSE IF j = 2 THEN (Multiply(s0, 9) + Multiply(s1, 14) + Multiply(s2, 11) + Multiply(s3, 13)) % 256
            ELSE IF j = 3 THEN (Multiply(s0, 13) + Multiply(s1, 9) + Multiply(s2, 14) + Multiply(s3, 11)) % 256
            ELSE (Multiply(s0, 11) + s1 + s2 + Multiply(s3, 14)) % 256]]


AddRoundKey(s, k) ==
    [i \in 1..Nb |-> [j \in 1..Nk |-> (s[i][j] + k[i][j]) % 256]]


Round(s, k) ==
    LET newState == MixColumns(ShiftRows(SubBytes(s)))
    IN AddRoundKey(newState, k)
InvRound(s, k) ==
    LET newState == SubBytes(InvShiftRows(InvMixColumns(s)))
    IN AddRoundKey(newState, k)


AESProcess(e, s, k) ==
    IF e THEN Round(s, k)
    ELSE InvRound(s, k)

NextRound ==
    /\ round < Nr
    /\ state' = AESProcess(encrypt, state, roundKey)
    /\ roundKey' = roundKey
    /\ Nb' = Nb
    /\ Nk' = Nk
    /\ Nr' = Nr
    /\ round' = round + 1
    /\ encrypt' = encrypt

Init ==
    /\ state = [i \in 1..4 |-> [j \in 1..4 |-> (i - 1) * 4 + j]]
    /\ roundKey = [i \in 1..4 |-> [j \in 1..4 |-> (i + j + 40) % 256]]
    /\ round = 0
    /\ Nb = 4
    /\ Nk = 4
    /\ Nr = 10
    /\ encrypt = FALSE

Spec ==
    Init /\ [][NextRound]_<<state, round, roundKey, Nb, Nk, Nr, encrypt>>

====

