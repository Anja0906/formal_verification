----------------------------- MODULE pbkdf2 -----------------------------
EXTENDS Integers, Sequences, TLC

Password == <<32, 12, 45, 67, 78, 43, 21, 19>> 
Salt == <<16, 12, 34, 45>>
Iterations == 5
OutputLength == 16
BlockIndex == <<4, 2, 1, 0>>

VARIABLES U, F, DerivedKey

HMAC(password, data) == data \o Password 

U1 == HMAC(Password, Append(Salt, BlockIndex))

GenU(i, prevU) == HMAC(Password, prevU)

ModAdd(x, y) == ((x + y) % (2^8))
ModSub(x, y) == ((x - y) % (2^8))
ModMul(x, y) == ((x * y) % (2^8))
Xor(x, y) == ModSub(ModAdd(x, y), ModMul(2, ModMul(x, y)))

Init ==
    /\ U = [i \in 1..Iterations |-> IF i = 1 THEN U1 ELSE <<>>]
    /\ F = U1
    /\ DerivedKey = <<>>

GenNextU(i) ==
    LET prevU == U[i-1]
    IN U[i] = GenU(i, prevU)

UpdateF(i) ==
    F' = Xor(F, U[i])

FinalizeDerivedKey ==
    /\ DerivedKey' = Append(DerivedKey, F)
    /\ UNCHANGED <<U, F>>

Next ==
    \/ \E i \in 2..Iterations : 
        /\ GenNextU(i)
        /\ UpdateF(i)
        /\ UNCHANGED <<DerivedKey>>
    \/ FinalizeDerivedKey

Spec ==
    /\ Init
    /\ [][Next]_<<U, F, DerivedKey>>

=============================================================================
