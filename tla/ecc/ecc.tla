----------------------------- MODULE ecc -----------------------------
EXTENDS Integers, Sequences, TLC, Bitwise

p == 203
a == 5
b == 13
Gx == 4
Gy == 5
n == 19
G == <<Gx, Gy>>

VARIABLES x, y, scalar, P, Q, R, k, s, d, r, z, validPoint

EllipticCurve(e, f) ==
    (f^2) = (e^3 + a * e + b) % p

ValidPoint(f, e) ==
    EllipticCurve(f, e)

InverseMod(m, l) ==
    LET 
        RECURSIVE extendedGCD(_, _)
        extendedGCD(u, v) == IF v = 0 THEN <<u, 1, 0>>
                            ELSE 
                                LET res == extendedGCD(v, u % v) IN
                                <<res[1], res[3], res[2] - (u \div v) * res[3]>>
        gcdRes == extendedGCD(m, l)
        gcd == gcdRes[1]
        inv == gcdRes[2] % l
    IN 
        IF gcd /= 1 THEN 
            IF gcd = 0 THEN 0 ELSE <<0, "Error: gcd(m, l) is not 1">>
        ELSE 
            IF inv < 0 THEN inv + l ELSE inv


PointAddition(J, K) ==
    LET
        x1 == J[1]
        y1 == J[2]
        x2 == K[1]
        y2 == K[2]
        isNeutral(A) == (A = <<0, 0>>)
        slope == 
            IF isNeutral(J) THEN 
                <<x2, y2>>
            ELSE IF isNeutral(K) THEN 
                <<x1, y1>>
            ELSE IF (x1 = x2) /\ (y1 = y2) THEN 
                ((3 * x1^2 + a) * InverseMod(2 * y1, p)) % p
            ELSE IF (x1 = x2) /\ (y1 /= y2) THEN 
                <<0, 0>>
            ELSE 
                ((y2 - y1) * InverseMod(x2 - x1, p)) % p
    IN
        IF (x1 = x2) /\ (y1 /= y2) THEN 
            /\ x' = 0
            /\ y' = 0
            /\ R' = <<x', y'>>
        ELSE
            /\ x' = (slope^2 - x1 - x2) % p
            /\ y' = ((slope * (x1 - x')) - y1) % p
            /\ R' = <<x', y'>>


RECURSIVE Bits(_)
Bits(scal) ==
    IF scal = 0 THEN <<>>
    ELSE Append(Bits(scal \div 2), scal % 2)

ScalarMultiplication(scal, J) ==
    LET
        bits == Bits(scal)
        R_init == <<0, 0>>
        Q_init == J
        result == [R_acc \in 1..Len(bits) |-> 
                    IF bits[R_acc] = 1 
                    THEN PointAddition(R_init, Q_init)
                    ELSE R_init]
        final_R == result[Len(bits)]
    IN final_R

GeneratePublicKey(d_) ==
    ScalarMultiplication(d_, G)

GenerateSignature(z_, d_) ==
    LET
        SecureRandomSet == {k_ \in 1..(n-1) : TRUE}  
        kVal == CHOOSE k_ \in SecureRandomSet : TRUE
        Rval == ScalarMultiplication(kVal, G)
        rval == IF Rval[1] = 0 THEN 1 ELSE Rval[1] % n
        sval == ((z_ + rval * d_) * InverseMod(kVal, n)) % n
    IN
        <<rval, sval>>


ValidateSignature(r_, s_, z_, Q_) ==
    LET
        w == InverseMod(s_, n)
        u1 == (z_ * w) % n
        u2 == (r_ * w) % n
        X == PointAddition(ScalarMultiplication(u1, G), ScalarMultiplication(u2, Q_))
    IN
        /\ r_ = X[1] % n
        /\ r_ /= 0
        /\ s_ /= 0

Init ==
    /\ x = Gx
    /\ y = Gy
    /\ k = 3 
    /\ s = 5
    /\ d = 7
    /\ r = 11
    /\ z = 13
    /\ P = G
    /\ Q = <<Gx, Gy>>
    /\ R = <<0, 0>>
    /\ validPoint = ValidPoint(Gx, Gy)
    /\ scalar = 17


Next ==
    \/ \E M \in {<<x, y>>}: ValidPoint(x, y) /\ P' = M
    
Spec ==
    Init /\ [][Next]_<<x, y, scalar, P, Q, R, k, s, d, r, z, validPoint>>

============================ END MODULE ============================
