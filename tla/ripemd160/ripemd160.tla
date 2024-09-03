------------------------------ MODULE ripemd160 ------------------------------
EXTENDS Reals, Sequences, TLC, Reals, Bitwise

VARIABLES A, B, C, D, E, AA, BB, CC, DD, EE, digest, Message

ModAdd(x, y) == ((x + y) % (2^8))

ModSub(x, y) == ((x - y) % (2^8))

ModMul(x, y) == ((x * y) % (2^8))

RECURSIVE shiftL(_,_)
shiftL(n,pos) == 
    IF pos = 0 
    THEN n
    ELSE LET double(z) == 2 * z
         IN shiftL(double(n), pos - 1)

LeftRotate(x, c) == 
    (shiftL(x, c) | shiftR(x, 32 - c)) % (2^32)

F1A(N, P, Q) == ModSub(ModAdd(N, ModSub(ModAdd(P, Q), ModMul(P, Q))), ModMul(N, ModSub(ModAdd(P, Q), ModMul(P, Q))))
F2A(N, P, Q) == ModAdd(ModMul(N, P), ModMul(ModSub(1, N), Q))
F3A(N, P, Q) == ModSub(ModAdd(N, ModSub(ModAdd(P, ModSub(1, Q)), ModMul(P, ModSub(1, Q)))), ModMul(N, ModSub(ModAdd(P, ModSub(1, Q)), ModMul(P, ModSub(1, Q)))))
F4A(N, P, Q) == ModAdd(ModMul(N, Q), ModMul(P, ModSub(1, Q)))
F5A(N, P, Q) == ModSub(ModAdd(N, ModSub(ModAdd(P, ModSub(1, Q)), ModMul(P, ModSub(1, Q)))), ModMul(N, ModSub(ModAdd(P, ModSub(1, Q)), ModMul(P, ModSub(1, Q)))))

F1B(N, P, Q) == ModSub(ModAdd(N, ModSub(ModAdd(P, Q), ModMul(P, Q))), ModMul(N, ModSub(ModAdd(P, Q), ModMul(P, Q))))
F2B(N, P, Q) == ModAdd(ModMul(N, Q), ModMul(P, ModSub(1, Q)))
F3B(N, P, Q) == ModSub(ModAdd(ModAdd(N, ModSub(1, P)), Q), ModMul(ModAdd(N, ModSub(1, P)), Q))
F4B(N, P, Q) == ModAdd(ModMul(N, P), ModMul(ModSub(1, N), Q))
F5B(N, P, Q) == ModSub(ModAdd(N, ModSub(ModAdd(P, ModSub(1, Q)), ModMul(P, ModSub(1, Q)))), ModMul(N, ModSub(ModAdd(P, ModSub(1, Q)), ModMul(P, ModSub(1, Q)))))

K1A == 0
K2A == 11
K3A == 13
K4A == 17
K5A == 19
K1B == 23
K2B == 27
K3B == 31
K4B == 37
K5B == 0

S1A == <<11, 14, 15, 12, 5, 8, 7, 9, 11, 13, 14, 15, 6, 7, 9, 8>>
S2A == <<7, 4, 13, 1, 10, 6, 15, 3, 12, 0, 9, 5, 2, 14, 11, 8>>
S3A == <<11, 13, 6, 7, 14, 9, 15, 8, 2, 0, 13, 11, 5, 14, 7, 13>>
S4A == <<7, 5, 6, 8, 11, 14, 14, 6, 8, 13, 5, 14, 13, 6, 5, 12>>
S5A == <<9, 15, 5, 11, 6, 8, 13, 12, 5, 7, 11, 12, 8, 15, 6, 5>>
S1B == <<8, 9, 11, 13, 15, 7, 12, 8, 6, 4, 14, 15, 8, 11, 10, 7>>
S2B == <<9, 13, 7, 15, 8, 14, 11, 2, 7, 1, 10, 13, 12, 5, 8, 9>>
S3B == <<8, 12, 4, 9, 10, 0, 15, 5, 3, 14, 7, 14, 5, 6, 11, 13>>
S4B == <<5, 6, 11, 14, 10, 2, 4, 9, 7, 8, 15, 11, 13, 9, 3, 1>>
S5B == <<12, 5, 15, 13, 6, 8, 2, 10, 7, 0, 9, 14, 3, 5, 1, 6>>

F(N, P, Q, isA, num) ==
    IF isA THEN
        IF num = 1 THEN F1A(N, P, Q)
        ELSE IF num = 2 THEN F2A(N, P, Q)
        ELSE IF num = 3 THEN F3A(N, P, Q)
        ELSE IF num = 4 THEN F4A(N, P, Q)
        ELSE F5A(N, P, Q)
    ELSE
        IF num = 1 THEN F1B(N, P, Q)
        ELSE IF num = 2 THEN F2B(N, P, Q)
        ELSE IF num = 3 THEN F3B(N, P, Q)
        ELSE IF num = 4 THEN F4B(N, P, Q)
        ELSE F5B(N, P, Q)


ProcessChunk(chunk) ==
  LET 
    P == [j \in 0..15 |-> SubSeq(Message, (chunk-1)*512 + j*32 + 1, (chunk-1)*512 + (j+1)*32)]
  IN
    /\ AA' = A
    /\ BB' = B
    /\ CC' = C
    /\ DD' = D
    /\ EE' = E
    /\ \A round \in 1..5 :
        LET
          K1 == IF round = 1 THEN K1A ELSE IF round = 2 THEN K2A ELSE IF round = 3 THEN K3A ELSE IF round = 4 THEN K4A ELSE K5A
          S1 == IF round = 1 THEN S1A ELSE IF round = 2 THEN S2A ELSE IF round = 3 THEN S3A ELSE IF round = 4 THEN S4A ELSE S5A
          K2 == IF round = 1 THEN K1B ELSE IF round = 2 THEN K2B ELSE IF round = 3 THEN K3B ELSE IF round = 4 THEN K4B ELSE K5B
          S2 == IF round = 1 THEN S1B ELSE IF round = 2 THEN S2B ELSE IF round = 3 THEN S3B ELSE IF round = 4 THEN S4B ELSE S5B
        IN
        /\ \A i \in 1..16 :
            LET
              resultA == F(B, C, D, TRUE, round) % (2^8)
              resultB == F(BB, CC, DD, FALSE, round) % (2^8)
            IN
              /\ A' = LeftRotate(((E + resultA) ^^ K1), S1[i]) % (2^8)
              /\ E' = D % (2^8)
              /\ D' = LeftRotate(C, 10) % (2^8)
              /\ C' = B % (2^8)
              /\ B' = A % (2^8)
              /\ AA' = LeftRotate(((EE + resultB) ^^ K2), S2[i]) % (2^8)
              /\ EE' = DD % (2^8)
              /\ DD' = LeftRotate(CC, 10) % (2^8)
              /\ CC' = BB % (2^8)
              /\ BB' = AA % (2^8)
    /\ UNCHANGED <<digest, Message>>


Preprocess ==
  LET msg == Append(Message, 0)
  IN /\ Len(msg) % 512 = 448
     /\ Message' = Append(msg, Len(Message) % (2^64))

Init ==
    /\ A = 13
    /\ B = 17
    /\ C = 19
    /\ D = 23
    /\ E = 29
    /\ AA = 13
    /\ BB = 17
    /\ CC = 19
    /\ DD = 23
    /\ EE = 29
    /\ digest = << >>
    /\ Message = <<>>

FinalCombine ==
    /\ A' = ModAdd(A, AA)
    /\ B' = ModAdd(B, BB)
    /\ C' = ModAdd(C, CC)
    /\ D' = ModAdd(D, DD)
    /\ E' = ModAdd(E, EE)
    /\ digest' = <<A', B', C', D', E'>>
    /\ UNCHANGED <<AA, BB, CC, DD, EE, Message>>


Next == 
    \/ Preprocess
    \/ \E chunk \in 1..(Len(Message) \div 512) : ProcessChunk(chunk)
    \/ FinalCombine


Spec == Init /\ [][Next]_<<A, B, C, D, E, AA, BB, CC, DD, EE, digest, Message>>

============================ END MODULE ============================
