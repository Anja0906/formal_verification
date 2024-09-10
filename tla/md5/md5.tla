------------------------------ MODULE md5 ------------------------------
EXTENDS Integers, Sequences, FiniteSets, Bitwise

VARIABLES A, B, C, D, AA, BB, CC, DD, M, K, S, Message, digest

RECURSIVE shiftL(_,_)
shiftL(n,pos) == 
    IF pos = 0 
    THEN n
    ELSE LET double(z) == 2 * z
         IN shiftL(double(n), pos - 1)
         
LeftRotate(x, c) == (shiftL(x, c) | shiftR(x, 32 - c)) % (2^8)

Preprocess ==
  LET msg == Append(Message, 0)
  IN /\ Len(msg) % 512 = 448
     /\ Message' = Append(msg, Len(Message) % (2^64)) (* Po standardu MD5 *)

ProcessChunk(chunk) ==
  LET P == [j \in 0..15 |-> SubSeq(Message, (chunk-1)*512 + j*32 + 1, (chunk-1)*512 + (j+1)*32)]
  IN
    /\ AA' = A
    /\ BB' = B
    /\ CC' = C
    /\ DD' = D
    /\ \A i \in 0..63 :
        LET
          F ==  IF i \in 0..15 THEN (B & C) | ((Not(B)) & D)
                ELSE IF i \in 16..31 THEN (D & B) | ((Not(D)) & C)
                ELSE IF i \in 32..47 THEN (B ^^ C) ^^ D
                ELSE C ^^ (B | (Not(D)))
          g ==  IF i \in 0..15 THEN i
                ELSE IF i \in 16..31 THEN (5*i + 1) % 16
                ELSE IF i \in 32..47 THEN (3*i + 5) % 16
                ELSE (7*i) % 16
        IN
          /\ F' = (F + A + K[i] + P[g]) % (2^8) (* Sve operacije su modulo 2^8 *)
          /\ A' = D
          /\ D' = C
          /\ C' = B
          /\ B' = (B + LeftRotate(F', S[i])) % (2^8)
    /\ A' = (A + AA) % (2^8)
    /\ B' = (B + BB) % (2^8)
    /\ C' = (C + CC) % (2^8)
    /\ D' = (D + DD) % (2^8)


FinalHash ==
  /\ A' = (A + AA) % (2^8)
  /\ B' = (B + BB) % (2^8)
  /\ C' = (C + CC) % (2^8)
  /\ D' = (D + DD) % (2^8)
  /\ digest' = <<A', B', C', D'>>
  /\ UNCHANGED <<AA, BB, CC, DD, Message, M, K, S>>

Init ==
  /\ A = 67
  /\ B = 31
  /\ C = 19
  /\ D = 47
  /\ K = <<19, 55, 50, 72, 59, 8, 66, 34,
           29, 14, 9, 17, 19, 23, 45, 80,
           84, 27, 77, 35, 97, 84, 25, 1,
           96, 7, 65, 76, 43, 20, 4, 12,
           25, 85, 95, 93, 97, 48, 22, 15,
           67, 4, 43, 30, 41, 74, 18, 16,
           64, 21, 57, 75, 49, 58, 18, 3,
           20, 12, 20, 88, 4, 49, 66, 90>>
  /\ S = <<7, 12, 17, 22, 7, 12, 17, 22, 7, 12, 17, 22, 7, 12, 17, 22,
           5, 9, 14, 20, 5, 9, 14, 20, 5, 9, 14, 20, 5, 9, 14, 20,
           4, 11, 16, 23, 4, 11, 16, 23, 4, 11, 16, 23, 4, 11, 16, 23,
           6, 10, 15, 21, 6, 10, 15, 21, 6, 10, 15, 21, 6, 10, 15, 21>>
  /\ AA = A
  /\ BB = B
  /\ CC = C
  /\ DD = D
  /\ Message = <<>>
  /\ M = <<>>
  /\ digest = <<>>


Next ==
  \/ Preprocess
  \/ \E chunk \in 1..(Len(Message) \div 512) : ProcessChunk(chunk)
  \/ FinalHash

Spec == Init /\ [][Next]_<<A, B, C, D, AA, BB, CC, DD, Message, M, digest>>

============================ END MODULE ============================
