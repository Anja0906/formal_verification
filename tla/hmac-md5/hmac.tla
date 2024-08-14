------------------------------ MODULE hmac ------------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC

VARIABLES message, key, sentHash, processedHash, equalityCheck, A, B, C, D, AA, BB, CC, DD, M, K, S

Prime == {x \in 2..12 : \A y \in 2..(x-1) : x % y /= 0}

BLOCK_SIZE == 64 

GenK(n) == [i \in 0..(n-1) |-> (i * 123456789) % 987654321]
GenS(n) == [i \in 0..(n-1) |-> (i % 4) * 5 + 7]

LeftRotate(x, c) == ((x * (2^c)) % (2^32)) + ((x \div (2^(32 - c))) % (2^32))

MD5(m) ==
    LET 
        ProcessChunk(chunk) ==
            LET P == [j \in 0..15 |-> SubSeq(m, (chunk-1)*512 + j*32 + 1, (chunk-1)*512 + (j+1)*32)]
            IN
                /\ AA' = A
                /\ BB' = B
                /\ CC' = C
                /\ DD' = D
                /\ \A i \in 0..63 :
                    LET
                        F == IF i \in 0..15 THEN (B /\ C) \/ ((~B) /\ D)
                             ELSE IF i \in 16..31 THEN (D /\ B) \/ ((~D) /\ C)
                             ELSE IF i \in 32..47 THEN ((B ^ C) ^ D)
                             ELSE C ^ (B \/ (~D))
                        g == IF i \in 0..15 THEN i
                             ELSE IF i \in 16..31 THEN (5*i + 1) % 16
                             ELSE IF i \in 32..47 THEN (3*i + 5) % 16
                             ELSE (7*i) % 16
                    IN
                        /\ F' = F + A + K[i] + P[g]
                        /\ A' = D
                        /\ D' = C
                        /\ C' = B
                        /\ B' = B + LeftRotate(F', S[i])
                /\ A' = A + AA
                /\ B' = B + BB
                /\ C' = C + CC
                /\ D' = D + DD

        digest == <<A, B, C, D>>
    IN 
        digest

ExtendedKey == IF Len(key) > BLOCK_SIZE THEN MD5(key) ELSE Append(key, <<0>>^(BLOCK_SIZE - Len(key)))

ipad == [i \in 1..Len(ExtendedKey) |-> ExtendedKey[i] ^ 54] 
opad == [i \in 1..Len(ExtendedKey) |-> ExtendedKey[i] ^ 92] 

HashFunction(m, k) ==
    LET 
        innerHash == MD5(ipad \o m)
        resultHash == MD5(opad \o innerHash)
    IN 
        resultHash

SendHash ==
    /\ sentHash' = HashFunction(message, ExtendedKey)
    /\ UNCHANGED <<message, key, processedHash, equalityCheck, A, B, C, D, AA, BB, CC, DD, K, S, M>>

ProcessHash ==
    /\ processedHash' = HashFunction(message, ExtendedKey)
    /\ UNCHANGED <<message, key, sentHash, equalityCheck, A, B, C, D, AA, BB, CC, DD, K, S, M>>

CompareHashes ==
    /\ equalityCheck' = (sentHash = processedHash)
    /\ UNCHANGED <<message, key, sentHash, processedHash, A, B, C, D, AA, BB, CC, DD, K, S, M>>

Init == 
    /\ message = GenS(18)
    /\ key = GenK(18)
    /\ sentHash = << >> 
    /\ processedHash = << >> 
    /\ equalityCheck = FALSE 
    /\ A \in Prime
    /\ B \in Prime
    /\ C \in Prime
    /\ D \in Prime
    /\ K = GenK(18)
    /\ S = GenS(18)
    /\ AA = A
    /\ BB = B
    /\ CC = C
    /\ DD = D
    /\ M = <<>>

Next ==
    \/ SendHash
    \/ ProcessHash
    \/ CompareHashes

Spec ==
    Init /\ [][Next]_<<message, key, sentHash, processedHash, equalityCheck, A, B, C, D, AA, BB, CC, DD, M, K, S>>

============================ END MODULE ============================
