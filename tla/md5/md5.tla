------------------------------ MODULE md5 ------------------------------
EXTENDS Integers, Sequences, FiniteSets

VARIABLES A, B, C, D, AA, BB, CC, DD, M, K, S, Message, digest

LeftRotate(x, c) == ((x * (2^c)) % (2^32)) + ((x \div (2^(32 - c))) % (2^32))

Divide(x, y) == x \div y

(* Generisanje generičkih nizova K i S *)
GenK(n) == [i \in 0..(n-1) |-> (i * 123456789) % 987654321]
GenS(n) == [i \in 0..(n-1) |-> (i % 4) * 5 + 7]

(* Preprocesiranje poruke *)
Preprocess ==
  LET msg == Append(Message, 0)
  IN /\ Len(msg) % 512 = 448
     /\ Message' = Append(msg, Len(Message) % (2^64))

(* Obrada svake deonice poruke *)
ProcessChunk(chunk) ==
  LET P == [j \in 0..15 |-> SubSeq(Message, (chunk-1)*512 + j*32 + 1, (chunk-1)*512 + (j+1)*32)]
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

(* Finalni hash *)
FinalHash ==
  /\ digest' = <<A, B, C, D>>
  /\ UNCHANGED <<A, B, C, D, AA, BB, CC, DD, Message, M, K, S>>

(* Inicijalno stanje *)
Init ==
  /\ A \in 0..18
  /\ B \in 0..18
  /\ C \in 0..18
  /\ D \in 0..18
  /\ K = GenK(18)
  /\ S = GenS(18)
  /\ AA = A
  /\ BB = B
  /\ CC = C
  /\ DD = D
  /\ Message = <<>>
  /\ M = <<>>
  /\ digest = <<>>

(* Sledeće stanje sistema *)
Next ==
  \/ Preprocess
  \/ \E chunk \in 1..Divide(Len(Message), 512) : ProcessChunk(chunk)
  \/ FinalHash

(* Specifikacija *)
Spec == Init /\ [][Next]_<<A, B, C, D, AA, BB, CC, DD, Message, M, digest>>

============================ END MODULE ============================
