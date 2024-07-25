--------------------------- MODULE rsa ---------------------------
EXTENDS Integers, Sequences, FiniteSets

VARIABLES p, q, n, phi, e, d, m, c, message, ciphertext, plaintext

(* Definicija prostih brojeva u ograničenom opsegu *)
Prime == {x \in 2..10000 : \A y \in 2..(x-1) : x % y /= 0}

(* Definicija pomoćne funkcije za modularnu eksponencijaciju *)
ModExpHelper(base, half_exp, mod, half_result) ==
  (half_result * half_result) % mod

(* Definicija rekurzivne funkcije za modularnu eksponencijaciju *)
RECURSIVE ModExp(_ , _, _)
ModExp(base, exp, mod) == 
  IF exp = 0 THEN 1
  ELSE 
    IF exp % 2 = 0 THEN
      ModExpHelper(base, exp \div 2, mod, ModExp(base, exp \div 2, mod))
    ELSE
      (base * ModExp(base, exp - 1, mod)) % mod

(* Generisanje ključeva *)
GenerateKeys ==
  /\ d' = CHOOSE x \in 1..(phi-1) : (e * x) % phi = 1
  /\ UNCHANGED <<p, q, n, phi, e, m, c, plaintext, ciphertext, message>>

(* Enkripcija *)
Encrypt ==
  /\ c' = ModExp(m, e, n)
  /\ UNCHANGED <<p, q, n, phi, e, d, m, plaintext, ciphertext, message>>

(* Dekripcija *)
Decrypt ==
  /\ plaintext' = ModExp(c, d, n)
  /\ UNCHANGED <<p, q, n, phi, e, d, m, c, ciphertext, message>>

(* Izlaz *)
Output ==
  /\ ciphertext' = c
  /\ message' = plaintext
  /\ UNCHANGED <<p, q, n, phi, e, d, m, c, plaintext>>

(* Sledeće stanje sistema *)
Next ==
  \/ GenerateKeys
  \/ Encrypt
  \/ Decrypt
  \/ Output

(* Inicijalno stanje *)
Init ==
  /\ p = 3
  /\ q = 11
  /\ p /= q
  /\ n = p * q
  /\ phi = (p - 1) * (q - 1)
  /\ e = 7
  /\ m = 5
  /\ d = CHOOSE x \in 1..(phi-1) : (e * x) % phi = 1
  /\ c = ModExp(m, e, n)
  /\ plaintext = ModExp(c, d, n)
  /\ ciphertext = c
  /\ message = plaintext

(* Specifikacija *)
Spec ==
  Init /\ [][Next]_<<p, q, n, phi, e, d, m, c, plaintext, ciphertext, message>>

============================ END MODULE ============================
