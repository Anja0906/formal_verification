--------------------------- MODULE rsa ---------------------------
EXTENDS Integers, Sequences, FiniteSets

VARIABLES p, q, n, phi, e, d, m, c, message, ciphertext, plaintext

Prime == {x \in 60..100 : \A y \in 2..(x-1) : x % y /= 0}

ChoosePrime == CHOOSE x \in Prime : TRUE

RECURSIVE ModExp(_ , _, _)
ModExp(base, exp, mod) == 
  IF exp = 0 THEN 1
  ELSE 
    IF exp % 2 = 0 THEN
      LET half_exp == ModExp(base, exp \div 2, mod) IN
      (half_exp * half_exp) % mod
    ELSE
      (base * ModExp(base, exp - 1, mod)) % mod

RECURSIVE ExtendedGCD(_, _, _, _, _, _)
ExtendedGCD(a, b, x0, y0, x1, y1) == 
  IF b = 0 THEN <<a, x0, y0>>
  ELSE 
    LET q_ == a \div b
        r_ == a % b
    IN ExtendedGCD(b, r_, x1, y1, x0 - q_ * x1, y0 - q_ * y1)

InverseMod(a, m_) ==
  LET gcdResult == ExtendedGCD(a, m_, 1, 0, 0, 1)
      gcd == gcdResult[1]
      x_ == gcdResult[2]
  IN IF gcd = 1 THEN (x_ + m_) % m_ ELSE 0

GenerateKeys ==
    /\ d' = InverseMod(e, phi)
    /\ UNCHANGED <<p, q, n, phi, e, m, c, plaintext, ciphertext, message>>


Encrypt ==
    /\ c' = ModExp(m, e, n)
    /\ UNCHANGED <<p, q, n, phi, e, d, m, plaintext, ciphertext, message>>

Decrypt ==
    /\ plaintext' = ModExp(c, d, n)
    /\ UNCHANGED <<p, q, n, phi, e, d, m, c, ciphertext, message>>

Output ==
    /\ ciphertext' = c
    /\ message' = plaintext
    /\ UNCHANGED <<p, q, n, phi, e, d, m, c, plaintext>>

Next ==
    \/ GenerateKeys
    \/ Encrypt
    \/ Decrypt
    \/ Output

Init ==
    /\ p = ChoosePrime
    /\ q = CHOOSE x \in Prime : x /= p
    /\ n = p * q
    /\ phi = (p - 1) * (q - 1)
    /\ e = 65537
    /\ ExtendedGCD(e, phi, 1, 0, 0, 1)[1] = 1
    /\ d = InverseMod(e, phi)
    /\ m \in 1..(n-1)
    /\ c = ModExp(m, e, n)
    /\ plaintext = ModExp(c, d, n)
    /\ ciphertext = c
    /\ message = plaintext

Spec ==
  Init /\ [][Next]_<<p, q, n, phi, e, d, m, c, plaintext, ciphertext, message>>

============================ END MODULE ============================
