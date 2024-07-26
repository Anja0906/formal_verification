------------------------------ MODULE dsa ------------------------------
EXTENDS Integers, Sequences, FiniteSets

VARIABLES p, q, g, k, r, x, y, s, w, u1, u2, v, hashM, signature, verified

(* Definicija prostih brojeva u ograničenom opsegu *)
Prime == {a \in 2..18 : \A b \in 2..(a-1) : a % b /= 0}

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

(* Definicija proširenog Euklidovog algoritma za izračunavanje GCD i koeficijenata *)
RECURSIVE GCDWithCoef(_ , _, _, _, _, _)
GCDWithCoef(a, b, x0, x1, y0, y1) == 
  IF b = 0 THEN <<a, x0, y0>>
  ELSE 
    GCDWithCoef(b, a % b, x1, x0 - (a \div b) * x1, y1, y0 - (a \div b) * y1)

(* Inverzni moduo *)
InverseMod(a, m) ==
  IF GCDWithCoef(a, m, 1, 0, 0, 1)[2] < 0 THEN 
    GCDWithCoef(a, m, 1, 0, 0, 1)[2] + m 
  ELSE 
    GCDWithCoef(a, m, 1, 0, 0, 1)[2]

(* Generisanje ključeva *)
GenerateKeys ==
  /\ y' = ModExp(g, x, p)
  /\ UNCHANGED <<p, q, g, x, k, r, s, w, u1, u2, v, hashM, signature, verified>>

(* Potpisivanje *)
Sign ==
  /\ k' = k
  /\ r' = (ModExp(g, k', p) % q)
  /\ hashM' = hashM
  /\ s' = (InverseMod(k', q) * (hashM' + x * r')) % q
  /\ signature' = <<r', s'>>
  /\ UNCHANGED <<p, q, g, x, y, k, w, u1, u2, v, verified>>

(* Verifikacija *)
Verify ==
  /\ w' = InverseMod(s, q)
  /\ u1' = (hashM * w') % q
  /\ u2' = (r * w') % q
  /\ v' = ((ModExp(g, u1', p) * ModExp(y, u2', p)) % p) % q
  /\ verified' = (v' = r)
  /\ UNCHANGED <<p, q, g, x, y, k, r, s, hashM, signature>>

(* Inicijalno stanje *)
Init ==
  /\ p \in Prime
  /\ q \in Prime
  /\ p /= q
  /\ g \in 2..(p-1)
  /\ x \in 1..(q-1)
  /\ k \in 1..(q-1)
  /\ hashM \in 1..(q-1)
  /\ y = ModExp(g, x, p)
  /\ r = (ModExp(g, k, p) % q)
  /\ s = (InverseMod(k, q) * (hashM + x * r)) % q
  /\ signature = <<r, s>>
  /\ w = InverseMod(s, q)
  /\ u1 = (hashM * w) % q
  /\ u2 = (r * w) % q
  /\ v = ((ModExp(g, u1, p) * ModExp(y, u2, p)) % p) % q
  /\ verified = (v = r)

(* Sledeće stanje sistema *)
Next ==
  \/ GenerateKeys
  \/ Sign
  \/ Verify

(* Specifikacija *)
Spec == Init /\ [][Next]_<<p, q, g, x, y, k, r, s, w, u1, u2, v, hashM, signature, verified>>

============================ END MODULE ============================
