------------------------------ MODULE dsa ------------------------------
EXTENDS Integers, Sequences, FiniteSets

VARIABLES p, q, g, k, r, x, y, s, w, u1, u2, v, hashM, signature, verified

Prime == {a \in 70..100 : \A b \in 2..(a-1) : a % b /= 0}

ModExpHelper(base, half_exp, mod, half_result) ==
  (half_result * half_result) % mod

RECURSIVE ModExp(_ , _, _)
ModExp(base, exp, mod) == 
  IF exp = 0 THEN 1
  ELSE 
    IF exp % 2 = 0 THEN
      ModExpHelper(base, exp \div 2, mod, ModExp(base, exp \div 2, mod))
    ELSE
      (base * ModExp(base, exp - 1, mod)) % mod

RECURSIVE GCDWithCoef(_ , _, _, _, _, _)
GCDWithCoef(a, b, x0, x1, y0, y1) == 
  IF b = 0 THEN <<a, x0, y0>>
  ELSE 
    GCDWithCoef(b, a % b, x1, x0 - (a \div b) * x1, y1, y0 - (a \div b) * y1)

InverseMod(a, m) ==
  IF GCDWithCoef(a, m, 1, 0, 0, 1)[2] < 0 THEN 
    GCDWithCoef(a, m, 1, 0, 0, 1)[2] + m 
  ELSE 
    GCDWithCoef(a, m, 1, 0, 0, 1)[2]

GenerateKeys ==
  /\ y' = ModExp(g, x, p)
  /\ UNCHANGED <<p, q, g, x, k, r, s, w, u1, u2, v, hashM, signature, verified>>

Sign ==
  /\ k' = k
  /\ r' = (ModExp(g, k', p) % q)
  /\ hashM' = hashM
  /\ s' = (InverseMod(k', q) * (hashM' + x * r')) % q
  /\ signature' = <<r', s'>>
  /\ UNCHANGED <<p, q, g, x, y, k, w, u1, u2, v, verified>>

Verify ==
  /\ w' = InverseMod(s, q)
  /\ u1' = (hashM * w') % q
  /\ u2' = (r * w') % q
  /\ v' = ((ModExp(g, u1', p) * ModExp(y, u2', p)) % p) % q
  /\ verified' = (v' = r)
  /\ UNCHANGED <<p, q, g, x, y, k, r, s, hashM, signature>>

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

Next ==
  \/ GenerateKeys
  \/ Sign
  \/ Verify

Spec == Init /\ [][Next]_<<p, q, g, x, y, k, r, s, w, u1, u2, v, hashM, signature, verified>>

============================ END MODULE ============================
