-- Decidable propositions and if-then-else -------------------------------------

-- Decision procedure for whether the proposition p holds
interface Decision p where
  decide: Dec p

-- If then else
ifthenelse: Decision p => a -> a -> a
ifthenelse {p} ifYes ifNo with (decide {p = p})
  ifthenelse ifYes ifNo | (Yes _) = ifYes
  ifthenelse ifYes ifNo | (No _) = ifNo

-- Decidable less than or equal ------------------------------------------------

-- A lemma
sucNotLteZero: S n `LTE` Z -> Void
sucNotLteZero LTEZero impossible
sucNotLteZero (LTESucc _) impossible

-- A lemma
sucLte: S m `LTE` S n -> m `LTE` n
sucLte (LTESucc mLteN) = mLteN

-- LTE is decidable
decLte: Dec (m `LTE` n)
decLte {m} {n} = isLTE m n

-- Decision for LTE
Decision (m `LTE` n) where
  decide = decLte

-- Can we use it? --------------------------------------------------------------

-- Testing
answer: Nat
answer = ifthenelse {p = 1 `LTE` 3} 1 0

-- Testing 1 2
answer2: Nat -> Nat -> Nat
answer2 m n = ifthenelse {p = m `LTE` n} 1 0

-- Alternative: use booleans instead of Dec ------------------------------------
-- (should be more efficient if the compiler can't figure out how to throw -----
-- away proof arguments to Dec when not used) ----------------------------------

interface DecisionX p where
  decideX: Bool
  decideImplP: decideX = True -> p
  pImplDecide: p -> decideX = True
  
ifthenelseX: DecisionX p => a -> a -> a
ifthenelseX {p} ifYes ifNo with (decideX {p = p})
  ifthenelseX ifYes ifNo | True = ifYes
  ifthenelseX ifYes ifNo | False = ifNo

implLte: m `lte` n = True -> m `LTE` n
implLte {m = Z} _ = LTEZero
implLte {m = S _} {n = Z} Refl impossible
implLte {m = S k} {n = S j} b = implLte b

lteImpl: m `LTE` n -> m `lte` n = True
lteImpl {m = Z} _ = Refl
lteImpl {m = S _} {n = Z} LTEZero impossible
lteImpl {m = S _} {n = Z} (LTESucc _) impossible
lteImpl {m = S k} {n = S j} r = lteImpl r

DecisionX (m `LTE` n) where
  decideX {m} {n} = m `lte` n
  decideImplP = implLte
  pImplDecide = lteImpl
  
answerX: Nat
answerX = ifthenelseX {p = 1 `LTE` 3} 1 0

answer2X: Nat -> Nat -> Nat
answer2X m n = ifthenelseX {p = m `LTE` n} 1 0
