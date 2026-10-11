import ICO.ProtocolControl

namespace ICO.SequentialIsometry
open Matrix QIT
open scoped BigOperators
noncomputable section
universe u
set_option maxHeartbeats 2000000
variable {A M O : Type u} [Fintype A] [DecidableEq A]
  [Fintype M] [DecidableEq M] [Fintype O] [DecidableEq O]

/-- Public memory after each subsequent known operation. It stays constant
past the last query, which permits a total Nat-indexed physical recurrence. -/
def Protocol.tailMemory {q : ℕ} (p : Protocol A (A×M) O q) (t : ℕ) : Type u := by
  induction t generalizing q M with
  | zero => exact M
  | succ t ih =>
    cases p with
    | stop post hpost => exact M
    | query pre hpre after => exact ih after

instance Protocol.tailMemoryFinite {q : ℕ} (p : Protocol A (A×M) O q) (t : ℕ) :
    Fintype (p.tailMemory t) := by
  induction t generalizing q M with
  | zero => exact inferInstanceAs (Fintype M)
  | succ t ih =>
    cases p with
    | stop post hpost => exact inferInstanceAs (Fintype M)
    | query pre hpre after => exact ih after

instance Protocol.tailMemoryDecide {q : ℕ} (p : Protocol A (A×M) O q) (t : ℕ) :
    DecidableEq (p.tailMemory t) := by
  induction t generalizing q M with
  | zero => exact inferInstanceAs (DecidableEq M)
  | succ t ih =>
    cases p with
    | stop post hpost => exact inferInstanceAs (DecidableEq M)
    | query pre hpre after => exact ih after

/-- The next preprocessing isometry acts only on the accessible query and
public-memory registers. Once queries are exhausted it is the identity. -/
def Protocol.tailKnown {q : ℕ} (p : Protocol A (A×M) O q) (t : ℕ) :
    Matrix (A×p.tailMemory (t+1)) (A×p.tailMemory t) ℂ := by
  induction t generalizing q M with
  | zero =>
    cases p with
    | stop post hpost => exact (1 : CMatrix (A×M))
    | query pre hpre after => exact pre
  | succ t ih =>
    cases p with
    | stop post hpost => exact (1 : CMatrix (A×M))
    | query pre hpre after => exact ih after

theorem Protocol.tailKnown_isometry {q : ℕ} (p : Protocol A (A×M) O q) (t : ℕ) :
    (p.tailKnown t).conjTranspose*p.tailKnown t=1 := by
  induction t generalizing q M with
  | zero =>
    cases p with
    | stop post hpost =>
      change (1 : CMatrix (A×M)).conjTranspose * (1 : CMatrix (A×M)) = (1 : CMatrix (A×M))
      simp
    | query pre hpre after => exact hpre
  | succ t ih =>
    cases p with
    | stop post hpost =>
      change (1 : CMatrix (A×M)).conjTranspose * (1 : CMatrix (A×M)) = (1 : CMatrix (A×M))
      simp
    | query pre hpre after => exact ih after

variable {B : Type u} [Fintype B] [DecidableEq B]

def Protocol.finalEnvironment {q : ℕ} (p : Protocol A B O q) : Type u := by
  induction p with
  | @stop B O E _ _ _ _ _ _ post hpost => exact E
  | query pre hpre after ih => exact ih

instance Protocol.finalEnvironmentFinite {q : ℕ} (p : Protocol A B O q) :
    Fintype p.finalEnvironment := by
  induction p with
  | @stop B O E _ _ _ _ _ _ post hpost => exact inferInstanceAs (Fintype E)
  | query pre hpre after ih => exact ih

instance Protocol.finalEnvironmentDecide {q : ℕ} (p : Protocol A B O q) :
    DecidableEq p.finalEnvironment := by
  induction p with
  | @stop B O E _ _ _ _ _ _ post hpost => exact inferInstanceAs (DecidableEq E)
  | query pre hpre after ih => exact ih

def Protocol.tailFinal {q : ℕ} (p : Protocol A (A×M) O q) :
    Matrix (O×p.finalEnvironment) (A×p.tailMemory (q+1)) ℂ := by
  induction q generalizing M with
  | zero =>
    cases p with
    | stop post hpost => exact post
  | succ q ih =>
    cases p with
    | query pre hpre after => exact ih after

theorem Protocol.tailFinal_isometry {q : ℕ} (p : Protocol A (A×M) O q) :
    p.tailFinal.conjTranspose*p.tailFinal=1 := by
  induction q generalizing M with
  | zero =>
    cases p with
    | stop post hpost => exact hpost
  | succ q ih =>
    cases p with
    | query pre hpre after => exact ih after

/-- Actual density evolution for one current query followed by the remaining
queries of p. Public known operations act after each query, including an
identity operation after the last one. -/
def Protocol.tailEvolution {q : ℕ} (p : Protocol A (A×M) O q)
    {I : Type u} [Fintype I] (U : I → CMatrix A) (X : CMatrix (A×M)) :
    (t : ℕ) → CMatrix (A×p.tailMemory t)
  | 0 => X
  | t+1 => p.tailKnown t * ICO.AllChannelDilation.oracleMap U (p.tailEvolution U X t) *
      (p.tailKnown t).conjTranspose

variable {N I : Type u} [Fintype N] [DecidableEq N] [Fintype I] [DecidableEq I]

theorem Protocol.tailEvolution_query_succ {q : ℕ}
    (pre : Matrix (A×N) (A×M) ℂ) (hpre : pre.conjTranspose*pre=1)
    (after : Protocol A (A×N) O q) (U : I → CMatrix A) (X : CMatrix (A×M)) (t : ℕ) :
    (Protocol.query pre hpre after).tailEvolution U X (t+1) =
      after.tailEvolution U (pre * ICO.AllChannelDilation.oracleMap U X * pre.conjTranspose) t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    change after.tailKnown t * ICO.AllChannelDilation.oracleMap (M := after.tailMemory t) U
      ((Protocol.query pre hpre after).tailEvolution U X (t+1)) * (after.tailKnown t).conjTranspose = _
    rw [ih]
    rfl

theorem Protocol.tailEvolution_output {q : ℕ} (p : Protocol A (A×M) O q)
    (U : I → CMatrix A) (X : CMatrix (A×M)) :
    MatrixMap.ofKraus (erasedKraus p.tailFinal) (p.tailEvolution U X (q+1)) =
      p.map U (ICO.AllChannelDilation.oracleMap U X) := by
  induction q generalizing M with
  | zero =>
    cases p with
    | stop post hpost =>
      change MatrixMap.ofKraus (erasedKraus post)
        ((1 : CMatrix (A×M)) * ICO.AllChannelDilation.oracleMap U X * (1 : CMatrix (A×M)).conjTranspose) = _
      simp only [Matrix.conjTranspose_one,Matrix.one_mul,Matrix.mul_one]
      rfl
  | succ q ih =>
    cases p with
    | query pre hpre after =>
      rw [Protocol.tailEvolution_query_succ]
      change MatrixMap.ofKraus (erasedKraus after.tailFinal)
        (after.tailEvolution U (pre * ICO.AllChannelDilation.oracleMap U X * pre.conjTranspose) (q+1)) = _
      rw [ih]
      change after.map U (ICO.AllChannelDilation.oracleMap U
        (pre * ICO.AllChannelDilation.oracleMap U X * pre.conjTranspose)) =
        after.map U (ICO.AllChannelDilation.oracleMap U (singleMap pre (ICO.AllChannelDilation.oracleMap U X)))
      rw [singleMap_apply]

#print axioms Protocol.tailEvolution_output
#print axioms Protocol.tailFinal_isometry
#print axioms Protocol.tailKnown_isometry
end
end ICO.SequentialIsometry
