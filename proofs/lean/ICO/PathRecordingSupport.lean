import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Powerset
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Tactic

/-!
# Finite-relation support facts for a dephased recording wrapper

This module proves support invariants, defines the normalized right-insertion
matrix, and proves column orthonormality on its admissible domain. Dephasing
its output Gram matrix and compressing to bounded records gives the PSD and
Euclidean operator-norm bound `1/(d-m)`. The physical operator-to-support
embedding, partial-trace identities, and the Ma--Huang theorem remain separate.

Relations on this support have unique first coordinates and hence no repeated
edges, so a finite set is an appropriate representation of these basis labels.
-/

namespace ICO.PathRecordingSupport

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

abbrev Relation (α β : Type*) := Finset (α × β)

/-- Every first coordinate has at most one second coordinate. -/
def LeftUnique (s : Relation α β) : Prop :=
  ∀ ⦃x : α⦄ ⦃y z : β⦄, (x, y) ∈ s → (x, z) ∈ s → y = z

/-- Every second coordinate has at most one first coordinate. -/
def RightUnique (s : Relation α β) : Prop :=
  ∀ ⦃x z : α⦄ ⦃y : β⦄, (x, y) ∈ s → (z, y) ∈ s → x = z

def FreshLeft (x : α) (s : Relation α β) : Prop := ∀ y, (x, y) ∉ s

def FreshRight (y : β) (s : Relation α β) : Prop := ∀ x, (x, y) ∉ s

omit [DecidableEq α] [DecidableEq β] in
theorem leftUnique_empty : LeftUnique (∅ : Relation α β) := by
  simp [LeftUnique]

omit [DecidableEq α] [DecidableEq β] in
theorem rightUnique_empty : RightUnique (∅ : Relation α β) := by
  simp [RightUnique]

omit [DecidableEq α] [DecidableEq β] in
theorem leftUnique_mono {s t : Relation α β} (h : s ⊆ t)
    (ht : LeftUnique t) : LeftUnique s := by
  intro x y z hxy hxz
  exact ht (h hxy) (h hxz)

omit [DecidableEq α] [DecidableEq β] in
theorem rightUnique_mono {s t : Relation α β} (h : s ⊆ t)
    (ht : RightUnique t) : RightUnique s := by
  intro x z y hxy hzy
  exact ht (h hxy) (h hzy)

theorem leftUnique_erase {s : Relation α β} (h : LeftUnique s) (e : α × β) :
    LeftUnique (s.erase e) := leftUnique_mono (Finset.erase_subset _ _) h

theorem rightUnique_erase {s : Relation α β} (h : RightUnique s) (e : α × β) :
    RightUnique (s.erase e) := rightUnique_mono (Finset.erase_subset _ _) h

/-- Freshness is sufficient to preserve uniqueness on insertion. -/
theorem leftUnique_insert {s : Relation α β} {a : α} {b : β}
    (h : LeftUnique s) (hf : FreshLeft a s) : LeftUnique (insert (a, b) s) := by
  intro x y z hxy hxz
  rcases Finset.mem_insert.mp hxy with he1 | ho1
  · rcases Prod.mk.inj he1 with ⟨rfl, rfl⟩
    rcases Finset.mem_insert.mp hxz with he2 | ho2
    · exact (Prod.mk.inj he2).2.symm
    · exact (hf z ho2).elim
  · rcases Finset.mem_insert.mp hxz with he2 | ho2
    · rcases Prod.mk.inj he2 with ⟨rfl, rfl⟩
      exact (hf y ho1).elim
    · exact h ho1 ho2

theorem rightUnique_insert {s : Relation α β} {a : α} {b : β}
    (h : RightUnique s) (hf : FreshRight b s) : RightUnique (insert (a, b) s) := by
  intro x z y hxy hzy
  rcases Finset.mem_insert.mp hxy with he1 | ho1
  · rcases Prod.mk.inj he1 with ⟨rfl, rfl⟩
    rcases Finset.mem_insert.mp hzy with he2 | ho2
    · exact (Prod.mk.inj he2).1.symm
    · exact (hf z ho2).elim
  · rcases Finset.mem_insert.mp hzy with he2 | ho2
    · rcases Prod.mk.inj he2 with ⟨rfl, rfl⟩
      exact (hf x ho1).elim
    · exact h ho1 ho2

/-- Removing the unique edge with a given first coordinate makes it fresh. -/
theorem freshLeft_erase {s : Relation α β} {x : α} {y : β}
    (h : LeftUnique s) (he : (x, y) ∈ s) : FreshLeft x (s.erase (x, y)) := by
  intro z hz
  have hzy : z = y := h (Finset.mem_of_mem_erase hz) he
  subst z
  exact Finset.notMem_erase _ _ hz

theorem freshRight_erase {s : Relation α β} {x : α} {y : β}
    (h : RightUnique s) (he : (x, y) ∈ s) : FreshRight y (s.erase (x, y)) := by
  intro z hz
  have hzx : z = x := h (Finset.mem_of_mem_erase hz) he
  subst z
  exact Finset.notMem_erase _ _ hz

/-- A left-edge replacement keeps the first coordinate but takes a fresh
    second coordinate, preserving both uniqueness properties. -/
theorem left_replacement_preserves {s : Relation α β} {a : α} {b c : β}
    (hl : LeftUnique s) (hr : RightUnique s) (he : (a, b) ∈ s)
    (hf : FreshRight c (s.erase (a, b))) :
    LeftUnique (insert (a, c) (s.erase (a, b))) ∧
      RightUnique (insert (a, c) (s.erase (a, b))) := by
  exact ⟨leftUnique_insert (leftUnique_erase hl _) (freshLeft_erase hl he),
    rightUnique_insert (rightUnique_erase hr _) hf⟩

/-- The newly inserted edge is determined by its fresh first coordinate.
    This is the exact finite-label equality underlying the claimed elimination
    of discarded-record coherences after dephasing the query coordinate. -/
theorem fresh_insert_injective {s t : Relation α β} {x : α} {y z : β}
    (hs : FreshLeft x s) (ht : FreshLeft x t)
    (heq : insert (x, y) s = insert (x, z) t) : y = z ∧ s = t := by
  have hy : (x, y) ∈ insert (x, z) t := by
    rw [← heq]
    exact Finset.mem_insert_self _ _
  have hyz : y = z := by
    rcases Finset.mem_insert.mp hy with hy | hy
    · exact (Prod.mk.inj hy).2
    · exact (ht y hy).elim
  subst z
  have herase := congrArg (fun u : Relation α β => u.erase (x, y)) heq
  dsimp only at herase
  rw [Finset.erase_insert (hs y), Finset.erase_insert (ht y)] at herase
  exact ⟨rfl, herase⟩

/-- Two recording indices with the same dephased query and final private
    registers agree on all indices that can affect the visible output. -/
theorem same_final_records {s t r r' : Relation α β} {x : α} {y z : β}
    (hs : FreshLeft x s) (ht : FreshLeft x t) (hr : r = r')
    (heq : (insert (x, y) s, r) = (insert (x, z) t, r')) :
    y = z ∧ s = t ∧ r = r' := by
  obtain ⟨hy, hst⟩ := fresh_insert_injective hs ht (Prod.mk.inj heq).1
  exact ⟨hy, hst, hr⟩

theorem card_replace_le {s : Relation α β} {a b : α × β} (ha : a ∈ s) :
    (insert b (s.erase a)).card ≤ s.card := by
  have h := Finset.card_insert_le b (s.erase a)
  have hpos : 0 < s.card := Finset.card_pos.mpr ⟨a, ha⟩
  rw [Finset.card_erase_of_mem ha] at h
  omega

/-- The support invariant used between wrappers. -/
def Good (l r : Relation α β) : Prop := LeftUnique l ∧ RightUnique l ∧ LeftUnique r

omit [DecidableEq α] [DecidableEq β] in
theorem good_empty : Good (∅ : Relation α β) ∅ :=
  ⟨leftUnique_empty, rightUnique_empty, leftUnique_empty⟩

/-- Abstract recording-basis branches corresponding to the four terms in the
    inverse-wrapper expansion. Admissibility may impose additional conditions;
    only the freshness needed for the support invariant is encoded here. This
    inductive relation is not itself a definition of a quantum operator. -/
inductive InverseBranch (l r : Relation α β) : Relation α β → Relation α β → α → Prop
  | removeLeft {x : α} {y : β} (he : (x, y) ∈ l) :
      InverseBranch l r (l.erase (x, y)) r x
  | removeLeftMoveRight {a c x : α} {b z : β}
      (hl : (a, b) ∈ l) (hr : (c, z) ∈ r)
      (hfl : FreshLeft x (l.erase (a, b)))
      (hfr : FreshLeft x (r.erase (c, z))) :
      InverseBranch l r (l.erase (a, b)) (insert (x, z) (r.erase (c, z))) x
  | insertRight {x : α} {y : β} (hfl : FreshLeft x l) (hfr : FreshLeft x r) :
      InverseBranch l r l (insert (x, y) r) x
  | moveLeftInsertRight {a x : α} {b c y : β}
      (he : (a, b) ∈ l) (hf : FreshRight c (l.erase (a, b)))
      (hfl : FreshLeft x (insert (a, c) (l.erase (a, b)))) (hfr : FreshLeft x r) :
      InverseBranch l r (insert (a, c) (l.erase (a, b))) (insert (x, y) r) x

theorem inverse_branch_preserves {l r l' r' : Relation α β} {x : α}
    (hg : Good l r) (hb : InverseBranch l r l' r' x) :
    Good l' r' ∧ FreshLeft x l' ∧ l'.card + r'.card ≤ l.card + r.card + 1 := by
  obtain ⟨hll, hlr, hrl⟩ := hg
  cases hb with
  | @removeLeft x y he =>
      refine ⟨⟨leftUnique_erase hll _, rightUnique_erase hlr _, hrl⟩,
        freshLeft_erase hll he, ?_⟩
      have h := Finset.card_le_card (Finset.erase_subset (x, y) l)
      omega
  | @removeLeftMoveRight a c x b z hl hr hfl hfr =>
      refine ⟨⟨leftUnique_erase hll _, rightUnique_erase hlr _,
        leftUnique_insert (leftUnique_erase hrl _) hfr⟩, hfl, ?_⟩
      have h1 := Finset.card_le_card (Finset.erase_subset (a, b) l)
      have h2 := card_replace_le (b := (x, z)) hr
      omega
  | @insertRight x y hfl hfr =>
      refine ⟨⟨hll, hlr, leftUnique_insert hrl hfr⟩, hfl, ?_⟩
      have h := Finset.card_insert_le (x, y) r
      omega
  | @moveLeftInsertRight a x b c y he hf hfl hfr =>
      obtain ⟨h1, h2⟩ := left_replacement_preserves hll hlr he hf
      refine ⟨⟨h1, h2, leftUnique_insert hrl hfr⟩, hfl, ?_⟩
      have hc1 := card_replace_le (b := (a, c)) he
      have hc2 := Finset.card_insert_le (x, y) r
      omega

/-- The final growing-only insertion restores a good completed wrapper and
    increases total record size by at most two. -/
theorem completed_wrapper_preserves {l r l' r' : Relation α β} {x : α} {y : β}
    (hg : Good l r) (hb : InverseBranch l r l' r' x)
    (hf : FreshRight y l') :
    Good (insert (x, y) l') r' ∧
      (insert (x, y) l').card + r'.card ≤ l.card + r.card + 2 := by
  obtain ⟨⟨hl, hr, hrl⟩, hx, hcard⟩ := inverse_branch_preserves hg hb
  refine ⟨⟨leftUnique_insert hl hx, rightUnique_insert hr hf, hrl⟩, ?_⟩
  have h := Finset.card_insert_le (x, y) l'
  omega

/-- A sequence of completed abstract recording wrappers, starting from empty
    private records. No amplitudes or quantum states are included. -/
inductive WrapperRun : ℕ → Relation α β → Relation α β → Prop
  | empty : WrapperRun 0 ∅ ∅
  | step {t : ℕ} {l r l' r' : Relation α β} {x : α} {y : β}
      (past : WrapperRun t l r) (branch : InverseBranch l r l' r' x)
      (fresh : FreshRight y l') :
      WrapperRun (t + 1) (insert (x, y) l') r'

theorem wrapper_run_invariant {t : ℕ} {l r : Relation α β}
    (h : WrapperRun t l r) : Good l r ∧ l.card + r.card ≤ 2 * t := by
  induction h with
  | empty => exact ⟨good_empty, by simp⟩
  | step past branch fresh ih =>
      obtain ⟨hg, hcard⟩ := completed_wrapper_preserves ih.1 branch fresh
      refine ⟨hg, ?_⟩
      omega

/-- At the intermediate point after the inverse half of wrapper `t+1`, the
    query coordinate is absent from the left record and at most `2t+1` edges
    are present. -/
theorem intermediate_run_invariant {t : ℕ} {l r l' r' : Relation α β} {x : α}
    (h : WrapperRun t l r) (hb : InverseBranch l r l' r' x) :
    Good l' r' ∧ FreshLeft x l' ∧ l'.card + r'.card ≤ 2 * t + 1 := by
  obtain ⟨hg, hcard⟩ := wrapper_run_invariant h
  obtain ⟨hg', hf, hcard'⟩ := inverse_branch_preserves hg hb
  exact ⟨hg', hf, by omega⟩

section MatrixSupport

variable [Fintype α] [Fintype β]

/-- A finite insertion matrix records `(x,y)` and requires fresh `x`.
    The old left record can be treated as an additional fixed parameter. -/
def InsertionSupported
    (b : Matrix (α × Relation α β) (β × Relation α β) ℂ) : Prop :=
  ∀ x r y r₀, b (x, r) (y, r₀) ≠ 0 →
    FreshLeft x r₀ ∧ r = insert (x, y) r₀

omit [Fintype α] [Fintype β] in
/-- On the fresh-coordinate support, a row has at most one nonzero
    predecessor coefficient. -/
theorem insertion_row_unique
    {b : Matrix (α × Relation α β) (β × Relation α β) ℂ}
    (hb : InsertionSupported b) {x : α} {r : Relation α β}
    {c c' : β × Relation α β}
    (hc : b (x, r) c ≠ 0) (hc' : b (x, r) c' ≠ 0) : c = c' := by
  obtain ⟨hf, he⟩ := hb x r c.1 c.2 hc
  obtain ⟨hf', he'⟩ := hb x r c'.1 c'.2 hc'
  obtain ⟨hy, hr⟩ := fresh_insert_injective hf hf' (he.symm.trans he')
  exact Prod.ext hy hr

/-- After dephasing the query coordinate, the insertion Gram matrix has
    no off-diagonal entries between distinct final relation records. This is
    a matrix statement with an explicit support hypothesis. -/
theorem dephased_insertion_gram_offDiagonal
    {b : Matrix (α × Relation α β) (β × Relation α β) ℂ}
    (hb : InsertionSupported b) (x : α) {r s : Relation α β} (hrs : r ≠ s) :
    (b * b.conjTranspose) (x, r) (x, s) = 0 := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
  apply Finset.sum_eq_zero
  intro c _
  by_cases hc : b (x, r) c = 0
  · simp [hc]
  · have hz : b (x, s) c = 0 := by
      by_contra hn
      exact hrs ((hb x r c.1 c.2 hc).2.trans (hb x s c.1 c.2 hn).2.symm)
    simp [hz]

/-- If a predecessor is present, the diagonal Gram entry is exactly its
    coefficient times its complex conjugate, with no hidden sum over edges. -/
theorem insertion_gram_diagonal
    {b : Matrix (α × Relation α β) (β × Relation α β) ℂ}
    (hb : InsertionSupported b) (x : α) (r : Relation α β)
    (c : β × Relation α β) (hc : b (x, r) c ≠ 0) :
    (b * b.conjTranspose) (x, r) (x, r) =
      b (x, r) c * star (b (x, r) c) := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
  apply Finset.sum_eq_single c
  · intro c' _ hne
    have hz : b (x, r) c' = 0 := by
      by_contra hn
      exact hne (insertion_row_unique hb hn hc)
    simp [hz]
  · intro hnot
    exact (hnot (Finset.mem_univ c)).elim

/-- The set of occupied first coordinates of a relation. -/
def leftDomain (r : Relation α β) : Finset α := r.image Prod.fst

/-- The finite matrix of fresh right-record insertion, with the left record
    fixed. It uses the published normalization by the number of free first
    coordinates. Its Hilbert-space interpretation and isometry domain are not
    asserted by this definition. -/
noncomputable def rightInsertionMatrix (l : Relation α β) :
    Matrix (α × Relation α β) (β × Relation α β) ℂ := by
  classical
  exact fun o i =>
    if FreshLeft o.1 (l ∪ i.2) ∧ o.2 = insert (o.1, i.1) i.2 then
      (((Real.sqrt ((Fintype.card α : ℝ) - ((leftDomain (l ∪ i.2)).card : ℝ)))⁻¹ : ℝ) : ℂ)
    else 0

omit [Fintype β] in
/-- The concrete normalized insertion matrix satisfies the support condition
    required for the preceding Gram-matrix diagonalization. -/
theorem rightInsertionMatrix_supported (l : Relation α β) :
    InsertionSupported (rightInsertionMatrix l) := by
  classical
  intro x r y r₀ hn
  unfold rightInsertionMatrix at hn
  split_ifs at hn with h
  · refine ⟨?_, h.2⟩
    intro z hz
    exact h.1 z (Finset.mem_union_right l hz)
  · exact (hn rfl).elim

theorem rightInsertionMatrix_dephased_offDiagonal (l : Relation α β) (x : α)
    {r s : Relation α β} (hrs : r ≠ s) :
    (rightInsertionMatrix l * (rightInsertionMatrix l).conjTranspose) (x, r) (x, s) = 0 :=
  dephased_insertion_gram_offDiagonal (rightInsertionMatrix_supported l) x hrs

omit [Fintype β] in
theorem rightInsertionMatrix_row_unique (l : Relation α β) {x : α}
    {r : Relation α β} {c c' : β × Relation α β}
    (hc : rightInsertionMatrix l (x, r) c ≠ 0)
    (hc' : rightInsertionMatrix l (x, r) c' ≠ 0) : c = c' :=
  insertion_row_unique (rightInsertionMatrix_supported l) hc hc'

omit [DecidableEq β] [Fintype α] [Fintype β] in
theorem freshLeft_iff_not_mem_domain (x : α) (r : Relation α β) :
    FreshLeft x r ↔ x ∉ leftDomain r := by
  constructor
  · intro hf hm
    obtain ⟨⟨a, b⟩, he, ha⟩ := Finset.mem_image.mp hm
    change a = x at ha
    subst a
    exact hf b he
  · intro hx y hy
    exact hx (Finset.mem_image.mpr ⟨(x, y), hy, rfl⟩)

/-- Distinct input columns of the concrete insertion matrix are orthogonal. -/
theorem rightInsertionMatrix_column_orthogonal (l : Relation α β)
    {c c' : β × Relation α β} (hne : c ≠ c') :
    ((rightInsertionMatrix l).conjTranspose * rightInsertionMatrix l) c c' = 0 := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
  apply Finset.sum_eq_zero
  intro o _
  by_cases hc : rightInsertionMatrix l o c = 0
  · simp [hc]
  · have hz : rightInsertionMatrix l o c' = 0 := by
      by_contra hn
      exact hne (rightInsertionMatrix_row_unique l hc hn)
    simp [hz]

theorem rightInsertionMatrix_column_normSq (l : Relation α β) (y : β)
    (r₀ : Relation α β)
    (hfree : (leftDomain (l ∪ r₀)).card < Fintype.card α) :
    ∑ o, Complex.normSq (rightInsertionMatrix l o (y, r₀)) = 1 := by
  classical
  have hlt : ((leftDomain (l ∪ r₀)).card : ℝ) < Fintype.card α := by
    exact_mod_cast hfree
  have hd : (0 : ℝ) < (Fintype.card α : ℝ) - (leftDomain (l ∪ r₀)).card := by
    linarith
  have hfilter : Finset.univ.filter (fun x => FreshLeft x (l ∪ r₀)) =
      (leftDomain (l ∪ r₀))ᶜ := by
    ext x
    simp [freshLeft_iff_not_mem_domain]
  have hinner (x : α) :
      (∑ r, Complex.normSq (rightInsertionMatrix l (x, r) (y, r₀))) =
        if FreshLeft x (l ∪ r₀) then
          1 / ((Fintype.card α : ℝ) - (leftDomain (l ∪ r₀)).card) else 0 := by
    by_cases hx : FreshLeft x (l ∪ r₀)
    · simp [rightInsertionMatrix, hx, apply_ite,
        Complex.normSq_ofReal, Real.mul_self_sqrt hd.le]
    · simp [rightInsertionMatrix, hx]
  rw [Fintype.sum_prod_type]
  simp_rw [hinner]
  rw [Finset.sum_ite]
  simp only [hfilter, Finset.sum_const, nsmul_eq_mul, mul_zero, add_zero]
  rw [Finset.card_compl, Nat.cast_sub (Finset.card_le_univ _)]
  field_simp [ne_of_gt hd]

/-- Every admissible input basis column has Gram diagonal one. Together with
    `rightInsertionMatrix_column_orthogonal`, this certifies orthonormality of
    the insertion columns on the domain with at least one free first label. -/
theorem rightInsertionMatrix_column_gram_one (l : Relation α β) (y : β)
    (r₀ : Relation α β)
    (hfree : (leftDomain (l ∪ r₀)).card < Fintype.card α) :
    ((rightInsertionMatrix l).conjTranspose * rightInsertionMatrix l)
      (y, r₀) (y, r₀) = 1 := by
  have h := congrArg (fun a : ℝ => (a : ℂ))
    (rightInsertionMatrix_column_normSq l y r₀ hfree)
  simpa only [Complex.ofReal_sum, Complex.normSq_eq_conj_mul_self, Complex.ofReal_one,
    Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.star_def] using h

omit [DecidableEq β] [Fintype β] in
theorem fresh_domain_card_lt (x : α) (r : Relation α β) (hf : FreshLeft x r) :
    (leftDomain r).card < Fintype.card α :=
  Finset.card_lt_univ_of_notMem ((freshLeft_iff_not_mem_domain x r).mp hf)

omit [Fintype β] in
/-- The squared coefficient is the reciprocal number of free first labels. -/
theorem rightInsertionMatrix_coefficient_normSq (l r₀ : Relation α β) (x : α) (y : β)
    (hf : FreshLeft x (l ∪ r₀)) :
    Complex.normSq (rightInsertionMatrix l (x, insert (x, y) r₀) (y, r₀)) =
      1 / ((Fintype.card α : ℝ) - (leftDomain (l ∪ r₀)).card) := by
  have hlt := fresh_domain_card_lt x (l ∪ r₀) hf
  have hlt' : ((leftDomain (l ∪ r₀)).card : ℝ) < Fintype.card α := by
    exact_mod_cast hlt
  have hd : (0 : ℝ) ≤ (Fintype.card α : ℝ) - (leftDomain (l ∪ r₀)).card := by
    linarith
  simp [rightInsertionMatrix, hf, Complex.normSq_ofReal,
    Real.mul_self_sqrt hd]

omit [Fintype β] in
/-- A scalar coefficient bound with the same denominator as the suppressed
    removal estimate, once a bound on occupied first coordinates is supplied. -/
theorem rightInsertionMatrix_coefficient_bound (l r₀ : Relation α β) (x : α) (y : β)
    (hf : FreshLeft x (l ∪ r₀)) (m : ℕ)
    (hm : (leftDomain (l ∪ r₀)).card ≤ m) (hmd : m < Fintype.card α) :
    Complex.normSq (rightInsertionMatrix l (x, insert (x, y) r₀) (y, r₀)) ≤
      1 / ((Fintype.card α : ℝ) - (m : ℝ)) := by
  rw [rightInsertionMatrix_coefficient_normSq l r₀ x y hf]
  have hm' : ((leftDomain (l ∪ r₀)).card : ℝ) ≤ m := by exact_mod_cast hm
  have hmd' : (m : ℝ) < Fintype.card α := by exact_mod_cast hmd
  apply one_div_le_one_div_of_le
  · linarith
  · linarith

omit [Fintype α] [Fintype β] in
theorem domain_card_le_records (l r : Relation α β) :
    (leftDomain (l ∪ r)).card ≤ l.card + r.card := by
  exact le_trans (Finset.card_image_le) (Finset.card_union_le l r)

omit [Fintype β] in
theorem rightInsertionMatrix_nonzero_data (l r r₀ : Relation α β) (x : α) (y : β)
    (hn : rightInsertionMatrix l (x, r) (y, r₀) ≠ 0) :
    FreshLeft x (l ∪ r₀) ∧ r = insert (x, y) r₀ := by
  classical
  unfold rightInsertionMatrix at hn
  split_ifs at hn with h
  · exact h
  · exact (hn rfl).elim

/-- Every dephased Gram diagonal entry is at most the reciprocal of the
    remaining label count. Combined with off-diagonal vanishing, this is the
    entrywise form of the suppressed-removal projector estimate. The theorem
    still does not claim a Hilbert-space operator-norm comparison. -/
theorem rightInsertionMatrix_gram_diagonal_bound (l r : Relation α β) (x : α)
    (m : ℕ) (hsize : l.card + r.card ≤ m) (hmd : m < Fintype.card α) :
    ((rightInsertionMatrix l * (rightInsertionMatrix l).conjTranspose)
      (x, r) (x, r)).re ≤ 1 / ((Fintype.card α : ℝ) - (m : ℝ)) := by
  classical
  by_cases he : ∃ c, rightInsertionMatrix l (x, r) c ≠ 0
  · obtain ⟨⟨y, r₀⟩, hc⟩ := he
    obtain ⟨hf, hr⟩ := rightInsertionMatrix_nonzero_data l r r₀ x y hc
    have hcard : r₀.card ≤ r.card := by
      rw [hr]
      exact Finset.card_le_card (Finset.subset_insert _ _)
    have hdom : (leftDomain (l ∪ r₀)).card ≤ m := by
      have h := domain_card_le_records l r₀
      omega
    rw [insertion_gram_diagonal (rightInsertionMatrix_supported l) x r (y, r₀) hc]
    simp only [Complex.star_def, Complex.mul_conj, Complex.ofReal_re]
    rw [hr]
    exact rightInsertionMatrix_coefficient_bound l r₀ x y hf m hdom hmd
  · have hz (c : β × Relation α β) : rightInsertionMatrix l (x, r) c = 0 := by
      by_contra hn
      exact he ⟨c, hn⟩
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, hz, zero_mul,
      Finset.sum_const_zero, Complex.zero_re]
    have hd : (m : ℝ) < Fintype.card α := by exact_mod_cast hmd
    have hden : (0 : ℝ) < (Fintype.card α : ℝ) - (m : ℝ) := by linarith
    positivity

/-- Gram diagonal entries are real, with an explicit sum-of-squares expression. -/
theorem rightInsertionMatrix_gram_diagonal_real (l r : Relation α β) (x : α) :
    (rightInsertionMatrix l * (rightInsertionMatrix l).conjTranspose)
      (x, r) (x, r) =
      ((∑ c, Complex.normSq (rightInsertionMatrix l (x, r) c) : ℝ) : ℂ) := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.star_def,
    Complex.mul_conj, Complex.ofReal_sum]

/-- Records on which the occupied-label bound is available. -/
abbrev BoundedRecord (l : Relation α β) (m : ℕ) :=
  {r : Relation α β // l.card + r.card ≤ m}

/-- Dephase the query label in `BB†`, then compress to bounded records. The
    separate query index in this definition makes the dephasing explicit. -/
noncomputable def compressedDephasedGram (l : Relation α β) (m : ℕ) :
    Matrix (α × BoundedRecord l m) (α × BoundedRecord l m) ℂ :=
  fun u v => if u.1 = v.1 then
    (rightInsertionMatrix l * (rightInsertionMatrix l).conjTranspose)
      (u.1, u.2.val) (v.1, v.2.val) else 0

/-- Dephasing removes all coherence between different bounded basis records. -/
theorem compressedDephasedGram_eq_diagonal (l : Relation α β) (m : ℕ) :
    compressedDephasedGram l m = Matrix.diagonal (fun u =>
      (rightInsertionMatrix l * (rightInsertionMatrix l).conjTranspose)
        (u.1, u.2.val) (u.1, u.2.val)) := by
  classical
  ext u v
  by_cases huv : u = v
  · subst v
    simp [compressedDephasedGram]
  · by_cases hq : u.1 = v.1
    · have hr : u.2.val ≠ v.2.val := by
        intro he
        exact huv (Prod.ext hq (Subtype.ext he))
      simp only [compressedDephasedGram, hq, ↓reduceIte,
        Matrix.diagonal_apply_ne _ huv]
      rw [← hq]
      exact rightInsertionMatrix_dephased_offDiagonal l u.1 hr
    · simp [compressedDephasedGram, hq, Matrix.diagonal_apply_ne _ huv]

open scoped ComplexOrder

/-- The compressed, dephased Gram matrix is positive semidefinite. -/
theorem compressedDephasedGram_posSemidef (l : Relation α β) (m : ℕ) :
    (compressedDephasedGram l m).PosSemidef := by
  classical
  rw [compressedDephasedGram_eq_diagonal]
  apply Matrix.PosSemidef.diagonal
  intro u
  change 0 ≤ (rightInsertionMatrix l * (rightInsertionMatrix l).conjTranspose)
    (u.1, u.2.val) (u.1, u.2.val)
  rw [rightInsertionMatrix_gram_diagonal_real]
  exact_mod_cast (Finset.sum_nonneg (fun c _ => Complex.normSq_nonneg
    (rightInsertionMatrix l (u.1, u.2.val) c)))

/-- The full compressed dephased Gram matrix is bounded above in positive
    semidefinite order by `I/(d-m)`. Unlike an entrywise bound, this controls
    arbitrary coherent superpositions of all bounded query-and-record labels.
    The physical support embedding into this finite model is still separate. -/
theorem compressedDephasedGram_le_scalar (l : Relation α β) (m : ℕ)
    (hmd : m < Fintype.card α) :
    (Matrix.diagonal (fun _ : α × BoundedRecord l m =>
      ((1 / ((Fintype.card α : ℝ) - (m : ℝ)) : ℝ) : ℂ)) -
      compressedDephasedGram l m).PosSemidef := by
  classical
  rw [compressedDephasedGram_eq_diagonal, Matrix.diagonal_sub]
  apply Matrix.PosSemidef.diagonal
  intro u
  change 0 ≤ ((1 / ((Fintype.card α : ℝ) - (m : ℝ)) : ℝ) : ℂ) -
    (rightInsertionMatrix l * (rightInsertionMatrix l).conjTranspose)
      (u.1, u.2.val) (u.1, u.2.val)
  have hle := rightInsertionMatrix_gram_diagonal_bound l u.2.val u.1 m u.2.property hmd
  rw [rightInsertionMatrix_gram_diagonal_real] at hle ⊢
  simp only [Complex.ofReal_re] at hle
  rw [← Complex.ofReal_sub]
  exact_mod_cast sub_nonneg.mpr hle

open scoped Matrix.Norms.L2Operator

/-- The recording rule with the published total-size domain cutoff restored.
    The multiset-basis embedding is distinct from this finite-set definition. -/
noncomputable def cutoffRightInsertionMatrix (l : Relation α β) :
    Matrix (α × Relation α β) (β × Relation α β) ℂ :=
  fun o i => if l.card + i.2.card < Fintype.card α then rightInsertionMatrix l o i else 0

omit [Fintype β] in
/-- On an output row of size below `d`, the total-size cutoff cannot remove a
    nonzero predecessor. This identifies the finite extension with the actual
    cutoff rule exactly where the suppression argument uses it. -/
theorem cutoffRightInsertionMatrix_row_eq (l r : Relation α β) (x : α)
    (hsize : l.card + r.card < Fintype.card α) (c : β × Relation α β) :
    cutoffRightInsertionMatrix l (x, r) c = rightInsertionMatrix l (x, r) c := by
  classical
  by_cases hc : rightInsertionMatrix l (x, r) c = 0
  · simp [cutoffRightInsertionMatrix, hc]
  · obtain ⟨_, hr⟩ := rightInsertionMatrix_nonzero_data l r c.2 x c.1 hc
    have hcard : c.2.card ≤ r.card := by
      rw [hr]
      exact Finset.card_le_card (Finset.subset_insert _ _)
    have hi : l.card + c.2.card < Fintype.card α := by omega
    simp [cutoffRightInsertionMatrix, hi]

/-- Both versions of `BB†` agree on every bounded output subspace. -/
theorem cutoffRightInsertionMatrix_gram_eq (l r s : Relation α β) (x y : α)
    (hr : l.card + r.card < Fintype.card α)
    (hs : l.card + s.card < Fintype.card α) :
    (cutoffRightInsertionMatrix l * (cutoffRightInsertionMatrix l).conjTranspose)
      (x, r) (y, s) =
    (rightInsertionMatrix l * (rightInsertionMatrix l).conjTranspose) (x, r) (y, s) := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply,
    cutoffRightInsertionMatrix_row_eq l r x hr,
    cutoffRightInsertionMatrix_row_eq l s y hs]

/-- Euclidean operator norm of the compressed dephased Gram matrix. This is
    the finite Hilbert-space compression bound used by the removal argument. -/
theorem compressedDephasedGram_operator_norm_le (l : Relation α β) (m : ℕ)
    (hmd : m < Fintype.card α) :
    ‖compressedDephasedGram l m‖ ≤
      1 / ((Fintype.card α : ℝ) - (m : ℝ)) := by
  classical
  have hd : (m : ℝ) < Fintype.card α := by exact_mod_cast hmd
  have hc : 0 ≤ 1 / ((Fintype.card α : ℝ) - (m : ℝ)) := by positivity
  rw [compressedDephasedGram_eq_diagonal, Matrix.l2_opNorm_diagonal]
  apply (pi_norm_le_iff_of_nonneg hc).mpr
  intro u
  have hle := rightInsertionMatrix_gram_diagonal_bound l u.2.val u.1 m u.2.property hmd
  rw [rightInsertionMatrix_gram_diagonal_real] at hle ⊢
  have hs : 0 ≤ ∑ c, Complex.normSq (rightInsertionMatrix l (u.1, u.2.val) c) :=
    Finset.sum_nonneg (fun c _ => Complex.normSq_nonneg _)
  simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs,
    Complex.ofReal_re] using hle

/-- Both recording registers with their joint size bound. -/
abbrev BoundedPair (m : ℕ) :=
  {lr : Relation α β × Relation α β // lr.1.card + lr.2.card ≤ m}

noncomputable instance boundedPairFintype (m : ℕ) :
    Fintype (BoundedPair (α := α) (β := β) m) := Fintype.ofFinite _

noncomputable instance boundedPairDecidableEq (m : ℕ) :
    DecidableEq (BoundedPair (α := α) (β := β) m) := Classical.decEq _

/-- Dephased Gram compression including arbitrary superpositions of the left
    record. The right-insertion map preserves the left register exactly. -/
noncomputable def fullCompressedDephasedGram (m : ℕ) :
    Matrix (α × BoundedPair (α := α) (β := β) m)
      (α × BoundedPair (α := α) (β := β) m) ℂ := fun u v =>
  if u.1 = v.1 ∧ u.2.val.1 = v.2.val.1 then
    (rightInsertionMatrix u.2.val.1 * (rightInsertionMatrix u.2.val.1).conjTranspose)
      (u.1, u.2.val.2) (v.1, v.2.val.2) else 0

theorem fullCompressedDephasedGram_eq_diagonal (m : ℕ) :
    fullCompressedDephasedGram (α := α) (β := β) m = Matrix.diagonal (fun u =>
      (rightInsertionMatrix u.2.val.1 * (rightInsertionMatrix u.2.val.1).conjTranspose)
        (u.1, u.2.val.2) (u.1, u.2.val.2)) := by
  classical
  ext u v
  by_cases huv : u = v
  · subst v
    simp [fullCompressedDephasedGram]
  · by_cases he : u.1 = v.1 ∧ u.2.val.1 = v.2.val.1
    · have hr : u.2.val.2 ≠ v.2.val.2 := by
        intro hr
        exact huv (Prod.ext he.1 (Subtype.ext (Prod.ext he.2 hr)))
      simp only [fullCompressedDephasedGram, if_pos he,
        Matrix.diagonal_apply_ne _ huv]
      rw [← he.1]
      exact rightInsertionMatrix_dephased_offDiagonal u.2.val.1 u.1 hr
    · simp [fullCompressedDephasedGram, he, Matrix.diagonal_apply_ne _ huv]

/-- The uniform operator-norm suppression includes coherent left and right
    records, not merely a fixed-left-record block. -/
theorem fullCompressedDephasedGram_operator_norm_le (m : ℕ)
    (hmd : m < Fintype.card α) :
    ‖fullCompressedDephasedGram (α := α) (β := β) m‖ ≤
      1 / ((Fintype.card α : ℝ) - (m : ℝ)) := by
  classical
  have hd : (m : ℝ) < Fintype.card α := by exact_mod_cast hmd
  have hc : 0 ≤ 1 / ((Fintype.card α : ℝ) - (m : ℝ)) := by positivity
  rw [fullCompressedDephasedGram_eq_diagonal, Matrix.l2_opNorm_diagonal]
  apply (pi_norm_le_iff_of_nonneg hc).mpr
  intro u
  have hle := rightInsertionMatrix_gram_diagonal_bound u.2.val.1 u.2.val.2 u.1
    m u.2.property hmd
  rw [rightInsertionMatrix_gram_diagonal_real] at hle ⊢
  have hs : 0 ≤ ∑ c, Complex.normSq
      (rightInsertionMatrix u.2.val.1 (u.1, u.2.val.2) c) :=
    Finset.sum_nonneg (fun c _ => Complex.normSq_nonneg _)
  simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs,
    Complex.ofReal_re] using hle

/-- The full coherent-record compression is bounded in PSD order as well. -/
theorem fullCompressedDephasedGram_le_scalar (m : ℕ) (hmd : m < Fintype.card α) :
    (Matrix.diagonal (fun _ : α × BoundedPair (α := α) (β := β) m =>
      ((1 / ((Fintype.card α : ℝ) - (m : ℝ)) : ℝ) : ℂ)) -
      fullCompressedDephasedGram (α := α) (β := β) m).PosSemidef := by
  classical
  rw [fullCompressedDephasedGram_eq_diagonal, Matrix.diagonal_sub]
  apply Matrix.PosSemidef.diagonal
  intro u
  change 0 ≤ ((1 / ((Fintype.card α : ℝ) - (m : ℝ)) : ℝ) : ℂ) -
    (rightInsertionMatrix u.2.val.1 * (rightInsertionMatrix u.2.val.1).conjTranspose)
      (u.1, u.2.val.2) (u.1, u.2.val.2)
  have hle := rightInsertionMatrix_gram_diagonal_bound u.2.val.1 u.2.val.2 u.1
    m u.2.property hmd
  rw [rightInsertionMatrix_gram_diagonal_real] at hle ⊢
  simp only [Complex.ofReal_re] at hle
  rw [← Complex.ofReal_sub]
  exact_mod_cast sub_nonneg.mpr hle

end MatrixSupport

end ICO.PathRecordingSupport
