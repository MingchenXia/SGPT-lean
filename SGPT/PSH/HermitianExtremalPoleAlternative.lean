import SGPT.PSH.HermitianExtremalNormalization
import SGPT.PSH.HermitianExtremalSeriesPole
import SGPT.PSH.HermitianLocalCorrection

/-!
# The genuine extremal competitor family and its pole alternative

Unbounded competitors are normalized by their actual finite maxima. A
geometric weighted series of the normalized potentials is a genuine
Hermitian PSH potential and is negative infinity on the original set.
Countable unions of pole sets in the same Hermitian class use the same
series, retaining every original pole.

Source: FPT, `lem:hermitian-extremal-pole-alternative`.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.HermitianExtremal

open Set Filter MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open Hermitian HermitianExtremalNormalization HermitianExtremalSeries
  HermitianExtremalSeriesPole HermitianExtremalCurrentAlgebra
open scoped Topology

variable {m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]

/-- The literal original extremal competitors: genuine Hermitian-relative
PSH functions nonpositive on the prescribed set. -/
def competitors (ω : Background (m + 1) M) (A : Set M) : Set (M → EReal) :=
  {u | IsHermitianPSH ω u ∧ ∀ x ∈ A, u x ≤ 0}

/-- The literal pointwise global extremal function, before regularization. -/
def extremal (ω : Background (m + 1) M) (A : Set M) (x : M) : EReal :=
  ⨆ u : competitors ω A, u.val x

/-- The zero function is an actual Hermitian PSH potential. The empty
finite-combination theorem constructs its full current positivity. -/
theorem isHermitianPSH_zero (ω : Background (m + 1) M) :
    IsHermitianPSH ω (fun _ : M => (0 : EReal)) := by
  have h := isHermitianPSH_fintype_nonnegSum ω (fun _ : Fin 0 => (0 : ℝ))
    (fun _ => le_rfl) (by simp) (fun _ : Fin 0 => fun _ : M => (0 : EReal))
    (fun i => Fin.elim0 i)
  simpa using h

theorem zero_mem_competitors (ω : Background (m + 1) M) (A : Set M) :
    (fun _ : M => (0 : EReal)) ∈ competitors ω A :=
  ⟨isHermitianPSH_zero ω, fun _ _ => le_rfl⟩

theorem extremal_nonneg (ω : Background (m + 1) M) (A : Set M) (x : M) :
    0 ≤ extremal ω A x :=
  le_iSup (fun u : competitors ω A => u.val x) ⟨fun _ => 0, zero_mem_competitors ω A⟩

theorem extremal_le_zero_on (ω : Background (m + 1) M) {A : Set M} {x : M} (hx : x ∈ A) :
    extremal ω A x ≤ 0 :=
  iSup_le fun u => u.property.2 x hx

/-- Genuine local nondegeneracy excludes poles on every nonempty open
subset, independently of compactness or a measure on the manifold. -/
theorem not_pole_of_nonempty_interior (ω : Background (m + 1) M) (A : Set M)
    (hA : (interior A).Nonempty) :
    ¬ ∃ q : M → EReal, IsHermitianPSH ω q ∧ ∀ x ∈ A, q x = ⊥ := by
  rintro ⟨q, hq, hpoles⟩
  obtain ⟨x, hx⟩ := hA
  obtain ⟨y, hy, hyfinite⟩ := hq.quasiPshPotential.2 x (interior A) isOpen_interior hx
  exact hyfinite (hpoles y (interior_subset hy))

/-- Increasing the prescribed set shrinks the actual competitor family. -/
theorem extremal_antitone (ω : Background (m + 1) M) {A B : Set M} (hAB : A ⊆ B) :
    extremal ω B ≤ extremal ω A := by
  intro x
  apply iSup_le
  intro u
  exact le_iSup_of_le ⟨u.val, u.property.1, fun y hy => u.property.2 y (hAB hy)⟩ le_rfl

/-- The positive geometric coefficient sequence in the source series. -/
def geometricWeight (j : ℕ) : ℝ := (1 / 2 : ℝ) ^ (j + 1)

theorem geometricWeight_pos (j : ℕ) : 0 < geometricWeight j := by
  unfold geometricWeight
  positivity

/-- Every actual finite coefficient sum is at most one. -/
theorem geometricWeight_budget (N : ℕ) :
    ∑ j ∈ Finset.range N, geometricWeight j ≤ 1 := by
  have heq : ∑ j ∈ Finset.range N, geometricWeight j = 1 - (1 / 2 : ℝ) ^ N := by
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_range_succ, ih, geometricWeight, pow_succ]
      ring
  rw [heq]
  exact sub_le_self _ (pow_nonneg (by norm_num) N)

variable [CompactSpace M] [ConnectedSpace M]

/-- Genuine unbounded original competitors manufacture a nonpositive
Hermitian PSH pole potential, without a pole or capacity certificate. -/
theorem exists_pole_of_unbounded_competitors (ω : Background (m + 1) M) (A : Set M)
    (hunbounded : ∀ R : ℝ, ∃ u : M → EReal,
      u ∈ competitors ω A ∧ (R : EReal) ≤ ⨆ x, u x) :
    ∃ q : M → EReal, IsHermitianPSH ω q ∧ (∀ x, q x ≤ 0) ∧ ∀ x ∈ A, q x = ⊥ := by
  classical
  choose u hu hbig using fun j : ℕ => hunbounded ((2 : ℝ) ^ (j + 1))
  choose b hb hclass hle p hp using fun j => exists_normalized_sub_sup ω (hu j).1
  let ψ : ℕ → M → EReal := fun j x => u j x + ((-b j : ℝ) : EReal)
  have hψ : ∀ j, IsHermitianPSH ω (ψ j) := hclass
  have hψle : ∀ j x, ψ j x ≤ 0 := hle
  have hψnorm : ∀ j, ∃ x, 0 ≤ ψ j x := fun j => ⟨p j, (hp j).ge⟩
  have hseries := isHermitianPSH_normalized_series ω (hasCommonLocalCorrections ω)
    geometricWeight (fun j => (geometricWeight_pos j).le) geometricWeight_budget ψ hψ hψle hψnorm
  refine ⟨fun x => ⨅ N, partialSum geometricWeight ψ N x, hseries, fun x => ?_, ?_⟩
  · exact (iInf_le (fun N => partialSum geometricWeight ψ N x) 0).trans_eq (by simp [partialSum])
  · intro x hx
    apply series_eq_bot_of_weighted_terms_le_neg_one
    intro j
    have hbj : (2 : ℝ) ^ (j + 1) ≤ b j := by
      apply EReal.coe_le_coe_iff.mp
      rw [← hb j]
      exact hbig j
    have hvalue : ψ j x ≤ ((-((2 : ℝ) ^ (j + 1)) : ℝ) : EReal) := by
      calc
        ψ j x ≤ (0 : EReal) + ((-b j : ℝ) : EReal) :=
          add_le_add ((hu j).2 x hx) le_rfl
        _ = ((-b j : ℝ) : EReal) := zero_add _
        _ ≤ ((-((2 : ℝ) ^ (j + 1)) : ℝ) : EReal) :=
          EReal.coe_le_coe_iff.mpr (neg_le_neg hbj)
    have hprod : geometricWeight j * (-((2 : ℝ) ^ (j + 1))) = -1 := by
      rw [geometricWeight, mul_neg, ← mul_pow]
      norm_num
    calc
      (geometricWeight j : EReal) * ψ j x
          ≤ (geometricWeight j : EReal) * ((-((2 : ℝ) ^ (j + 1)) : ℝ) : EReal) :=
        mul_le_mul_of_nonneg_left hvalue (EReal.coe_nonneg.mpr (geometricWeight_pos j).le)
      _ = (-1 : EReal) := by rw [← EReal.coe_mul, hprod]; norm_num

omit [CompactSpace M] in
/-- A genuine pole potential produces arbitrarily large actual competitors
by finite translation; its genuine finite point witnesses the growth. -/
theorem unbounded_competitors_of_pole (ω : Background (m + 1) M) (A : Set M)
    {q : M → EReal} (hq : IsHermitianPSH ω q) (hpoles : ∀ x ∈ A, q x = ⊥)
    (R : ℝ) : ∃ u : M → EReal, u ∈ competitors ω A ∧ (R : EReal) ≤ ⨆ x, u x := by
  obtain ⟨x⟩ := (inferInstance : Nonempty M)
  obtain ⟨y, _, hy⟩ := hq.quasiPshPotential.2 x univ isOpen_univ (mem_univ x)
  let t : ℝ := (q y).toReal
  have hyt : q y = (t : EReal) := (EReal.coe_toReal (hq.ne_top y) hy).symm
  let u : M → EReal := fun z => q z + ((R - t : ℝ) : EReal)
  have huy : u y = (R : EReal) := by
    change q y + ((R - t : ℝ) : EReal) = (R : EReal)
    rw [hyt, ← EReal.coe_add]
    congr 1
    ring
  refine ⟨u, ⟨isFormPSH_add_const hq (R - t), fun z hz => ?_⟩, ?_⟩
  · change q z + ((R - t : ℝ) : EReal) ≤ 0
    rw [hpoles z hz, EReal.bot_add]
    exact bot_le
  · rw [← huy]
    exact le_iSup u y

/-- The actual same-background pole condition is equivalent to unbounded
original competitors, with both constructions proved. -/
theorem pole_iff_unbounded_competitors (ω : Background (m + 1) M) (A : Set M) :
    (∃ q : M → EReal, IsHermitianPSH ω q ∧ ∀ x ∈ A, q x = ⊥) ↔
      ∀ R : ℝ, ∃ u : M → EReal, u ∈ competitors ω A ∧ (R : EReal) ≤ ⨆ x, u x := by
  constructor
  · rintro ⟨q, hq, hpoles⟩ R
    exact unbounded_competitors_of_pole ω A hq hpoles R
  · intro hunbounded
    obtain ⟨q, hq, _, hpoles⟩ := exists_pole_of_unbounded_competitors ω A hunbounded
    exact ⟨q, hq, hpoles⟩

/-- If no genuine Hermitian PSH pole potential exists, the entire original
competitor family admits one finite uniform upper bound. -/
theorem exists_uniform_bound_of_not_pole (ω : Background (m + 1) M) (A : Set M)
    (hnot : ¬ ∃ q : M → EReal, IsHermitianPSH ω q ∧ ∀ x ∈ A, q x = ⊥) :
    ∃ C : ℝ, ∀ u ∈ competitors ω A, ∀ x, u x ≤ (C : EReal) := by
  classical
  by_contra hbound
  apply hnot
  have hunbounded : ∀ R : ℝ, ∃ u : M → EReal,
      u ∈ competitors ω A ∧ (R : EReal) ≤ ⨆ x, u x := by
    intro R
    have hR : ¬ ∀ u ∈ competitors ω A, ∀ x, u x ≤ (R : EReal) :=
      fun h => hbound ⟨R, h⟩
    push Not at hR
    obtain ⟨u, hu, x, hx⟩ := hR
    exact ⟨u, hu, hx.le.trans (le_iSup u x)⟩
  obtain ⟨q, hq, _, hpoles⟩ := exists_pole_of_unbounded_competitors ω A hunbounded
  exact ⟨q, hq, hpoles⟩

/-- A countable union of genuine pole sets in one fixed Hermitian class
has one actual nonpositive pole potential in the same class. -/
theorem exists_pole_iUnion (ω : Background (m + 1) M) (A : ℕ → Set M)
    (hA : ∀ j, ∃ u : M → EReal, IsHermitianPSH ω u ∧ ∀ x ∈ A j, u x = ⊥) :
    ∃ q : M → EReal, IsHermitianPSH ω q ∧ (∀ x, q x ≤ 0) ∧
      ∀ x ∈ ⋃ j, A j, q x = ⊥ := by
  classical
  choose u hu hpoles using hA
  choose b _ hclass hle p hp using fun j => exists_normalized_sub_sup ω (hu j)
  let ψ : ℕ → M → EReal := fun j x => u j x + ((-b j : ℝ) : EReal)
  obtain ⟨q, hq, hqle, hqpoles⟩ := normalized_series_nonpositive_and_poles ω
    (hasCommonLocalCorrections ω) geometricWeight geometricWeight_pos geometricWeight_budget
    ψ hclass hle (fun j => ⟨p j, (hp j).ge⟩)
  refine ⟨q, hq, hqle, fun x hx => ?_⟩
  obtain ⟨j, hj⟩ := mem_iUnion.mp hx
  apply hqpoles j x
  change u j x + ((-b j : ℝ) : EReal) = ⊥
  rw [hpoles j x hj, EReal.bot_add]

end SGPT.PSH.HermitianExtremal
