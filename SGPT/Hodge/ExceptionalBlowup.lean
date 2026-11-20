import SGPT.Hodge.ExceptionalBDivisor
import SGPT.Foundations.Analysis.Pending.LocalPotentials
import SGPT.Foundations.Analysis.Pending.KahlerDomination
import SGPT.Foundations.Analysis.Pending.PluripolarCapacityDichotomy

/-!
# The `(1,1)`-cohomology of a modification

For a modification `π : Y → X` of compact complex manifolds let `E₁, …, E_N` be the `π`-exceptional
prime divisors (`SGPT.Hodge.Exceptional.excPrimes`, a finite set). Then

`H^{1,1}(X, ℝ) × ℝ^N → H^{1,1}(Y, ℝ)`,  `(β, t) ↦ π^*β + ∑ t_i {E_i}`

is injective (`blowupClassMap_injective`, from the independence of exceptional classes) and, when
`Y` carries a Kähler form, surjective (`blowupClassMap_surjective`: for a closed real
`(1,1)`-form `θ` choose `A > 0` with `σ = θ + Aω_Y ≥ 0`; the smooth currents `σ` and `ω_Y` are
non-divisorial, so Siu's pull–push lemma `π^*π_*S = S + ∑ c_i [E_i]` expresses their classes).
Hence `blowupClassEquiv : H^{1,1}(X, ℝ) × ℝ^N ≃ₗ H^{1,1}(Y, ℝ)`, the general form of
`prop:blowup_cone` (chapter *The theory of b-divisors*; "see RYY19 for a much more general
result"). For a blow-up along a connected centre of codimension at least two the only exceptional
prime divisor is the exceptional divisor `E`; given that, `blowupClassMap_single_bijective` is the
book's identification `H^{1,1}(Y, ℝ) = H^{1,1}(X, ℝ) ⊕ ℝ{E}`.
-/

set_option autoImplicit false

noncomputable section

universe u

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ContDiff Manifold ENNReal

namespace SGPT.Hodge.Exceptional

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.BlowupSequences
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses
  SGPT.Foundations.Analysis.Pending
  SGPT.Foundations.Analysis.Pending.CanonicalCurrentFrame
  SGPT.Foundations.Analysis.Pending.CurrentBottChernClass
  SGPT.Foundations.Analysis.Pending.ThetaPotentialCurrentBottChernClass
  SGPT.Foundations.Analysis.Pending.NaturalThetaPshGeometricCurrent
  SGPT.Foundations.Analysis.Pending.AnalyticModificationLocalDiscrepancy
  SGPT.BDivisor SGPT.Currents.AnalyticSupport

section Formula

variable {m : ℕ} {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
  [ChartedSpace (ComplexModel (m + 1)) X] [IsComplexManifold (m + 1) X]
  [ChartedSpace (ComplexModel (m + 1)) Y] [IsComplexManifold (m + 1) Y]
  [CompactSpace X] [CompactSpace Y]

local notation "PrimeY" => SGPT.PSH.GeometricPrimeCarrier (m + 1) Y

/-- `t ↦ ∑_i t_i {E_i}` over the `π`-exceptional prime divisors. -/
def excCombination {π : Y → X} (hπ : IsAnalyticModification (n := m + 1) π) :
    (excPrimes hπ → ℝ) →ₗ[ℝ] RealBottChern (m + 1) Y where
  toFun t := ∑ E : excPrimes hπ, t E • primeDivisorClass E.val
  map_add' t t' := by
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c t := by
    simp only [Pi.smul_apply, smul_eq_mul, mul_smul, RingHom.id_apply, Finset.smul_sum]

/-- **The blow-up map** `(β, t) ↦ π^*β + ∑_i t_i {E_i}`. -/
def blowupClassMap {π : Y → X} (hπ : IsAnalyticModification (n := m + 1) π) :
    RealBottChern (m + 1) X × (excPrimes hπ → ℝ) →ₗ[ℝ] RealBottChern (m + 1) Y :=
  (classPullback hπ.1).comp (LinearMap.fst ℝ _ _) +
    (excCombination hπ).comp (LinearMap.snd ℝ _ _)

omit [CompactSpace X] in
theorem blowupClassMap_apply {π : Y → X} (hπ : IsAnalyticModification (n := m + 1) π)
    (β : RealBottChern (m + 1) X) (t : excPrimes hπ → ℝ) :
    blowupClassMap hπ (β, t) =
      classPullback hπ.1 β + ∑ E : excPrimes hπ, t E • primeDivisorClass E.val := rfl

omit [CompactSpace X] in
open Classical in
theorem excCombination_eq_sum {π : Y → X} (hπ : IsAnalyticModification (n := m + 1) π)
    (t : excPrimes hπ → ℝ) :
    excCombination hπ t = ∑ D ∈ excPrimes hπ,
      (if h : D ∈ excPrimes hπ then t ⟨D, h⟩ else 0) • primeDivisorClass D := by
  change ∑ E : excPrimes hπ, t E • primeDivisorClass E.val = _
  rw [← Finset.sum_coe_sort (excPrimes hπ)]
  refine Finset.sum_congr rfl fun E _ => ?_
  rw [dif_pos E.2]

/-- **Injectivity of the blow-up map** (independence of exceptional classes). -/
theorem blowupClassMap_injective {π : Y → X} (hπ : IsAnalyticModification (n := m + 1) π) :
    Function.Injective (blowupClassMap hπ) := by
  classical
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  rintro ⟨β, t⟩ h0
  rw [blowupClassMap_apply] at h0
  have h1 : excCombination hπ t = classPullback hπ.1 (-β) := by
    rw [map_neg]
    exact eq_neg_of_add_eq_zero_right h0
  rw [excCombination_eq_sum] at h1
  obtain ⟨ht, hβ⟩ := exceptional_independence hπ (excPrimes hπ)
    (fun E hE => (mem_excPrimes hπ).mp hE) _ (-β) h1
  refine Prod.ext (neg_eq_zero.mp hβ) (funext fun E => ?_)
  have := ht E.val E.2
  rwa [dif_pos E.2] at this

/-- The class of a closed semipositive smooth form lies in the image of the blow-up map. -/
theorem mem_range_blowupClassMap_of_semipositive {π : Y → X}
    (hπ : IsAnalyticModification (n := m + 1) π) (σ : ClosedRealOneOneForm (m + 1) Y)
    (hσ : IsThetaPshPotential σ.val (fun _ => (0 : EReal))) :
    RealBottChern.ofRepresentative σ ∈ LinearMap.range (blowupClassMap hπ) := by
  classical
  set S := thetaPotentialCurrent σ.val (fun _ => (0 : EReal)) hσ with hSdef
  have hS : SGPT.Siu.IsClosedPositiveCurrent S :=
    SGPT.Siu.isClosedPositiveCurrent_thetaPotentialCurrent _ _ hσ
  have hnd : SGPT.Siu.IsNonDivisorial S hS := by
    rw [SGPT.Siu.isNonDivisorial_iff]
    intro D
    obtain ⟨x, hx⟩ := D.nonempty
    refine le_antisymm ((SGPT.Siu.currentGenericLelong_le hS D hx).trans (le_of_eq ?_)) bot_le
    rw [SGPT.Siu.currentLelong_eq_of_eq_thetaPotentialCurrent hS rfl]
    exact SGPT.Okounkov.squaredLogLelongNumber_zero x
  obtain ⟨F, c, hF, hP⟩ := Modification4.pullback_pushforward_eq_add hπ hS hnd
  have hsum := sum_eq_sum_excPrimes hπ F (fun D hD => (hF D hD).1) c SGPT.Siu.primeDivisorCurrent
  have hD := isClosedPositiveCurrent_sum (excPrimes hπ) (fun D => if D ∈ F then c D else 0)
    (fun D _ => by split_ifs with h; exacts [(hF D h).2.le, le_rfl])
  have hcls : classPullback hπ.1 (classPushforward hπ.1 (canonicalBasis (m + 1)) (Nat.succ_pos m)
      (bottChernClass (canonicalBasis (m + 1)) (Nat.succ_pos m) ⟨S, hS.1, hS.2.1⟩)) =
      bottChernClass (canonicalBasis (m + 1)) (Nat.succ_pos m) ⟨S, hS.1, hS.2.1⟩ +
        ∑ D ∈ excPrimes hπ, (if D ∈ F then c D else 0) • primeDivisorClass D := by
    rw [← bottChernClass_pullPush hπ hS,
      ← bottChernClass_sum_primeDivisorCurrent _ _ hD.1 hD.2.1, ← bottChernClass_add']
    congr 1
    exact Subtype.ext (hP.trans (congrArg (S + ·) hsum))
  have hSσ : bottChernClass (canonicalBasis (m + 1)) (Nat.succ_pos m) ⟨S, hS.1, hS.2.1⟩ =
      RealBottChern.ofRepresentative σ := bottChernClass_thetaClosedCurrent σ _ hσ
  refine ⟨(classPushforward hπ.1 (canonicalBasis (m + 1)) (Nat.succ_pos m)
      (RealBottChern.ofRepresentative σ),
    fun E => -(if E.val ∈ F then c E.val else 0)), ?_⟩
  rw [blowupClassMap_apply, ← hSσ, hcls]
  change _ + excCombination hπ _ = _
  rw [excCombination_eq_sum]
  have hBC : ∑ D ∈ excPrimes hπ, (if D ∈ F then c D else 0) • primeDivisorClass D +
      ∑ D ∈ excPrimes hπ, (if h : D ∈ excPrimes hπ then -(if D ∈ F then c D else 0) else 0) •
        primeDivisorClass D = 0 := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun D hD => ?_
    rw [dif_pos hD, neg_smul, add_neg_cancel]
  exact (add_assoc _ _ _).trans ((congrArg (_ + ·) hBC).trans (add_zero _))

/-- **Surjectivity of the blow-up map** when `Y` is Kähler: every class of `Y` is
`π^*β + ∑ t_i {E_i}`. -/
theorem blowupClassMap_surjective {π : Y → X} (hπ : IsAnalyticModification (n := m + 1) π)
    (ωY : KahlerBackground (m + 1) Y) : Function.Surjective (blowupClassMap hπ) := by
  rw [← LinearMap.range_eq_top, eq_top_iff]
  intro α _
  induction α using Quotient.inductionOn with
  | h θ =>
    change RealBottChern.ofRepresentative θ ∈ _
    obtain ⟨A, -, hsemi⟩ := KahlerDomination.exists_pos_isSemipositive_add_smul ωY θ
    have h1 := mem_range_blowupClassMap_of_semipositive hπ (θ + A • ωY.form)
      ((LocalPotentials.isThetaPshPotential_zero_iff _).mpr hsemi)
    have h2 := mem_range_blowupClassMap_of_semipositive hπ ωY.form
      (PluripolarCapacityDichotomy.isThetaPshPotential_zero ωY)
    have h3 := Submodule.sub_mem _ h1 (Submodule.smul_mem _ A h2)
    rw [RealBottChern.ofRepresentative_add, RealBottChern.ofRepresentative_smul,
      add_sub_cancel_right] at h3
    exact h3

/-- **The `(1,1)`-cohomology of a modification with Kähler source** (general form of
`prop:blowup_cone`): `H^{1,1}(X, ℝ) × ℝ^{exceptional primes} ≃ H^{1,1}(Y, ℝ)`,
`(β, t) ↦ π^*β + ∑ t_E {E}`. -/
def blowupClassEquiv {π : Y → X} (hπ : IsAnalyticModification (n := m + 1) π)
    (ωY : KahlerBackground (m + 1) Y) :
    (RealBottChern (m + 1) X × (excPrimes hπ → ℝ)) ≃ₗ[ℝ] RealBottChern (m + 1) Y :=
  LinearEquiv.ofBijective (blowupClassMap hπ)
    ⟨blowupClassMap_injective hπ, blowupClassMap_surjective hπ ωY⟩

/-- **`prop:blowup_cone`, given the unique exceptional prime**: if `E` is the only
`π`-exceptional prime divisor and `Y` is Kähler, then `(β, t) ↦ π^*β + t{E}` is a linear
bijection `H^{1,1}(X, ℝ) × ℝ → H^{1,1}(Y, ℝ)`. -/
theorem blowupClassMap_single_bijective {π : Y → X} (hπ : IsAnalyticModification (n := m + 1) π)
    (ωY : KahlerBackground (m + 1) Y) (E : PrimeY) (hE : excPrimes hπ = {E}) :
    Function.Bijective (fun p : RealBottChern (m + 1) X × ℝ =>
      classPullback hπ.1 p.1 + p.2 • primeDivisorClass E) := by
  have hmem : E ∈ excPrimes hπ := by rw [hE]; exact Finset.mem_singleton_self E
  let e : (excPrimes hπ → ℝ) ≃ₗ[ℝ] ℝ :=
    { toFun := fun t => t ⟨E, hmem⟩
      invFun := fun s _ => s
      left_inv := fun t => by
        funext D
        have hD : D = ⟨E, hmem⟩ := Subtype.ext (Finset.mem_singleton.mp (hE ▸ D.2))
        rw [hD]
      right_inv := fun s => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hcomp : (fun p : RealBottChern (m + 1) X × ℝ =>
      classPullback hπ.1 p.1 + p.2 • primeDivisorClass E) =
      blowupClassMap hπ ∘ ((LinearEquiv.refl ℝ _).prodCongr e.symm) := by
    funext p
    simp only [Function.comp_apply, LinearEquiv.prodCongr_apply, LinearEquiv.refl_apply,
      blowupClassMap_apply]
    congr 1
    have huniv : (Finset.univ : Finset (excPrimes hπ)) = {⟨E, hmem⟩} := by
      ext D
      simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
      exact Subtype.ext (Finset.mem_singleton.mp (hE ▸ D.2))
    rw [huniv, Finset.sum_singleton]
    rfl
  rw [hcomp]
  exact (LinearEquiv.ofBijective (blowupClassMap hπ)
    ⟨blowupClassMap_injective hπ, blowupClassMap_surjective hπ ωY⟩).bijective.comp
    ((LinearEquiv.refl ℝ _).prodCongr e.symm).bijective

end Formula

end SGPT.Hodge.Exceptional
