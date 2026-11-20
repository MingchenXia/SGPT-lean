import SGPT.Siu.SiuModificationLelong
import SGPT.Siu.ModifiedNef
import SGPT.BDivisor.ClassPullback
import SGPT.BDivisor.ClassPushforward
import SGPT.BDivisor.NefBDivisor
import SGPT.Foundations.Analysis.Pending.UniformPerturbedKahlerLowerBound
import SGPT.Foundations.Analysis.Pending.PositiveCurrentPrescribedBottChernRepresentation
import SGPT.Foundations.Analysis.Pending.ThetaPotentialCurrentBottChernClass

/-!
# Modified nef classes under push-forward along modifications (`prop:cones_modif`, item 2)

Source `prop:cones_modif` (chapter *Plurisubharmonic functions*): for a proper bimeromorphic
morphism `π : Y → X` from a Kähler manifold `Y`,

1. `π^*α` is nef for every nef class `α` on `X`
   (`SGPT.BDivisor.classNef_classPullback`, already formalized);
2. `π_*β` is modified nef for every modified nef class `β` on `Y`
   (`classModifiedNefWithRespectTo_classPushforward`, this file).

For item 2 the book reduces to big classes and uses currents with minimal singularities. We use
the definition of modified nef classes (`def:mnclass`, `SGPT.Siu.ModifiedNefWithRespectTo`)
directly, which avoids the reduction: for `ε > 0` choose `A > 0` with `A ω_X ≥ κ` for a smooth
representative `κ` of `π_*{ω_Y}`, and a non-divisorial current `S = θ + δω_Y + ddᶜφ` (`δ = ε/A`)
given by the modified nefness of `β = {θ}`. Its push-forward `π_*S` is a closed positive current
in `π_*β + δπ_*{ω_Y}`, hence `π_*S = θ' + δκ + ddᶜu` (`θ'` a representative of `π_*β`), and
`π_*S` is non-divisorial by `lma:ndvpush` (`SGPT.Siu.isNonDivisorial_currentPushforward`). Since
`θ' + εω_X = (θ' + δκ) + δ(Aω_X − κ)` with `Aω_X − κ ≥ 0`, `u` is `(θ' + εω_X)`-psh with
vanishing generic Lelong numbers along all prime divisors.

The argument only needs, for a closed form `σ` on `Y` (no Kähler form on `Y`), that every class
`{θ + εσ}` contains a non-divisorial closed positive current
(`classModifiedNefWithRespectTo_classPushforward_of_forall`). For `cor:mn_level_nefb` we also
record:

* nef classes are modified nef (`ModifiedNefWithRespectTo.of_nef`), and pulled-back nef classes
  satisfy the criterion (`exists_pullback_nef_potential`);
* the modified nef cone is closed in the Euclidean topology when `H^{1,1}` is finite-dimensional
  (`classModifiedNef_of_tendsto`).
-/

set_option autoImplicit false

noncomputable section

universe u

open Set Filter
open scoped Topology Manifold ContDiff ENNReal

namespace SGPT.Siu

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses
  SGPT.Foundations.Analysis.Pending
  SGPT.Foundations.Analysis.Pending.CanonicalCurrentFrame
  SGPT.Foundations.Analysis.Pending.CurrentBottChernClass
  SGPT.Foundations.Analysis.Pending.NaturalThetaPshGeometricCurrent
  SGPT.Foundations.Analysis.Pending.AnalyticModificationLocalDiscrepancy
  SGPT.BDivisor

variable {m : ℕ} {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
  [ChartedSpace (ComplexModel (m + 1)) X] [IsComplexManifold (m + 1) X]
  [ChartedSpace (ComplexModel (m + 1)) Y] [IsComplexManifold (m + 1) Y]
  [CompactSpace X] [CompactSpace Y]

/-- **The push-forward criterion for modified nef classes.** Let `π : Y → X` be a proper
bimeromorphic morphism of compact complex manifolds, `ω_X` a Kähler form on `X`, and `θ, σ`
closed real `(1,1)`-forms on `Y` such that for every `ε > 0` the class `{θ + εσ}` contains a
non-divisorial closed positive current `θ + εσ + ddᶜφ` (no positivity of `σ` and no Kähler form
on `Y` are needed). Then `π_*{θ}` is modified nef. -/
theorem classModifiedNefWithRespectTo_classPushforward_of_forall {π : Y → X}
    (hπ : IsAnalyticModification (n := m + 1) π) (ωX : KahlerBackground (m + 1) X)
    (θ σ : ClosedRealOneOneForm (m + 1) Y)
    (hθ : ∀ ε : ℝ, 0 < ε → ∃ φ : Y → EReal, IsThetaPshPotential (θ + ε • σ).val φ ∧
      ∀ D : SGPT.PSH.GeometricPrimeCarrier (m + 1) Y, primeGenericLelong φ D = 0) :
    ClassModifiedNefWithRespectTo ωX
      (classPushforward hπ.1 (canonicalBasis (m + 1)) (Nat.succ_pos m)
        (RealBottChern.ofRepresentative θ)) := by
  set P := classPushforward hπ.1 (canonicalBasis (m + 1)) (Nat.succ_pos m) with hP
  -- a representative `θ'` of `π_*{θ}` and `κ` of `π_*{σ}`
  obtain ⟨θ', hθ'⟩ : ∃ θ' : ClosedRealOneOneForm (m + 1) X,
      RealBottChern.ofRepresentative θ' = P (RealBottChern.ofRepresentative θ) :=
    ⟨Quotient.out _, Quotient.out_eq _⟩
  obtain ⟨κ, hκ⟩ : ∃ κ : ClosedRealOneOneForm (m + 1) X,
      RealBottChern.ofRepresentative κ = P (RealBottChern.ofRepresentative σ) :=
    ⟨Quotient.out _, Quotient.out_eq _⟩
  rw [← hθ']
  change ModifiedNefWithRespectTo ωX θ'
  obtain ⟨A, hA, hsemi⟩ := KahlerDomination.exists_pos_isSemipositive_add_smul ωX (-κ)
  intro ε hε
  set δ := ε / A with hδ
  have hδpos : 0 < δ := div_pos hε hA
  obtain ⟨φ, hφ, hφD⟩ := hθ δ hδpos
  -- the non-divisorial current `S = (θ + δσ) + ddᶜφ` and its push-forward
  set S := ThetaPotentialCurrentBottChernClass.thetaClosedCurrent (θ + δ • σ) φ hφ
  have hS : bottChernClass (canonicalBasis (m + 1)) (Nat.succ_pos m) S =
      RealBottChern.ofRepresentative (θ + δ • σ) :=
    ThetaPotentialCurrentBottChernClass.bottChernClass_thetaClosedCurrent _ φ hφ
  have hpush : bottChernClass (canonicalBasis (m + 1)) (Nat.succ_pos m)
      (closedCurrentPushforward hπ.1 (canonicalBasis (m + 1)) (Nat.succ_pos m) S) =
      RealBottChern.ofRepresentative (θ' + δ • κ) := by
    rw [bottChernClass_closedCurrentPushforward, hS, RealBottChern.ofRepresentative_add,
      RealBottChern.ofRepresentative_smul, RealBottChern.ofRepresentative_add,
      RealBottChern.ofRepresentative_smul, hθ', hκ, ← hP, map_add, map_smul]
  have hT : IsClosedPositiveCurrent (thetaPotentialCurrent (θ + δ • σ).val φ hφ) :=
    isClosedPositiveCurrent_thetaPotentialCurrent _ φ hφ
  have hpos : GlobalPositiveCurrentACRestriction.IsFullPositive
      (closedCurrentPushforward hπ.1 (canonicalBasis (m + 1)) (Nat.succ_pos m) S).val :=
    (isClosedPositiveCurrent_currentPushforward hπ.1 hT).2.2
  obtain ⟨w, hw, hread, -⟩ :=
    PositiveCurrentPrescribedBottChernRepresentation.exists_theta_representation_of_class_eq
      (closedCurrentPushforward hπ.1 (canonicalBasis (m + 1)) (Nat.succ_pos m) S)
      (θ' + δ • κ) hpos hpush
  have hread' : currentPushforward hπ.1 (thetaPotentialCurrent (θ + δ • σ).val φ hφ) =
      thetaPotentialCurrent (θ' + δ • κ).val w hw := hread
  -- `w` is `(θ' + εω_X)`-psh
  have hsemi' : (δ • (-κ + A • ωX.form)).val.IsSemipositive :=
    KahlerDomination.isSemipositive_smul hsemi hδpos.le
  have hw' := LocalPotentials.isThetaPshPotential_add_of_semipositive hw hsemi'
  have hform : θ' + δ • κ + δ • (-κ + A • ωX.form) = θ' + ε • ωX.form := by
    rw [smul_add, smul_neg, smul_smul, hδ, div_mul_cancel₀ ε hA.ne']
    abel
  rw [hform] at hw'
  refine ⟨w, hw', fun D => ?_⟩
  -- the generic Lelong numbers of `w` are those of the non-divisorial current `π_*S`
  have hnd : IsNonDivisorial (thetaPotentialCurrent (θ + δ • σ).val φ hφ) hT := by
    rw [isNonDivisorial_iff]
    intro D'
    rw [currentGenericLelong_eq_primeGenericLelong hT rfl D']
    exact hφD D'
  have hpushnd := isNonDivisorial_currentPushforward hπ hT hnd
  rw [isNonDivisorial_iff] at hpushnd
  have h0 := hpushnd D
  rwa [currentGenericLelong_eq_primeGenericLelong _ hread' D] at h0

/-- **Source `prop:cones_modif`, item 2: the push-forward of a modified nef class is modified
nef.** For a proper bimeromorphic morphism `π : Y → X` of compact complex manifolds carrying
Kähler forms `ω_Y`, `ω_X`, and a class `β ∈ H^{1,1}(Y, ℝ)` which is modified nef, the class
`π_*β ∈ H^{1,1}(X, ℝ)` is modified nef. -/
theorem classModifiedNefWithRespectTo_classPushforward {π : Y → X}
    (hπ : IsAnalyticModification (n := m + 1) π)
    (ωX : KahlerBackground (m + 1) X) (ωY : KahlerBackground (m + 1) Y)
    {β : RealBottChern (m + 1) Y} (hβ : ClassModifiedNefWithRespectTo ωY β) :
    ClassModifiedNefWithRespectTo ωX
      (classPushforward hπ.1 (canonicalBasis (m + 1)) (Nat.succ_pos m) β) := by
  induction β using Quotient.inductionOn with
  | h θ => exact classModifiedNefWithRespectTo_classPushforward_of_forall hπ ωX θ ωY.form hβ

/-! ### Nef classes and their pull-backs -/

omit [CompactSpace X] [CompactSpace Y] in
/-- A real-valued `θ`-psh potential has vanishing generic Lelong numbers (a positive Lelong number
forces a pole). -/
theorem primeGenericLelong_coe_eq_zero {θ : SmoothRealForm (m + 1) Y 2} {h : Y → ℝ}
    (hh : IsThetaPshPotential θ (fun y => (h y : EReal)))
    (D : SGPT.PSH.GeometricPrimeCarrier (m + 1) Y) :
    primeGenericLelong (fun y => (h y : EReal)) D = 0 := by
  obtain ⟨x, hx⟩ := D.nonempty
  refine le_antisymm ((iInf₂_le x hx).trans_eq ?_) bot_le
  have hL : FirstPass.NonKahlerLocus.lelongNumber (n := m + 1) (fun y => (h y : EReal)) x = 0 := by
    by_contra hne
    exact EReal.coe_ne_bot (h x) (FirstPass.NonKahlerLocus.eq_bot_of_lelongNumber_pos
      (Nat.succ_pos m) hh.1 (pos_iff_ne_zero.mpr hne))
  rw [SquaredLogLelongSourceNormalization.lelongNumber_eq_two_mul_squaredLog
    (Nat.succ_ne_zero m)] at hL
  exact (mul_eq_zero.mp hL).resolve_left (by norm_num)

omit [CompactSpace X] [CompactSpace Y] in
/-- Pull-back of closed real `(1,1)`-forms commutes with `a + c • b`. -/
theorem pullback_add_smul {f : Y → X}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel (m + 1)) ∞ f)
    (a b : ClosedRealOneOneForm (m + 1) X) (c : ℝ) :
    ClosedRealOneOneForm.pullback hf (a + c • b) =
      ClosedRealOneOneForm.pullback hf a + c • ClosedRealOneOneForm.pullback hf b := by
  apply ClosedRealOneOneForm.ext
  intro e z
  ext v
  rfl

omit [CompactSpace X] [CompactSpace Y] in
/-- A nef class `{θ}` has, for every `ε > 0`, a smooth `(θ + εω)`-psh potential. -/
theorem exists_nef_potential {κ : KahlerBackground (m + 1) X} {θ : ClosedRealOneOneForm (m + 1) X}
    (hθ : NefWithRespectTo κ θ) (ε : ℝ) (hε : 0 < ε) :
    ∃ h : X → ℝ, ChartSmooth (n := m + 1) h ∧
      ThetaPlurisubharmonic (θ + ε • κ.form).val (fun x => (h x : EReal)) := by
  obtain ⟨h, hh, hpos⟩ := hθ ε hε
  refine ⟨h, hh, (LocalPotentials.thetaPlurisubharmonic_smooth_iff (θ + ε • κ.form) h hh).mpr ?_⟩
  intro e z hz v
  have h1 := hpos e z hz v
  simp only [ClosedRealOneOneForm.coeff_add, ClosedRealOneOneForm.coeff_smul,
    ContinuousAlternatingMap.add_apply, ContinuousAlternatingMap.smul_apply,
    smul_eq_mul] at h1 ⊢
  linarith

omit [CompactSpace X] [CompactSpace Y] in
/-- **Nef classes are modified nef.** -/
theorem ModifiedNefWithRespectTo.of_nef {ωX : KahlerBackground (m + 1) X}
    {θ : ClosedRealOneOneForm (m + 1) X} (hθ : NefWithRespectTo ωX θ) :
    ModifiedNefWithRespectTo ωX θ := by
  intro ε hε
  obtain ⟨h, -, hpsh⟩ := exists_nef_potential hθ ε hε
  have hpot : IsThetaPshPotential (θ + ε • ωX.form).val (fun x => (h x : EReal)) :=
    ⟨hpsh, fun y _ _ hy => ⟨y, hy, EReal.coe_ne_bot _⟩⟩
  exact ⟨_, hpot, primeGenericLelong_coe_eq_zero hpot⟩

omit [CompactSpace X] [CompactSpace Y] in
/-- **Pulled-back nef classes satisfy the push-forward criterion.** If `θ` is nef with respect to
a Kähler form `κ` on `X` and `f : Y → X` is holomorphic (no Kähler form on `Y` is needed), then
for every `ε > 0` the class `f^*{θ + εκ}` contains `f^*θ + εf^*κ + ddᶜ(h ∘ f)` with `h` smooth,
a closed positive current with vanishing Lelong numbers. -/
theorem exists_pullback_nef_potential {f : Y → X}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel (m + 1)) ∞ f)
    (κ : KahlerBackground (m + 1) X) {θ : ClosedRealOneOneForm (m + 1) X}
    (hθ : NefWithRespectTo κ θ) (ε : ℝ) (hε : 0 < ε) :
    ∃ φ : Y → EReal, IsThetaPshPotential
        (ClosedRealOneOneForm.pullback hf θ + ε • ClosedRealOneOneForm.pullback hf κ.form).val φ ∧
      ∀ D : SGPT.PSH.GeometricPrimeCarrier (m + 1) Y, primeGenericLelong φ D = 0 := by
  obtain ⟨h, -, hpsh⟩ := exists_nef_potential hθ ε hε
  have hcomp := GlobalPotentialPullback.thetaPlurisubharmonic_comp hf hpsh
  rw [← ClosedRealOneOneForm.pullback_val, pullback_add_smul] at hcomp
  have hpot : IsThetaPshPotential
      (ClosedRealOneOneForm.pullback hf θ + ε • ClosedRealOneOneForm.pullback hf κ.form).val
      (fun y => ((h (f y) : ℝ) : EReal)) :=
    ⟨hcomp, fun y _ _ hy => ⟨y, hy, EReal.coe_ne_bot _⟩⟩
  exact ⟨_, hpot, primeGenericLelong_coe_eq_zero hpot⟩

/-! ### Closedness of the modified nef cone -/

omit [CompactSpace Y] in
/-- **The modified nef cone is closed**: if `H^{1,1}(X, ℝ)` is finite-dimensional (Hodge theory,
not formalized), a limit (in the Euclidean topology, along any nontrivial filter) of modified nef
classes is modified nef. -/
theorem classModifiedNef_of_tendsto [FiniteDimensional ℝ (RealBottChern (m + 1) X)]
    (ωX : KahlerBackground (m + 1) X) {ι : Type*} {l : Filter ι} [l.NeBot]
    {α : ι → RealBottChern (m + 1) X} {β : RealBottChern (m + 1) X}
    (hα : ∀ i, ClassModifiedNefWithRespectTo ωX (α i))
    (hlim : Tendsto α l (@nhds _ (euclideanTopology (RealBottChern (m + 1) X)) β)) :
    ClassModifiedNefWithRespectTo ωX β := by
  classical
  let b := Module.finBasis ℝ (RealBottChern (m + 1) X)
  -- smooth representatives of the basis and Kähler bounds `± B_j ≤ C_j ω`
  have hrep : ∀ j, ∃ B : ClosedRealOneOneForm (m + 1) X,
      RealBottChern.ofRepresentative B = b j := fun j => ⟨Quotient.out (b j), Quotient.out_eq _⟩
  choose B hB using hrep
  have hbound : ∀ j, ∃ C : ℝ, 0 < C ∧ (B j + C • ωX.form).val.IsSemipositive ∧
      (-B j + C • ωX.form).val.IsSemipositive := by
    intro j
    obtain ⟨A₁, hA₁, h₁⟩ := KahlerDomination.exists_pos_isSemipositive_add_smul ωX (B j)
    obtain ⟨A₂, hA₂, h₂⟩ := KahlerDomination.exists_pos_isSemipositive_add_smul ωX (-B j)
    exact ⟨A₁ + A₂, by positivity,
      KahlerDomination.isSemipositive_add_smul_mono ωX.isSemipositive (by linarith) h₁,
      KahlerDomination.isSemipositive_add_smul_mono ωX.isSemipositive (by linarith) h₂⟩
  choose C hCpos hC₁ hC₂ using hbound
  induction β using Quotient.inductionOn with
  | h θ =>
  change ModifiedNefWithRespectTo ωX θ
  have hθq : (Quotient.mk _ θ : RealBottChern (m + 1) X) = RealBottChern.ofRepresentative θ :=
    rfl
  rw [hθq] at hlim
  intro ε hε
  set S := ∑ j, C j with hSdef
  have hS : 0 ≤ S := Finset.sum_nonneg fun j _ => (hCpos j).le
  set δ := ε / (2 * (S + 1)) with hδdef
  have hδ : 0 < δ := by positivity
  -- eventually all coordinates of `α i` are `δ`-close to those of `β`
  have hev : ∀ᶠ i in l, ∀ j, |b.coord j (RealBottChern.ofRepresentative θ) -
      b.coord j (α i)| < δ := by
    rw [Filter.eventually_all]
    intro j
    have h1 := (tendsto_euclideanTopology_iff.mp hlim) (b.coord j)
    filter_upwards [Metric.tendsto_nhds.mp h1 δ hδ] with i hi
    rw [Real.dist_eq, abs_sub_comm] at hi
    exact hi
  obtain ⟨i, hi⟩ := hev.exists
  set t : _ → ℝ := fun j => b.coord j (RealBottChern.ofRepresentative θ) - b.coord j (α i)
    with htdef
  -- a modified nef representative of `α i`
  obtain ⟨θi, hθi⟩ : ∃ θi : ClosedRealOneOneForm (m + 1) X,
      RealBottChern.ofRepresentative θi = α i := ⟨Quotient.out _, Quotient.out_eq _⟩
  have hαi := hα i
  rw [← hθi] at hαi
  change ModifiedNefWithRespectTo ωX θi at hαi
  obtain ⟨φ, hφ, hφD⟩ := hαi (ε / 2) (by positivity)
  -- `κ = ∑ t_j B_j + (ε/2) ω` is semipositive
  set κ : ClosedRealOneOneForm (m + 1) X := ∑ j, t j • B j + (ε / 2) • ωX.form with hκdef
  have hterm : ∀ j, (t j • B j + (|t j| * C j) • ωX.form).val.IsSemipositive := by
    intro j
    rcases le_or_gt 0 (t j) with htj | htj
    · have h := KahlerDomination.isSemipositive_smul (hC₁ j) htj
      have heq : t j • (B j + C j • ωX.form) = t j • B j + (|t j| * C j) • ωX.form := by
        rw [abs_of_nonneg htj, smul_add, smul_smul]
      rwa [heq] at h
    · have h := KahlerDomination.isSemipositive_smul (hC₂ j) (neg_nonneg.mpr htj.le)
      have heq : (-t j) • (-B j + C j • ωX.form) = t j • B j + (|t j| * C j) • ωX.form := by
        rw [abs_of_neg htj, smul_add, smul_smul, neg_smul, smul_neg, neg_neg, neg_mul]
      rwa [heq] at h
  have hsum : ∀ s : Finset _,
      (∑ j ∈ s, (t j • B j + (|t j| * C j) • ωX.form)).val.IsSemipositive := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        rw [Finset.sum_empty]
        intro e z hz v
        simp
    | @insert j s hj ih =>
        rw [Finset.sum_insert hj]
        exact UniformPerturbedKahlerLowerBound.isSemipositive_add (hterm j) ih
  have hsmall : ∑ j, |t j| * C j ≤ ε / 2 := by
    have h1 : ∑ j, |t j| * C j ≤ ∑ j, δ * C j :=
      Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hi j).le (hCpos j).le
    have h2 : ∑ j, δ * C j = δ * S := by rw [hSdef, Finset.mul_sum]
    have h3 : δ * S ≤ ε / 2 := by
      rw [hδdef, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    linarith
  have hκ : κ.val.IsSemipositive := by
    have hrest : ((ε / 2 - ∑ j, |t j| * C j) • ωX.form).val.IsSemipositive :=
      KahlerDomination.isSemipositive_smul ωX.isSemipositive (by linarith)
    have heq : κ = ∑ j, (t j • B j + (|t j| * C j) • ωX.form) +
        (ε / 2 - ∑ j, |t j| * C j) • ωX.form := by
      rw [hκdef, Finset.sum_add_distrib, ← Finset.sum_smul, sub_smul]
      abel
    rw [heq]
    exact UniformPerturbedKahlerLowerBound.isSemipositive_add (hsum _) hrest
  -- the class identity `{θi + (ε/2) ω + κ} = {θ + ε ω}`
  have hsumcls : RealBottChern.ofRepresentative (∑ j, t j • B j) =
      RealBottChern.ofRepresentative θ - α i := by
    have h1 : RealBottChern.ofRepresentative (∑ j, t j • B j) = ∑ j, t j • b j := by
      change RealBottChern.ofRepresentativeLinearMap (∑ j, t j • B j) = _
      rw [map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_smul]
      change t j • RealBottChern.ofRepresentative (B j) = _
      rw [hB j]
    rw [h1]
    have h2 : ∀ j, t j = b.repr (RealBottChern.ofRepresentative θ - α i) j := by
      intro j
      rw [map_sub]
      rfl
    simp only [h2]
    exact b.sum_repr _
  have hcls : RealBottChern.ofRepresentative (θi + (ε / 2) • ωX.form + κ) =
      RealBottChern.ofRepresentative (θ + ε • ωX.form) := by
    rw [hκdef]
    simp only [RealBottChern.ofRepresentative_add, RealBottChern.ofRepresentative_smul]
    rw [hsumcls, hθi]
    module
  obtain ⟨f, hf, hfeq⟩ := (RealBottChern.ofRepresentative_eq_iff _ _).mp hcls
  have hφ' := LocalPotentials.isThetaPshPotential_add_of_semipositive hφ hκ
  refine ⟨fun x => φ x - (f x : EReal), thetaPshPotential_sub_smooth hf hfeq hφ', fun D => ?_⟩
  rw [primeGenericLelong_sub_smooth φ hf D, hφD D]

end SGPT.Siu
