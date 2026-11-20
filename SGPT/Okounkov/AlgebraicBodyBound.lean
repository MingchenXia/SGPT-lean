import SGPT.Okounkov.AlgebraicBodyOperations
import SGPT.Okounkov.SchemeSectionCartierValuation
import SGPT.Okounkov.SchemeSectionWeight
import SGPT.Okounkov.SchemeLineBundleStructuralMetric
import SGPT.Okounkov.TranscendentalBodyBound
import SGPT.Okounkov.PotentialFlagValuationScaling
import SGPT.Okounkov.EffectiveDivisorMetricGeneric
import SGPT.LineBundle.BigLineBundle

/-!
# The flag valuation of sections grows at most linearly: Step 1 of `prop:Okounbiglbdl`

Source `prop:Okounbiglbdl` (chapter *The theory of Okounkov bodies*), Step 1: **there is a
convex body `Δ` (here the cube `[0, C]ⁿ`) such that `Δ_k(L) ⊆ Δ` for all `k`**, i.e. there is
`C` with `ν(s)_i ≤ C k` for every nonzero `s ∈ H⁰(X, L^k)` and every `i`.

## Route

The source argues with intersection numbers `(L - b Y₁) · H^{n-1}` along the flag. We use the
analytic dictionary instead, which is available in the workspace:

* for a smooth Hermitian metric `h` on `L` (`schemeLineBundleMetric`, with curvature `θ`), the
  flag vector of a nonzero section `s ∈ H⁰(L^k)` is the flag valuation of the potential
  `log |s|²_{h^k}` (`schemeFubiniStudySectionVector_eq_flagValuation`): by the Lelong–Poincaré
  dictionary of `SGPT.Okounkov.SchemeSectionWeight` the integration current of the section
  divisor is `kθ + dd^c log |s|²_{h^k}`, whose valuation is the section vector
  (`schemeFubiniStudySectionVector_current`);
* `k⁻¹ log |s|²_{h^k}` is `θ`-psh and the valuation is positively homogeneous, so
  `ν(s)/k = ν(k⁻¹ log |s|²)` is bounded by the uniform bound of the flag valuation on `PSH(X, θ)`
  (`SGPT.Okounkov.TranscendentalBody.exists_flagValuation_le`, blueprint `tok:valuation-bound`,
  proved by the uniform Lelong bound and the trace operator);
* in degree `0`, the powers `s^j` of a nonzero section stay in degree `0` and have bounded
  valuation, so `ν(s) = 0`.

## Main results

* `exists_schemeFubiniStudySectionVector_le`: `∃ C ≥ 0, ν(s)_i ≤ C k` (all line bundles).
* `cubeCone C`: the admissible cone over the cube `[0, C]ⁿ`;
  `schemeProjectiveSectionSemigroup_le_cubeCone`: `Γ(L) ⊆ C([0, C]ⁿ)`, i.e. `Γ(L) ∈ 𝒮(C(Δ))`.
* `degreePolytope_subset_cube`: `Δ_k(L) ⊆ [0, C]ⁿ`; `lineBundleOkounkovBody_subset_cube`,
  `isCompact_lineBundleOkounkovBody`; `nonempty_lineBundleOkounkovBody` for big `L`.
* Consequences for the conditional consumers of `prop:Okounbiglbdl`: `cor:Okounvol` and the
  untwisted case of `prop:Deltaconvtwisted` now only assume the lattice generation of Step 2
  (`tendsto_finrank_div_pow_lineBundleOkounkovBody_of_generates`,
  `tendsto_hausdorffDist_lineBundleDegreeBody_of_generates`).

Step 2 of the source proof (`Γ(L)` generates `ℤⁿ⁺¹` for big `L`, via very ample `A`, `B` with
`L = A - B` carrying sections of prescribed valuations) is not formalized.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.Okounkov

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Set Opposite Filter
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.AlmostSemigroup
open scoped NNReal Pointwise

section Cube

/-- The admissible cone `{(x, t) : t ≥ 0, 0 ≤ xᵢ ≤ C t}` over the cube `[0, C]ⁿ`. -/
def cubeCone {n : ℕ} (C : ℝ) : AdmissibleCone n where
  cone :=
    { carrier := {z | 0 ≤ z.2 ∧ ∀ i, 0 ≤ z.1 i ∧ z.1 i ≤ C * z.2}
      smul_mem' := by
        rintro c hc z ⟨hz2, hz1⟩
        refine ⟨by simpa using mul_nonneg hc.le hz2, fun i => ?_⟩
        simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul]
        refine ⟨mul_nonneg hc.le (hz1 i).1, ?_⟩
        nlinarith [(hz1 i).2]
      add_mem' := by
        rintro z ⟨hz2, hz1⟩ w ⟨hw2, hw1⟩
        refine ⟨by simpa using add_nonneg hz2 hw2, fun i => ?_⟩
        simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply]
        exact ⟨add_nonneg (hz1 i).1 (hw1 i).1, by nlinarith [(hz1 i).2, (hw1 i).2]⟩ }
  closed := by
    have : {z : (Fin n → ℝ) × ℝ | 0 ≤ z.2 ∧ ∀ i, 0 ≤ z.1 i ∧ z.1 i ≤ C * z.2} =
        {z | 0 ≤ z.2} ∩ ⋂ i, ({z | 0 ≤ z.1 i} ∩ {z | z.1 i ≤ C * z.2}) := by
      ext z
      simp [Set.mem_iInter]
    change IsClosed {z : (Fin n → ℝ) × ℝ | 0 ≤ z.2 ∧ ∀ i, 0 ≤ z.1 i ∧ z.1 i ≤ C * z.2}
    rw [this]
    refine (isClosed_le continuous_const continuous_snd).inter (isClosed_iInter fun i => ?_)
    exact (isClosed_le continuous_const ((continuous_apply i).comp continuous_fst)).inter
      (isClosed_le ((continuous_apply i).comp continuous_fst)
        (continuous_const.mul continuous_snd))
  nonnegativeHeight := fun _ hz => hz.1
  zeroHeight := by
    rintro x ⟨-, hx⟩
    funext i
    have := hx i
    simp only [mul_zero] at this
    exact le_antisymm this.2 this.1

/-- The height-one slice of `cubeCone C` is the cube `[0, C]ⁿ`. -/
theorem heightOne_cubeCone {n : ℕ} (C : ℝ) :
    heightOne (cubeCone (n := n) C).cone = Icc (0 : Fin n → ℝ) (fun _ => C) := by
  ext x
  change (0 ≤ (1 : ℝ) ∧ ∀ i, 0 ≤ x i ∧ x i ≤ C * 1) ↔ _
  simp only [zero_le_one, true_and, mul_one, Set.mem_Icc, Pi.le_def, Pi.zero_apply]
  exact ⟨fun h => ⟨fun i => (h i).1, fun i => (h i).2⟩, fun h i => ⟨h.1 i, h.2 i⟩⟩

end Cube

section PositiveDimension

variable {X : Scheme} [IsIntegral X] (f : X ⟶ Spec (.of ℂ)) (m : ℕ)
  [SmoothOfRelativeDimension (m + 1) f] (E : ClosedProjectiveEmbedding f)

local instance algebraicBoundPointTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance algebraicBoundPointCharts :
    ChartedSpace (ComplexModel (m + 1)) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f (m + 1)
local instance algebraicBoundPointManifold [IsSeparated f] [QuasiCompact f] :
    IsComplexManifold (m + 1) (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f (m + 1)

variable (Y : Fin (m + 1 + 1) → Set (SchemeComplexPoint f)) (hY : IsSmoothFlag Y)

/-- The flag vector of a nonzero section `s ∈ H⁰(L^k)` is the flag valuation of the potential
`log |s|²_{h^k}`, for every smooth Hermitian metric `h` of `L`. -/
theorem schemeFubiniStudySectionVector_eq_flagValuation {L : X.Modules} (a : LineBundleAtlas L)
    (H : SchemeLineBundleMetric f (m + 1) E L) (k : ℕ) (s : bundlePowerGlobalSections L k)
    (hs : s ≠ 0) :
    letI := E.isSeparated
    letI := E.quasiCompact
    (fun i => (schemeFubiniStudySectionVector f (m + 1) E Y hY a k s hs i : ℝ)) =
      TranscendentalCore.flagValuation (schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY)
        (H.sectionLogNormSq a k s) := by
  let := E.isSeparated
  let := E.quasiCompact
  let F := schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY
  let D := schemeSectionAnalyticDivisor f (m + 1) E a k s hs
  let ED := H.sectionMeteredDivisor a k s hs
  have hED : DivisorMetric.IsDivisorMetric D ED := H.sectionMeteredDivisor_isDivisorMetric a k s hs
  have hu := isThetaPshPotential_effectiveDivisorMetric D ED hED
  have hcur := schemeFubiniStudySectionVector_current f m E Y hY a k s hs
  have hread : effectiveDivisorIntegrationCurrent F D =
      NaturalThetaPshGeometricCurrent.thetaPotentialCurrent ED.curvature.val ED.weight hu :=
    (effectiveDivisorIntegrationCurrent_eq_of_metric F D ED hED).trans
      (thetaPotentialCurrent_effectiveDivisorMetric_eq D ED hED).symm
  have hcl := effectiveDivisorIntegrationCurrent_closed_type_positive F D
  dsimp only at hcur
  rw [currentFlagValuation_eq_potentialFlagValuation F _ hcl.1 hcl.2.1 hcl.2.2 hu hread] at hcur
  have hw : ED.weight = H.sectionLogNormSq a k s := H.sectionMeteredDivisor_weight a k s hs
  have hfv := TranscendentalCore.flagValuation_eq (F := F) hu
  change _ = TranscendentalCore.flagValuation F (H.sectionLogNormSq a k s)
  rw [← hw, hfv, hcur]
  funext i
  simp

/-- Sections in positive degree: `ν(s)_i ≤ C k`. -/
theorem exists_schemeFubiniStudySectionVector_le_of_pos {L : X.Modules} (a : LineBundleAtlas L) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (k : ℕ), 0 < k → ∀ (s : bundlePowerGlobalSections L k) (hs : s ≠ 0)
      (i : Fin (m + 1)), (schemeFubiniStudySectionVector f (m + 1) E Y hY a k s hs i : ℝ) ≤
        C * k := by
  let := E.isSeparated
  let := E.quasiCompact
  let F := schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY
  let H := schemeLineBundleMetric f (m + 1) E a
  obtain ⟨C, hC0, hC⟩ := TranscendentalBody.exists_flagValuation_le (F := F) (H.curvature a)
  refine ⟨C, hC0, fun k hk s hs i => ?_⟩
  have hA := congrFun (schemeFubiniStudySectionVector_eq_flagValuation f m E Y hY a H k s hs) i
  have hu1 := H.isThetaPshPotential_sectionLogNormSq a k s hs
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  let c : ℝ≥0 := ⟨(k : ℝ)⁻¹, (inv_pos.mpr hkR).le⟩
  have hc : 0 < c := by
    change (0 : ℝ) < (k : ℝ)⁻¹
    exact inv_pos.mpr hkR
  have hsmul := RestrictedApproximantComparison.isThetaPshPotential_smul hu1
    (show 0 < (c : ℝ) from hc)
  have hsc := potentialFlagValuation_pos_smul F hu1 hc
  have hnorm : IsThetaPshPotential (H.curvature a).val
      (fun x => ((c : ℝ) : EReal) * H.sectionLogNormSq a k s x) :=
    H.isThetaPshPotential_normalized_sectionLogNormSq a k hk s hs
  have hb := hC _ hnorm i
  rw [TranscendentalCore.flagValuation_eq hsmul, hsc] at hb
  rw [TranscendentalCore.flagValuation_eq hu1] at hA
  change ((c * potentialFlagValuation F hu1 i : ℝ≥0) : ℝ) ≤ C at hb
  rw [NNReal.coe_mul] at hb
  change (k : ℝ)⁻¹ * ((potentialFlagValuation F hu1 i : ℝ≥0) : ℝ) ≤ C at hb
  rw [hA]
  have := (inv_mul_le_iff₀ hkR).mp hb
  linarith [mul_comm C (k : ℝ)]

/-- Nonzero sections of `L⁰ = 𝒪_X` have flag vector `0`. -/
theorem schemeFubiniStudySectionVector_degree_zero {L : X.Modules} (a : LineBundleAtlas L)
    (s : bundlePowerGlobalSections L 0) (hs : s ≠ 0) :
    schemeFubiniStudySectionVector f (m + 1) E Y hY a 0 s hs = 0 := by
  let := E.isSeparated
  let := E.quasiCompact
  let F := schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY
  let H := schemeLineBundleMetric f (m + 1) E a
  obtain ⟨C, -, hC⟩ :=
    TranscendentalBody.exists_flagValuation_le (F := F) (((0 : ℕ) : ℝ) • H.curvature a)
  -- every nonzero degree-zero section has valuation at most `C`
  have hbound : ∀ (t : bundlePowerGlobalSections L 0) (ht : t ≠ 0) (i : Fin (m + 1)),
      (schemeFubiniStudySectionVector f (m + 1) E Y hY a 0 t ht i : ℝ) ≤ C := by
    intro t ht i
    rw [congrFun (schemeFubiniStudySectionVector_eq_flagValuation f m E Y hY a H 0 t ht) i]
    exact hC _ (H.isThetaPshPotential_sectionLogNormSq a 0 t ht) i
  have hmem : ((fun i => (schemeFubiniStudySectionVector f (m + 1) E Y hY a 0 s hs i : ℤ)),
      (0 : ℤ)) ∈ schemeProjectiveSectionSemigroup f (m + 1) E Y hY a := ⟨0, s, hs, rfl⟩
  funext i
  by_contra hne
  have hpos : (1 : ℝ) ≤ (schemeFubiniStudySectionVector f (m + 1) E Y hY a 0 s hs i : ℝ) := by
    have : 1 ≤ schemeFubiniStudySectionVector f (m + 1) E Y hY a 0 s hs i :=
      Nat.one_le_iff_ne_zero.mpr hne
    exact_mod_cast this
  obtain ⟨j, hj⟩ := exists_nat_gt C
  have hjmem := AlgebraicBody.succ_nsmul_mem _ hmem j
  obtain ⟨d, t, ht, hz⟩ := hjmem
  simp only [Prod.smul_mk, smul_zero] at hz
  obtain ⟨hx, hd⟩ := Prod.mk.inj hz
  have hd0 : d = 0 := by exact_mod_cast hd.symm
  subst hd0
  have hti := hbound t ht i
  have hxi := congrFun hx i
  simp only [Pi.smul_apply, nsmul_eq_mul] at hxi
  have hxi' : (((j + 1 : ℕ) : ℝ) *
      (schemeFubiniStudySectionVector f (m + 1) E Y hY a 0 s hs i : ℝ)) =
      (schemeFubiniStudySectionVector f (m + 1) E Y hY a 0 t ht i : ℝ) := by
    exact_mod_cast hxi
  have : ((j + 1 : ℕ) : ℝ) ≤ C := by
    calc ((j + 1 : ℕ) : ℝ) ≤ ((j + 1 : ℕ) : ℝ) *
          (schemeFubiniStudySectionVector f (m + 1) E Y hY a 0 s hs i : ℝ) :=
          le_mul_of_one_le_right (by positivity) hpos
      _ ≤ C := hxi' ▸ hti
  push_cast at this
  linarith

end PositiveDimension

variable {X : Scheme} [IsIntegral X] (f : X ⟶ Spec (.of ℂ)) (n : ℕ)
  [SmoothOfRelativeDimension n f] (E : ClosedProjectiveEmbedding f)

local instance algebraicBoundTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance algebraicBoundCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f n

/-- **Source `prop:Okounbiglbdl`, Step 1**: there is `C ≥ 0` such that `ν(s)_i ≤ C k` for every
nonzero section `s ∈ H⁰(X, L^k)`, every `k` and every coordinate `i` (any line bundle `L`). -/
theorem exists_schemeFubiniStudySectionVector_le (Y : Fin (n + 1) → Set (SchemeComplexPoint f))
    (hY : IsSmoothFlag Y) {L : X.Modules} (a : LineBundleAtlas L) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (k : ℕ) (s : bundlePowerGlobalSections L k) (hs : s ≠ 0) (i : Fin n),
      (schemeFubiniStudySectionVector f n E Y hY a k s hs i : ℝ) ≤ C * k := by
  rcases n with _ | m
  · exact ⟨0, le_rfl, fun _ _ _ i => i.elim0⟩
  · obtain ⟨C, hC0, hC⟩ := exists_schemeFubiniStudySectionVector_le_of_pos f m E Y hY a
    refine ⟨C, hC0, fun k s hs i => ?_⟩
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · rw [schemeFubiniStudySectionVector_degree_zero f m E Y hY a s hs]
      simp
    · exact hC k hk s hs i

variable (Y : Fin (n + 1) → Set (SchemeComplexPoint f)) (hY : IsSmoothFlag Y)

/-- **Source `prop:Okounbiglbdl`, Step 1, cone form**: `Γ(L)` lies in the cone over the cube
`[0, C]ⁿ` for some `C ≥ 0`. -/
theorem exists_schemeProjectiveSectionSemigroup_le_cubeCone {L : X.Modules}
    (a : LineBundleAtlas L) :
    ∃ C : ℝ, 0 ≤ C ∧ schemeProjectiveSectionSemigroup f n E Y hY a ≤
      latticePoints (cubeCone (n := n) C).cone := by
  obtain ⟨C, hC0, hC⟩ := exists_schemeFubiniStudySectionVector_le f n E Y hY a
  refine ⟨C, hC0, ?_⟩
  rintro _ ⟨k, s, hs, rfl⟩
  refine ⟨by simp [latticeCast], fun i => ⟨by simp [latticeCast], ?_⟩⟩
  simpa [latticeCast] using hC k s hs i

/-- One cone `C([0, C]ⁿ)` contains `Γ(θ, φ)` for every weight `φ`: the cone hypothesis in the
definition of the partial Okounkov body (`SGPT.Okounkov.partialOkounkovBody`, source
`def:Okounkov:L687`) holds for this admissible cone. -/
theorem exists_multiplierSectionSet_subset_cubeCone {L : X.Modules} (a : LineBundleAtlas L) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ φ : SchemeComplexPoint f → EReal,
      multiplierSectionSet f n E Y hY a φ ⊆
        (latticePoints (cubeCone (n := n) C).cone : Set ((Fin n → ℤ) × ℤ)) := by
  obtain ⟨C, hC0, hS⟩ := exists_schemeProjectiveSectionSemigroup_le_cubeCone f n E Y hY a
  exact ⟨C, hC0, fun φ z hz => hS (multiplierSectionSet_subset a φ hz)⟩

/-- **Source `prop:Okounbiglbdl`, Step 1, polytope form**: all polytopes `Δ_k(L)` lie in one
cube `[0, C]ⁿ`. -/
theorem exists_degreePolytope_subset_cube {L : X.Modules} (a : LineBundleAtlas L) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℕ,
      degreePolytope n (schemeProjectiveSectionSemigroup f n E Y hY a : Set ((Fin n → ℤ) × ℤ)) k ⊆
        Icc (0 : Fin n → ℝ) (fun _ => C) := by
  obtain ⟨C, hC0, hC⟩ := exists_schemeFubiniStudySectionVector_le f n E Y hY a
  refine ⟨C, hC0, fun k => convexHull_min ?_ (convex_Icc _ _)⟩
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨s, hs, rfl⟩ :=
    (schemeProjectiveSectionSemigroup_mem_slice f n E Y hY a k x).mp hx
  refine ⟨fun i => ?_, fun i => ?_⟩
  · simp only [Pi.zero_apply, Pi.smul_apply, smul_eq_mul, Counting.integerCast]
    positivity
  · simp only [Pi.smul_apply, smul_eq_mul, Counting.integerCast]
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simpa using hC0
    · have hkR : (0 : ℝ) < k := by exact_mod_cast hk
      have := hC k s hs i
      rw [inv_mul_le_iff₀ hkR]
      push_cast
      linarith [mul_comm C (k : ℝ)]

/-- `Δ_{Y•}(L)` lies in a cube `[0, C]ⁿ`. -/
theorem exists_lineBundleOkounkovBody_subset_cube {L : X.Modules} (a : LineBundleAtlas L) :
    ∃ C : ℝ, 0 ≤ C ∧ lineBundleOkounkovBody f n E Y hY a ⊆ Icc (0 : Fin n → ℝ) (fun _ => C) := by
  obtain ⟨C, hC0, hS⟩ := exists_schemeProjectiveSectionSemigroup_le_cubeCone f n E Y hY a
  refine ⟨C, hC0, ?_⟩
  intro x hx
  rw [← heightOne_cubeCone]
  exact Okounkov.closedCone_subset_source (cubeCone C) _ hS
    ⟨0, schemeProjectiveSectionSemigroup_zero_mem f n E Y hY a⟩ hx

/-- `Δ_{Y•}(L)` is compact. -/
theorem isCompact_lineBundleOkounkovBody {L : X.Modules} (a : LineBundleAtlas L) :
    IsCompact (lineBundleOkounkovBody f n E Y hY a) := by
  obtain ⟨C, -, hsub⟩ := exists_lineBundleOkounkovBody_subset_cube f n E Y hY a
  exact isCompact_Icc.of_isClosed_subset (lineBundleOkounkovBody_isClosed_convex a).1 hsub

/-- A nonzero section `s ∈ H⁰(L^k)`, `k > 0`, gives the point `ν(s)/k` of `Δ_{Y•}(L)`. -/
theorem normalized_mem_lineBundleOkounkovBody {L : X.Modules} (a : LineBundleAtlas L) {k : ℕ}
    (hk : 0 < k) (s : bundlePowerGlobalSections L k) (hs : s ≠ 0) :
    (k : ℝ)⁻¹ • (fun i => (schemeFubiniStudySectionVector f n E Y hY a k s hs i : ℝ)) ∈
      lineBundleOkounkovBody f n E Y hY a := by
  have hmem := Okounkov.mem_closedCone_of_mem (schemeProjectiveSectionSemigroup f n E Y hY a)
    (⟨k, s, hs, rfl⟩ : ((fun i => (schemeFubiniStudySectionVector f n E Y hY a k s hs i : ℤ)),
      (k : ℤ)) ∈ schemeProjectiveSectionSemigroup f n E Y hY a)
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have := (Okounkov.closedCone (schemeProjectiveSectionSemigroup f n E Y hY a)).smul_mem
    (r := (k : ℝ)⁻¹) (inv_pos.mpr hkR).le hmem
  change ((k : ℝ)⁻¹ • (fun i => (schemeFubiniStudySectionVector f n E Y hY a k s hs i : ℝ)),
    (1 : ℝ)) ∈ (Okounkov.closedCone (schemeProjectiveSectionSemigroup f n E Y hY a) :
      Set ((Fin n → ℝ) × ℝ))
  have heq : (k : ℝ)⁻¹ • latticeCast n
      ((fun i => (schemeFubiniStudySectionVector f n E Y hY a k s hs i : ℤ)), (k : ℤ)) =
      ((k : ℝ)⁻¹ • (fun i => (schemeFubiniStudySectionVector f n E Y hY a k s hs i : ℝ)),
        (1 : ℝ)) := by
    ext i
    · simp [latticeCast]
    · simp [latticeCast, hkR.ne']
  rw [← heq]
  exact this

/-- For a big line bundle `L`, `Δ_{Y•}(L)` is nonempty; with compactness and convexity, it is a
convex body (source `def:Okobd`, appendix: a convex body is a nonempty compact convex set). -/
theorem nonempty_lineBundleOkounkovBody {L : X.Modules} (a : LineBundleAtlas L)
    (hL : SGPT.LineBundle.IsBig f L n) : (lineBundleOkounkovBody f n E Y hY a).Nonempty := by
  obtain ⟨k, ⟨s, hs⟩, hk⟩ := ((hL.eventually_exists_ne_zero).and (eventually_gt_atTop 0)).exists
  exact ⟨_, normalized_mem_lineBundleOkounkovBody f n E Y hY a hk s hs⟩

/-- Source `cor:Okounvol`, conditional only on Step 2 of `prop:Okounbiglbdl`: if `Γ(L)` generates
`ℤⁿ⁺¹`, then `k⁻ⁿ h⁰(X, L^k) → vol Δ_{Y•}(L)`. -/
theorem tendsto_finrank_div_pow_lineBundleOkounkovBody_of_generates {L : X.Modules}
    (a : LineBundleAtlas L)
    (hG : LatticeSlices.generatedGroup (schemeProjectiveSectionSemigroup f n E Y hY a) = ⊤) :
    Tendsto (fun k : ℕ =>
        letI := schemeGlobalSectionModule f (bundleTensorPower L k)
        (k : ℝ)⁻¹ ^ n * (Module.finrank ℂ (bundlePowerGlobalSections L k) : ℝ))
      atTop (nhds (MeasureTheory.volume.real (lineBundleOkounkovBody f n E Y hY a))) := by
  obtain ⟨C, -, hS⟩ := exists_schemeProjectiveSectionSemigroup_le_cubeCone f n E Y hY a
  exact tendsto_finrank_div_pow_lineBundleOkounkovBody a (cubeCone C) hS hG

/-- Source `prop:Deltaconvtwisted` for `T = 𝒪_X`, conditional only on Step 2 of
`prop:Okounbiglbdl`: if `Γ(L)` generates `ℤⁿ⁺¹`, then `Δ_k(L) → Δ_{Y•}(L)` in the Hausdorff
metric. -/
theorem tendsto_hausdorffDist_lineBundleDegreeBody_of_generates {L : X.Modules}
    (a : LineBundleAtlas L)
    (hG : LatticeSlices.generatedGroup (schemeProjectiveSectionSemigroup f n E Y hY a) = ⊤) :
    Tendsto (fun k => Metric.hausdorffDist (schemeProjectiveSectionDegreeBody f n E Y hY a k)
      ((EuclideanSpace.equiv (Fin n) ℝ).symm '' lineBundleOkounkovBody f n E Y hY a))
      atTop (nhds 0) := by
  obtain ⟨C, -, hS⟩ := exists_schemeProjectiveSectionSemigroup_le_cubeCone f n E Y hY a
  exact tendsto_hausdorffDist_lineBundleDegreeBody a (cubeCone C) hS hG

end SGPT.Okounkov
