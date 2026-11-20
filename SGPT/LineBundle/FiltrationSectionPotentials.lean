import SGPT.LineBundle.SectionFiltration
import SGPT.Okounkov.SchemeSectionWeight
import SGPT.Okounkov.SchemeCoordinateGlobalGerm
import SGPT.Okounkov.SchemeNativeHolomorphicGerm
import SGPT.PSH.Supremum
import SGPT.Foundations.Analysis.Pending.SubgeodesicSupremumInterior
import SGPT.Foundations.Analysis.Pending.ProductTestForms

/-!
# Section potentials of a filtration

Source `ex:RWN` (chapter *Test curves*), first step: for a filtration `𝓕` of the section ring
of `L` and a smooth Hermitian metric `h` on `L` with `θ = c₁(L, h)`,
`Γ^{𝓕,k}_τ = usc sup {log |s|²_{h^k} : s ∈ 𝓕^{kτ}_k, |s|²_{h^k} ≤ 1}`, and
`Γ^{𝓕,k}_τ ∈ PSH(X, kθ)` whenever `kτ ≤ τ_k(𝓕)`.

## Formal setting

`X` is an integral smooth projective complex scheme of dimension `n` (structure morphism `f`,
closed projective embedding `E`) viewed through its analytic point manifold
`SchemeComplexPoint f`; `h` is a structural smooth Hermitian metric
`H : SchemeLineBundleMetric f n E L`, `|s|²_{h^k} = H.sectionNormSq a k s`,
`log |s|²_{h^k} = H.sectionLogNormSq a k s` and `θ = c₁(L, h) = H.curvature a`. The psh
statement for `log |s|²` is the existing Lelong–Poincaré form
`SchemeLineBundleMetric.isThetaPshPotential_sectionLogNormSq`.

## Main results

* `schemeNativeStalkGerm_eval_const`, `SchemeLineBundleMetric.sectionNormSq_smul`:
  `|c s|²_{h^k} = |c|² |s|²_{h^k}`.
* `SchemeLineBundleMetric.exists_normalized`: every nonzero section has a nonzero multiple
  with `|s|²_{h^k} ≤ 1`.
* `SectionFiltration.isThetaPshPotential_sectionPotential`: `Γ^{𝓕,k}_τ ∈ PSH(X, kθ)` for
  `kτ ≤ τ_k(𝓕)`, `k > 0`; `SectionFiltration.sectionPotential_le_zero`: `Γ^{𝓕,k}_τ ≤ 0`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.LineBundle

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Filter Set SGPT.Okounkov
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open scoped Topology

variable {X : Scheme} (f : X ⟶ Spec (.of ℂ)) (n : ℕ) [SmoothOfRelativeDimension n f]

section Constants

variable [IsSeparated f] [QuasiCompact f]

local instance constPointTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance constPointCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f n
local instance constPointManifold : IsComplexManifold n (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f n

/-- A constant regular function `c` takes the value `c` at every complex point. -/
theorem schemeNativeStalkGerm_eval_const (p : SchemeComplexPoint f) (c : ℂ) :
    NativeHolGerm.eval (schemeNativeStalkGerm f n p
      (X.presheaf.germ ⊤ (schemeComplexPointImage f p) trivial (schemeGlobalConstants f c))) =
      c := by
  let : Algebra ℂ (SchemeCoordinateAffineRing f n p) :=
    affinePointFieldAlgebra ((standardSmoothComplexAffineChart f n p).val.map ≫ f)
  rw [← schemeCoordinateStalkEquiv_global f n p, schemeNativeStalkGerm_regular,
    schemeNativeRegularGerm_eval, schemeCoordinateGlobalCoefficient_const]
  exact AlgHom.commutes _ c

end Constants

end SGPT.LineBundle

namespace SGPT.Okounkov.SchemeLineBundleMetric

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Filter Set SGPT.Okounkov SGPT.LineBundle
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending

variable {X : Scheme} {f : X ⟶ Spec (.of ℂ)} {n : ℕ} [SmoothOfRelativeDimension n f]
  {E : ClosedProjectiveEmbedding f}

local instance potPointTopology' : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance potPointCharts' : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f n
local instance potPointManifold' [IsSeparated f] [QuasiCompact f] :
    IsComplexManifold n (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f n

variable {L : X.Modules} (H : SchemeLineBundleMetric f n E L)

/-- `|c s|²_{h^k} = |c|² |s|²_{h^k}`. -/
theorem sectionNormSq_smul (a : LineBundleAtlas L) (k : ℕ) (c : ℂ) (s : SectionSpace f L k)
    (p : SchemeComplexPoint f) :
    H.sectionNormSq a k (c • s : SectionSpace f L k) p =
      Complex.normSq c * H.sectionNormSq a k s p := by
  let := E.isSeparated
  let := E.quasiCompact
  let U := schemePointFrameOpen f p a
  let α := schemePointFrame f p a
  have hp : schemeComplexPointImage f p ∈ U := schemePointFrame_mem f p a
  rw [H.sectionNormSq_frame a α k _ p hp, H.sectionNormSq_frame a α k s p hp]
  have hco : (α.tensorPower k).coefficients (𝟙 U)
      ((bundleTensorPower L k).val.map (homOfLE le_top).op (c • s : SectionSpace f L k)) =
      X.sheaf.obj.map (homOfLE (le_top : U ≤ ⊤)).op (schemeGlobalConstants f c) *
        (α.tensorPower k).coefficients (𝟙 U)
          ((bundleTensorPower L k).val.map (homOfLE le_top).op s) := by
    have h := (bundleTensorPower L k).val.map_smul (homOfLE (le_top : U ≤ ⊤)).op
      (schemeGlobalConstants f c) s
    exact (congrArg ((α.tensorPower k).coefficients (𝟙 _)) h).trans
      (((α.tensorPower k).coefficients (𝟙 _)).map_smul _ _)
  rw [hco, schemeOpenRegularFunction_mul f n E U _ _ hp, map_mul, mul_assoc]
  congr 2
  rw [schemeOpenRegularFunction_apply f n E U _ p hp]
  have hg := TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE (le_top : U ≤ ⊤))
    (schemeComplexPointImage f p) hp (schemeGlobalConstants f c)
  erw [hg]
  exact schemeNativeStalkGerm_eval_const f n p c

/-- On a projective scheme every `|s|²_{h^k}` is bounded. -/
theorem exists_sectionNormSq_le (a : LineBundleAtlas L) (k : ℕ) (s : SectionSpace f L k) :
    ∃ M : ℝ, 0 < M ∧ ∀ p, H.sectionNormSq a k s p ≤ M := by
  let := E.isSeparated
  let := E.quasiCompact
  let := E.analyticCompact
  have hcont : Continuous (H.sectionNormSq a k s) :=
    ProductTestForms.ChartSmooth.continuous (H.sectionNormSq_chartSmooth a k s)
  obtain ⟨M, hM⟩ := (isCompact_range hcont).bddAbove
  exact ⟨max M 1, lt_of_lt_of_le one_pos (le_max_right _ _),
    fun p => (hM ⟨p, rfl⟩).trans (le_max_left _ _)⟩

/-- Every nonzero section has a nonzero multiple `c s` with `|c s|²_{h^k} ≤ 1`. -/
theorem exists_normalized (a : LineBundleAtlas L) (k : ℕ) (s : SectionSpace f L k)
    (hs : s ≠ 0) : ∃ c : ℂ, c ≠ 0 ∧ (c • s : SectionSpace f L k) ≠ 0 ∧
      ∀ p, H.sectionNormSq a k (c • s : SectionSpace f L k) p ≤ 1 := by
  obtain ⟨M, hM, hle⟩ := H.exists_sectionNormSq_le a k s
  refine ⟨((Real.sqrt M)⁻¹ : ℝ), ?_, ?_, fun p => ?_⟩
  · exact_mod_cast (inv_pos.mpr (Real.sqrt_pos.mpr hM)).ne'
  · exact smul_ne_zero (by exact_mod_cast (inv_pos.mpr (Real.sqrt_pos.mpr hM)).ne') hs
  · rw [H.sectionNormSq_smul a k, Complex.normSq_ofReal, ← mul_inv, Real.mul_self_sqrt hM.le]
    rw [inv_mul_le_iff₀ hM, mul_one]
    exact hle p

end SGPT.Okounkov.SchemeLineBundleMetric

namespace SGPT.LineBundle

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Filter Set SGPT.Okounkov
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending

variable {X : Scheme} {f : X ⟶ Spec (.of ℂ)} {n : ℕ} [SmoothOfRelativeDimension n f]
  {E : ClosedProjectiveEmbedding f}

local instance potPointTopology'' : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance potPointCharts'' : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f n
local instance potPointManifold'' [IsSeparated f] [QuasiCompact f] :
    IsComplexManifold n (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f n

namespace SectionFiltration

variable {L : X.Modules} {a : LineBundleAtlas L}

/-- The sections `s ∈ 𝓕^{kτ}_k` with `|s|²_{h^k} ≤ 1` (source `ex:RWN`). -/
def normalizedSections (F : SectionFiltration f a) (H : SchemeLineBundleMetric f n E L)
    (k : ℕ) (τ : ℝ) : Set (SectionSpace f L k) :=
  {s | s ∈ F.piece ((k : ℝ) * τ) k ∧ ∀ p, H.sectionNormSq a k s p ≤ 1}

/-- Source `ex:RWN`:
`Γ^{𝓕,k}_τ = usc sup {log |s|²_{h^k} : s ∈ 𝓕^{kτ}_k, |s|²_{h^k} ≤ 1}`. -/
def sectionPotential (F : SectionFiltration f a) (H : SchemeLineBundleMetric f n E L)
    (k : ℕ) (τ : ℝ) : SchemeComplexPoint f → EReal :=
  SGPT.PSH.uscSup fun s : F.normalizedSections H k τ => H.sectionLogNormSq a k s.1

/-- `Γ^{𝓕,k}_τ ≤ 0`. -/
theorem sectionPotential_le_zero (F : SectionFiltration f a) (H : SchemeLineBundleMetric f n E L)
    (k : ℕ) (τ : ℝ) : F.sectionPotential H k τ ≤ 0 := by
  have h : (fun x => ⨆ s : F.normalizedSections H k τ, H.sectionLogNormSq a k s.1 x) ≤
      fun _ => (0 : EReal) := fun x => iSup_le fun s => by
    change ENNReal.log (ENNReal.ofReal (H.sectionNormSq a k s.1 x)) ≤ 0
    rw [ENNReal.log_le_zero_iff]
    exact ENNReal.ofReal_le_one.mpr (s.2.2 x)
  intro x
  have := uscRegularization_mono h x
  rwa [uscRegularization_const] at this

/-- Source `ex:RWN`: `Γ^{𝓕,k}_τ ∈ PSH(X, kθ)` whenever `kτ ≤ τ_k(𝓕)` (and `k > 0`), where
`θ = c₁(L, h)`. -/
theorem isThetaPshPotential_sectionPotential [IsIntegral X] (F : SectionFiltration f a)
    (H : SchemeLineBundleMetric f n E L) {k : ℕ} {τ : ℝ}
    (hτ : (((k : ℝ) * τ : ℝ) : EReal) ≤ F.jump k) :
    letI := E.isSeparated
    letI := E.quasiCompact
    IsThetaPshPotential ((k : ℝ) • H.curvature a).val (F.sectionPotential H k τ) := by
  let := E.isSeparated
  let := E.quasiCompact
  have := SectionSpace.finiteDimensional f E a k
  have hne : F.piece ((k : ℝ) * τ) k ≠ ⊥ := (F.piece_ne_bot_iff _).mpr hτ
  obtain ⟨s₀, hs₀, hs₀0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  obtain ⟨c, _, hc0, hcle⟩ := H.exists_normalized a k s₀ hs₀0
  let J := {s : F.normalizedSections H k τ // s.1 ≠ 0}
  have hJ : Nonempty J :=
    ⟨⟨⟨c • s₀, (F.piece ((k : ℝ) * τ) k).smul_mem c hs₀, hcle⟩, hc0⟩⟩
  have hsup : (fun x => ⨆ s : F.normalizedSections H k τ, H.sectionLogNormSq a k s.1 x) =
      fun x => ⨆ j : J, H.sectionLogNormSq a k j.1.1 x := by
    funext x
    apply le_antisymm
    · refine iSup_le fun s => ?_
      by_cases h0 : s.1 = 0
      · have h := H.sectionLogNormSq_zero a k
        change H.sectionLogNormSq a k s.1 x ≤ _
        rw [h0]
        rw [show H.sectionLogNormSq a k (0 : bundlePowerGlobalSections L k) x = ⊥ from
          congrFun h x]
        exact bot_le
      · exact le_iSup_of_le (⟨s, h0⟩ : J) le_rfl
    · exact iSup_le fun j => le_iSup_of_le j.1 le_rfl
  change IsThetaPshPotential _ (uscRegularization fun x =>
    ⨆ s : F.normalizedSections H k τ, H.sectionLogNormSq a k s.1 x)
  rw [hsup]
  refine SubgeodesicSupremumInterior.isThetaPshPotential_uscRegularization_iSup
    (fun j : J => H.isThetaPshPotential_sectionLogNormSq a k j.1.1 j.2) (C := 0) ?_
  intro j x
  change ENNReal.log (ENNReal.ofReal (H.sectionNormSq a k j.1.1 x)) ≤ ((0 : ℝ) : EReal)
  rw [EReal.coe_zero, ENNReal.log_le_zero_iff]
  exact ENNReal.ofReal_le_one.mpr (j.1.2.2 x)

end SectionFiltration

end SGPT.LineBundle
