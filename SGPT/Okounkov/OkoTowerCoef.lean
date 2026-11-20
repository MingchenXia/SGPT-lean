import SGPT.Okounkov.OkoTowerSections
import SGPT.Trace.RestVolFrames
import SGPT.GAGA.OkoCloseFamily
import SGPT.GAGA.H0LDXMain
import SGPT.Okounkov.TranscendentalRelGenDescent
import SGPT.TestCurve.GlobalSkodaGauge
import SGPT.Foundations.Analysis.Pending.BlowupFunctionTransform

/-!
# Holomorphic sections of the pulled-back bundle descend to algebraic sections

Source: chapter *The theory of Okounkov bodies*, `prop:birinvO`, which reads the section spaces of
`(π^*L, π^*h)` on a modification `π : Z → X` as sections of `L` (`π_* 𝒪_Z = 𝒪_X`).

Setting: `X` an integral smooth projective complex scheme of dimension `m + 1`, `L` a line bundle
with atlas `a` and smooth metric `H`, `(L, H)^an` its Hermitian holomorphic line bundle on `X(ℂ)`
(`SGPT.NAPotential.GAGAMult.schemeHermitianLineBundle`), `π : Z → X(ℂ)` an analytic modification,
`π^*(L, H)^an = towerBundle` (`SGPT.Trace.RestVol.restrictBundle`).

* `towerCoef t i`: the coefficient on `π⁻¹(Vᵢ)` of a holomorphic section `t` of
  `(π^*L)^k ⊗ π^*𝒪` in the pulled-back frame `(π^*αᵢ)^k`; it transforms like the coefficients of
  a section of `L^k` (`towerCoef_transition`).
* Holomorphic functions on `π⁻¹(Vᵢ)` descend to `Vᵢ(ℂ)`
  (`SGPT.Okounkov.TranscendentalRelGen.exists_holomorphic_descent`); the descended coefficients
  form a holomorphic coefficient family, hence (GAGA,
  `SGPT.GAGA.OkoClose.exists_section_of_isHolomorphicCoefficientFamily`) are the coefficients of an
  algebraic section `towerSection t ∈ H⁰(X, L^k)` with `π^*(towerSection t) = t`
  (`sectionFrameCoefficient_towerSection`).
* **`isPullbackMultiplierSection_towerSection`**: if `t ∈ H⁰(Z, π^*L^k ⊗ 𝓘(k π^*φ))` then
  `π^*(towerSection t) ∈ H⁰(Z, π^*L^k ⊗ 𝓘(k π^*φ))` in the sense of
  `IsPullbackMultiplierSection` (all algebraic frames).
* **`finrank_literal_le_pullbackMultiplier`**: `t ↦ towerSection t` is linear and injective, so
  `dim H⁰(Z, π^*L^k ⊗ 𝓘(k π^*φ))` (the literal analytic section space of `def:Bergman:L778` on `Z`)
  is at most the dimension of `pullbackMultiplierSubmodule`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

noncomputable section

namespace SGPT.Okounkov.OkoTower

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Set Filter
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending.AnalyticModificationLocalDiscrepancy
open SGPT.Okounkov SGPT.LineBundle SGPT.NAPotential.GAGAMult SGPT.GAGA.H0L SGPT.GAGA.OkoClose
open SGPT.Trace.RestVol SGPT.IGood.DXLow2
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.TensorDictionaryDraft.HermitianHolomorphicLineBundle
open SGPT.Bergman.MultiplierSectionsDraft SGPT.Bergman.CompactHolomorphicSectionsDraft
open SGPT.Bergman.QuantizationDraft
open scoped Topology Manifold ContDiff

variable {X : Scheme.{0}} {f : X ⟶ Spec (.of ℂ)} {E : ClosedProjectiveEmbedding f} {m : ℕ}
  [SmoothOfRelativeDimension (m + 1) f] [IsSeparated f] [QuasiCompact f]

local instance okoTowerCoefTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance okoTowerCoefCharts : ChartedSpace (ComplexModel (m + 1)) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f (m + 1)
local instance okoTowerCoefManifold : IsComplexManifold (m + 1) (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f (m + 1)

variable {L : X.Modules} (a : LineBundleAtlas L) (H : SchemeLineBundleMetric f (m + 1) E L)
  {Z : Type} [TopologicalSpace Z] [ChartedSpace (ComplexModel (m + 1)) Z]
  [IsComplexManifold (m + 1) Z]
  {π : Z → SchemeComplexPoint f} (hπ : IsAnalyticModification (n := m + 1) π)

/-! ### Coefficients in the pulled-back frames -/

/-- The modification as a holomorphic map. -/
def towerMap : ContMDiffMap 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel (m + 1)) Z
    (SchemeComplexPoint f) ∞ :=
  ⟨π, hπ.1⟩

/-- `π^*(L, H)^an`. -/
abbrev towerBundle : HermitianHolomorphicLineBundle.{0, 0} (m + 1) Z :=
  restrictBundle (schemeHermitianLineBundle f (m + 1) E a H) (towerMap hπ)

/-- `π^*𝒪` (the trivial bundle). -/
abbrev towerUnit : HermitianHolomorphicLineBundle.{0, 0} (m + 1) Z :=
  restrictBundle (unit (n := m + 1) (M := SchemeComplexPoint f)) (towerMap hπ)

/-- The pulled-back frame `(π^*αᵢ)^k ⊗ π^*1` of `(π^*L)^k ⊗ π^*𝒪`. -/
def towerFrame (i : a.I) (k : ℕ) : AtlasFrame (twistedPower (towerBundle a H hπ) (towerUnit hπ) k) :=
  twistedPowerAtlasFrame (pullFrame (towerMap hπ) (schemeHermitianAtlasFrame f (m + 1) E a H (a.frame i)))
    (pullFrame (towerMap hπ) unitAtlasFrame) k

theorem mem_towerFrame_baseSet (i : a.I) (k : ℕ) {z : Z}
    (hz : schemeComplexPointImage f (π z) ∈ a.opens i) :
    z ∈ (towerFrame a H hπ i k).val.baseSet :=
  twistedPowerAtlasFrame_mem _ _ (mem_pullFrame_baseSet (towerMap hπ) _ hz)
    (mem_pullFrame_baseSet (towerMap hπ) _ (Set.mem_univ _)) k

/-- The coefficient of a section `t` of `(π^*L)^k ⊗ π^*𝒪` in the frame `(π^*αᵢ)^k`. -/
def towerCoef {k : ℕ} (t : twistedSections (towerBundle a H hπ) (towerUnit hπ) k) (i : a.I) :
    Z → ℂ :=
  sectionCoefficient _ (towerFrame a H hπ i k).val t

theorem towerCoef_eq_frameCoord {k : ℕ} (t : twistedSections (towerBundle a H hπ) (towerUnit hπ) k)
    (i : a.I) {z : Z} (hz : schemeComplexPointImage f (π z) ∈ a.opens i) :
    towerCoef a H hπ t i z = frameCoord (towerFrame a H hπ i k) z (t z) :=
  (frameCoord_apply _ (mem_towerFrame_baseSet a H hπ i k hz) (t z)).symm

/-- The coefficient in the pulled-back frame is the coefficient of the fibre vector in the frame
`αᵢ^k` of `L^k` at `π(z)`. -/
theorem towerCoef_eq_twistedFrame {k : ℕ}
    (t : twistedSections (towerBundle a H hπ) (towerUnit hπ) k)
    (i : a.I) {z : Z} (hz : schemeComplexPointImage f (π z) ∈ a.opens i) :
    towerCoef a H hπ t i z = frameCoord (twistedFrame f (m + 1) E a H (a.frame i) k) (π z)
      (twistedFiberEquiv (towerMap hπ) (schemeHermitianLineBundle f (m + 1) E a H) unit z k
        (t z)) := by
  rw [towerCoef_eq_frameCoord a H hπ t i hz]
  exact twistedPowerAtlasFrame_pull_coord (towerMap hπ) _ _ hz (Set.mem_univ _) k (t z)

/-- **Transition of the frame coordinates of `L^k`**: `c_l = g_{il}^k cᵢ` for every fibre
vector. -/
theorem frameCoord_twistedFrame_transition {k : ℕ} (i l : a.I) {p : SchemeComplexPoint f}
    (hpi : schemeComplexPointImage f p ∈ a.opens i) (hpl : schemeComplexPointImage f p ∈ a.opens l)
    (w : (twistedPower (schemeHermitianLineBundle f (m + 1) E a H) unit k).Fiber p) :
    frameCoord (twistedFrame f (m + 1) E a H (a.frame l) k) p w =
      schemeFrameTransition f (m + 1) E (a.frame i) (a.frame l) p ^ k *
        frameCoord (twistedFrame f (m + 1) E a H (a.frame i) k) p w := by
  set e := twistedFrame f (m + 1) E a H (a.frame i) k
  set e' := twistedFrame f (m + 1) E a H (a.frame l) k
  have he : p ∈ e.val.baseSet := mem_twistedFrame_baseSet f (m + 1) E a H _ k hpi
  have he' : p ∈ e'.val.baseSet := mem_twistedFrame_baseSet f (m + 1) E a H _ k hpl
  have htr := twistedPower_frame_transition
    (schemeHermitianAtlasFrame f (m + 1) E a H (a.frame i))
    (schemeHermitianAtlasFrame f (m + 1) E a H (a.frame l))
    (unitAtlasFrame (n := m + 1) (M := SchemeComplexPoint f)) unitAtlasFrame
    (x := p) hpi hpl (Set.mem_univ p) (Set.mem_univ p) k
  have hu : ((unitAtlasFrame (n := m + 1) (M := SchemeComplexPoint f)).val.coordChangeL ℂ
      unitAtlasFrame.val p) 1 = 1 := by
    change ((Bundle.Trivial.trivialization (SchemeComplexPoint f) ℂ).coordChangeL ℂ
      (Bundle.Trivial.trivialization (SchemeComplexPoint f) ℂ) p) 1 = 1
    rw [Bundle.Trivial.trivialization.coordChangeL]
    rfl
  rw [hu, mul_one, coordChangeL_schemeHermitianAtlasFrame' a H _ _ hpi hpl] at htr
  rw [frameCoord_apply e' he', frameCoord_apply e he]
  have hs : w = e.val.symm p ((e.val ⟨p, w⟩).2) := (e.val.symm_apply_apply_mk he w).symm
  conv_lhs => rw [hs]
  rw [← Bundle.Trivialization.coordChangeL_apply (R := ℂ) e.val e'.val ⟨he, he'⟩]
  have hlin : (e.val.coordChangeL ℂ e'.val p) ((e.val ⟨p, w⟩).2) =
      (e.val ⟨p, w⟩).2 * (e.val.coordChangeL ℂ e'.val p) 1 := by
    rw [← smul_eq_mul, ← map_smul, smul_eq_mul, mul_one]
  rw [hlin]
  change _ * ((twistedPowerAtlasFrame _ _ k).val.coordChangeL ℂ
    (twistedPowerAtlasFrame _ _ k).val p) 1 = _
  rw [htr, mul_comm]

/-- **Transition of the pulled-back coefficients**: `c_l = (g_{il} ∘ π)^k cᵢ` on
`π⁻¹(Vᵢ ∩ V_l)`. -/
theorem towerCoef_transition {k : ℕ} (t : twistedSections (towerBundle a H hπ) (towerUnit hπ) k)
    (i l : a.I) {z : Z} (hzi : schemeComplexPointImage f (π z) ∈ a.opens i)
    (hzl : schemeComplexPointImage f (π z) ∈ a.opens l) :
    towerCoef a H hπ t l z =
      schemeFrameTransition f (m + 1) E (a.frame i) (a.frame l) (π z) ^ k *
        towerCoef a H hπ t i z := by
  rw [towerCoef_eq_twistedFrame a H hπ t l hzl, towerCoef_eq_twistedFrame a H hπ t i hzi]
  exact frameCoord_twistedFrame_transition a H i l hzi hzl _

theorem towerCoef_holomorphicAt {k : ℕ}
    (t : twistedSections (towerBundle a H hπ) (towerUnit hπ) k) (i : a.I) {z : Z}
    (hz : schemeComplexPointImage f (π z) ∈ a.opens i) :
    HolomorphicAt (m + 1) (towerCoef a H hπ t i) z :=
  originalSectionCoefficient_holomorphicAt (n := m + 1) _
    ⟨(towerFrame a H hπ i k).val, (towerFrame a H hπ i k).property⟩ t
    (mem_towerFrame_baseSet a H hπ i k hz)

theorem towerCoef_add {k : ℕ} (t t' : twistedSections (towerBundle a H hπ) (towerUnit hπ) k)
    (i : a.I) {z : Z} (hz : schemeComplexPointImage f (π z) ∈ a.opens i) :
    towerCoef a H hπ (t + t') i z = towerCoef a H hπ t i z + towerCoef a H hπ t' i z := by
  rw [towerCoef_eq_frameCoord a H hπ _ i hz, towerCoef_eq_frameCoord a H hπ _ i hz,
    towerCoef_eq_frameCoord a H hπ _ i hz]
  change frameCoord _ z (t z + t' z) = _
  rw [map_add]

theorem towerCoef_smul {k : ℕ} (c : ℂ) (t : twistedSections (towerBundle a H hπ) (towerUnit hπ) k)
    (i : a.I) {z : Z} (hz : schemeComplexPointImage f (π z) ∈ a.opens i) :
    towerCoef a H hπ (c • t) i z = c * towerCoef a H hπ t i z := by
  rw [towerCoef_eq_frameCoord a H hπ _ i hz, towerCoef_eq_frameCoord a H hπ _ i hz]
  change frameCoord _ z (c • t z) = _
  rw [map_smul, smul_eq_mul]

/-! ### Descent of the coefficients -/

theorem isOpen_frameDomain (i : a.I) : IsOpen (schemeComplexPointImage f ⁻¹' (a.opens i : Set X)) :=
  (a.opens i).isOpen.preimage (schemeComplexPointImage_continuous f)

theorem exists_towerCoef_descent {k : ℕ}
    (t : twistedSections (towerBundle a H hπ) (towerUnit hπ) k) (i : a.I) :
    ∃ d : SchemeComplexPoint f → ℂ,
      MDifferentiableOn 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ℂ) d
        (schemeComplexPointImage f ⁻¹' (a.opens i : Set X)) ∧
      ∀ z ∈ π ⁻¹' (schemeComplexPointImage f ⁻¹' (a.opens i : Set X)),
        d (π z) = towerCoef a H hπ t i z :=
  SGPT.Okounkov.TranscendentalRelGen.exists_holomorphic_descent hπ (isOpen_frameDomain a i)
    fun _ hz => (towerCoef_holomorphicAt a H hπ t i hz).self_of_nhds.mdifferentiableWithinAt

/-- The descended coefficient `dᵢ` on `Vᵢ(ℂ)`, `dᵢ ∘ π = cᵢ`. -/
def towerDescent {k : ℕ} (t : twistedSections (towerBundle a H hπ) (towerUnit hπ) k) (i : a.I) :
    SchemeComplexPoint f → ℂ :=
  (exists_towerCoef_descent a H hπ t i).choose

theorem towerDescent_comp {k : ℕ} (t : twistedSections (towerBundle a H hπ) (towerUnit hπ) k)
    (i : a.I) {z : Z} (hz : schemeComplexPointImage f (π z) ∈ a.opens i) :
    towerDescent a H hπ t i (π z) = towerCoef a H hπ t i z :=
  (exists_towerCoef_descent a H hπ t i).choose_spec.2 z hz

/-- The descended coefficients form a holomorphic coefficient family of degree `k`. -/
theorem isHolomorphicCoefficientFamily_towerDescent {k : ℕ}
    (t : twistedSections (towerBundle a H hπ) (towerUnit hπ) k) :
    IsHolomorphicCoefficientFamily f E (m + 1) a k (towerDescent a H hπ t) where
  holomorphicAt i p hp := by
    have hd := (exists_towerCoef_descent a H hπ t i).choose_spec.1
    filter_upwards [(isOpen_frameDomain a i).mem_nhds hp] with q hq
    exact hd.mdifferentiableAt ((isOpen_frameDomain a i).mem_nhds hq)
  transition i l p hpi hpl := by
    obtain ⟨z, rfl⟩ :=
      SGPT.Foundations.Analysis.Pending.AnalyticModificationStrongPullback.surjective_of_isAnalyticModification
        hπ p
    rw [towerDescent_comp a H hπ t l hpl, towerDescent_comp a H hπ t i hpi]
    exact towerCoef_transition a H hπ t i l hpi hpl

/-! ### The algebraic section -/

variable [IsIntegral X] [CompactSpace (SchemeComplexPoint f)]

/-- **The algebraic section `s ∈ H⁰(X, L^k)` with `π^*s = t`.** -/
def towerSection {k : ℕ} (t : twistedSections (towerBundle a H hπ) (towerUnit hπ) k) :
    SectionSpace f L k :=
  (exists_section_of_isHolomorphicCoefficientFamily
    (isHolomorphicCoefficientFamily_towerDescent a H hπ t)).choose

theorem sectionFrameCoefficient_towerSection_descent {k : ℕ}
    (t : twistedSections (towerBundle a H hπ) (towerUnit hπ) k) (i : a.I)
    {p : SchemeComplexPoint f} (hp : schemeComplexPointImage f p ∈ a.opens i) :
    sectionFrameCoefficient f (m + 1) E (a.frame i) k (towerSection a H hπ t) p =
      towerDescent a H hπ t i p :=
  (exists_section_of_isHolomorphicCoefficientFamily
    (isHolomorphicCoefficientFamily_towerDescent a H hπ t)).choose_spec i p hp

/-- **`π^*(towerSection t) = t`**: the coefficient of `towerSection t` in `αᵢ^k`, composed with
`π`, is the coefficient of `t` in `(π^*αᵢ)^k`. -/
theorem sectionFrameCoefficient_towerSection {k : ℕ}
    (t : twistedSections (towerBundle a H hπ) (towerUnit hπ) k) (i : a.I) {z : Z}
    (hz : schemeComplexPointImage f (π z) ∈ a.opens i) :
    sectionFrameCoefficient f (m + 1) E (a.frame i) k (towerSection a H hπ t) (π z) =
      towerCoef a H hπ t i z := by
  rw [sectionFrameCoefficient_towerSection_descent a H hπ t i hz, towerDescent_comp a H hπ t i hz]

/-- **Multiplier sections descend to multiplier sections of the pullback**: if
`t ∈ H⁰(Z, π^*L^k ⊗ 𝓘(k π^*φ))`, then `π^*(towerSection t)` lies in it in every algebraic
frame. -/
theorem isPullbackMultiplierSection_towerSection {φ : SchemeComplexPoint f → EReal}
    (hφ : IsGlobalQuasiPshPotential (n := m + 1) (fun w => φ (π w))) {k : ℕ}
    {t : twistedSections (towerBundle a H hπ) (towerUnit hπ) k}
    (ht : t ∈ fullHolomorphicIdealSections (n := m + 1)
      (twistedPower (towerBundle a H hπ) (towerUnit hπ) k).Fiber
      (sourceDegreeMultiplierIdeal (n := m + 1) k (fun w => φ (π w)))) :
    IsPullbackMultiplierSection f E m π φ k (towerSection a H hπ t) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact Or.inl rfl
  right
  intro U α z hz
  obtain ⟨i, hi⟩ := a.covers (schemeComplexPointImage f (π z))
  have hmem := coefficient_mem_of_mem_full (n := m + 1)
    (twistedPower (towerBundle a H hπ) (towerUnit hπ) k).Fiber _
    (sourceDegreeMultiplierIdeal_isCoherent k hφ) ht
    ⟨(towerFrame a H hπ i k).val, (towerFrame a H hπ i k).property⟩
    (mem_towerFrame_baseSet a H hπ i k hi)
  rw [sourceDegreeMultiplierIdeal_pos k hk] at hmem
  have hhol : HolomorphicAt (m + 1)
      (fun w => schemeFrameTransition f (m + 1) E (a.frame i) α (π w) ^ k) z := by
    have h1 := BlowupFunctionTransform.holomorphicAt_pow
      (schemeFrameTransition_holomorphicAt f (m + 1) E (a.frame i) α (π z) hi hz) k
    exact h1.comp_contMDiff (Eventually.of_forall fun _ => hπ.1.contMDiffAt)
  have hmul := MultiplierIdealProductComparison.mem_multiplierIdeal_holomorphic_mul hhol hmem
  refine MultiplierIdealProductComparison.mem_multiplierIdeal_congr hmul ?_
  filter_upwards [preimage_frameDomain_mem_nhds f hπ.1.continuous (a.opens i) hi,
    preimage_frameDomain_mem_nhds f hπ.1.continuous U hz] with w hwi hwU
  rw [SGPT.TestCurve.GlobalSkoda.sectionFrameCoefficient_transition (a.frame i) α k (towerSection a H hπ t) hwi hwU,
    sectionFrameCoefficient_towerSection a H hπ t i hwi]
  rfl

/-- `t ↦ towerSection t` is additive. -/
theorem towerSection_add {k : ℕ} (t t' : twistedSections (towerBundle a H hπ) (towerUnit hπ) k) :
    towerSection a H hπ (t + t') = towerSection a H hπ t + towerSection a H hπ t' := by
  refine eq_of_algCoef_eq (f := f) (E := E) (n := m + 1) a ?_
  intro i p hp
  obtain ⟨z, rfl⟩ :=
    SGPT.Foundations.Analysis.Pending.AnalyticModificationStrongPullback.surjective_of_isAnalyticModification
      hπ p
  have h1 := sectionFrameCoefficient_towerSection a H hπ (t + t') i hp
  have h2 := SGPT.IGood.DXMain.sectionFrameCoefficient_add f (m + 1) E (a.frame i) k
    (towerSection a H hπ t) (towerSection a H hπ t') hp
  change sectionFrameCoefficient f (m + 1) E (a.frame i) k _ (π z) =
    sectionFrameCoefficient f (m + 1) E (a.frame i) k _ (π z)
  rw [h1, h2, sectionFrameCoefficient_towerSection a H hπ t i hp,
    sectionFrameCoefficient_towerSection a H hπ t' i hp, towerCoef_add a H hπ t t' i hp]

/-- `t ↦ towerSection t` is `ℂ`-homogeneous. -/
theorem towerSection_smul {k : ℕ} (c : ℂ)
    (t : twistedSections (towerBundle a H hπ) (towerUnit hπ) k) :
    towerSection a H hπ (c • t) = (c • towerSection a H hπ t : SectionSpace f L k) := by
  refine eq_of_algCoef_eq (f := f) (E := E) (n := m + 1) a ?_
  intro i p hp
  obtain ⟨z, rfl⟩ :=
    SGPT.Foundations.Analysis.Pending.AnalyticModificationStrongPullback.surjective_of_isAnalyticModification
      hπ p
  have h1 := sectionFrameCoefficient_towerSection a H hπ (c • t) i hp
  have h2 := SGPT.IGood.DXMain.sectionFrameCoefficient_smul f (m + 1) E (a.frame i) k c
    (towerSection a H hπ t) hp
  change sectionFrameCoefficient f (m + 1) E (a.frame i) k _ (π z) =
    sectionFrameCoefficient f (m + 1) E (a.frame i) k _ (π z)
  rw [h1, h2, sectionFrameCoefficient_towerSection a H hπ t i hp, towerCoef_smul a H hπ c t i hp]

/-- `towerSection t = 0` only for `t = 0`. -/
theorem eq_zero_of_towerSection_eq_zero {k : ℕ}
    {t : twistedSections (towerBundle a H hπ) (towerUnit hπ) k}
    (h : towerSection a H hπ t = 0) : t = 0 := by
  apply ContMDiffSection.ext
  intro z
  obtain ⟨i, hi⟩ := a.covers (schemeComplexPointImage f (π z))
  have h1 := sectionFrameCoefficient_towerSection a H hπ t i hi
  rw [h, SGPT.IGood.sectionFrameCoefficient_zero (f := f) (n := m + 1) (E := E) _ k hi,
    towerCoef_eq_frameCoord a H hπ t i hi, frameCoord_apply _ (mem_towerFrame_baseSet a H hπ i k hi)]
    at h1
  have hb := mem_towerFrame_baseSet a H hπ i k hi
  rw [ContMDiffSection.coe_zero, Pi.zero_apply]
  have h2 : (towerFrame a H hπ i k).val.continuousLinearEquivAt ℂ z hb (t z) = 0 := by
    rw [Bundle.Trivialization.coe_continuousLinearEquivAt_eq _ hb,
      Bundle.Trivialization.continuousLinearMapAt_apply_of_mem (R := ℂ) (towerFrame a H hπ i k).val hb]
    exact h1.symm
  exact ((towerFrame a H hπ i k).val.continuousLinearEquivAt ℂ z hb).map_eq_zero_iff.mp h2

/-- **The literal section space on `Z` injects into the pullback multiplier sections**:
`dim H⁰(Z, π^*L^k ⊗ 𝓘(k π^*φ)) ≤ dim {s ∈ H⁰(X, L^k) : π^*s ∈ H⁰(Z, π^*L^k ⊗ 𝓘(k π^*φ))}`. -/
theorem finrank_literal_le_pullbackMultiplier {φ : SchemeComplexPoint f → EReal}
    (hφ : IsGlobalQuasiPshPotential (n := m + 1) (fun w => φ (π w))) (k : ℕ) :
    Module.finrank ℂ (LiteralTwistedMultiplierSections (towerBundle a H hπ) (towerUnit hπ) k
      (fun w => φ (π w))) ≤
      Module.finrank ℂ (pullbackMultiplierSubmodule f E hπ.1.continuous hφ.1 L k) := by
  rw [(literalTwistedMultiplierSectionEquiv (towerBundle a H hπ) (towerUnit hπ) k
    (fun w => φ (π w))).finrank_eq]
  let W := fullHolomorphicIdealSections (n := m + 1)
    (twistedPower (towerBundle a H hπ) (towerUnit hπ) k).Fiber
    (sourceDegreeMultiplierIdeal (n := m + 1) k (fun w => φ (π w)))
  let Φ : W →ₗ[ℂ] pullbackMultiplierSubmodule f E hπ.1.continuous hφ.1 L k :=
    { toFun := fun w => ⟨towerSection a H hπ w.val,
        isPullbackMultiplierSection_towerSection a H hπ hφ w.property⟩
      map_add' := fun w w' => Subtype.ext (towerSection_add a H hπ w.val w'.val)
      map_smul' := fun c w => Subtype.ext (towerSection_smul a H hπ c w.val) }
  have : FiniteDimensional ℂ (SectionSpace f L k) := SectionSpace.finiteDimensional f E a k
  refine LinearMap.finrank_le_finrank_of_injective (f := Φ)
    ((injective_iff_map_eq_zero Φ).mpr fun w hw => ?_)
  have h : towerSection a H hπ w.val = 0 := congrArg Subtype.val hw
  exact Subtype.ext (eq_zero_of_towerSection_eq_zero a H hπ h)

/-- **`H⁰(Z, π^*L^k ⊗ 𝓘(k π^*φ)) = π^* {s ∈ H⁰(X, L^k) : π^*s ∈ H⁰(Z, π^*L^k ⊗ 𝓘(k π^*φ))}`**
(`π_* 𝒪_Z = 𝒪_X`): every holomorphic section `t` of `π^*L^k ⊗ 𝓘(k π^*φ)` on `Z` is `π^*s` for a
unique algebraic section `s ∈ H⁰(X, L^k)` (its coefficient in `(π^*αᵢ)^k` is `sᵢ ∘ π`), and this
`s` satisfies `IsPullbackMultiplierSection`.  Hence the section spaces of `Δ_ν(π^*L, π^*h)` are
the ones used in `pullbackMultiplierSectionSet`. -/
theorem existsUnique_section_pullback_eq {φ : SchemeComplexPoint f → EReal}
    (hφ : IsGlobalQuasiPshPotential (n := m + 1) (fun w => φ (π w))) {k : ℕ}
    {t : twistedSections (towerBundle a H hπ) (towerUnit hπ) k}
    (ht : t ∈ fullHolomorphicIdealSections (n := m + 1)
      (twistedPower (towerBundle a H hπ) (towerUnit hπ) k).Fiber
      (sourceDegreeMultiplierIdeal (n := m + 1) k (fun w => φ (π w)))) :
    ∃! s : SectionSpace f L k, IsPullbackMultiplierSection f E m π φ k s ∧
      ∀ (i : a.I) (z : Z), schemeComplexPointImage f (π z) ∈ a.opens i →
        sectionFrameCoefficient f (m + 1) E (a.frame i) k s (π z) = towerCoef a H hπ t i z := by
  refine ⟨towerSection a H hπ t, ⟨isPullbackMultiplierSection_towerSection a H hπ hφ ht,
    fun i z hz => sectionFrameCoefficient_towerSection a H hπ t i hz⟩, ?_⟩
  rintro s ⟨-, hs⟩
  refine eq_of_algCoef_eq (f := f) (E := E) (n := m + 1) a ?_
  intro i p hp
  obtain ⟨z, rfl⟩ :=
    SGPT.Foundations.Analysis.Pending.AnalyticModificationStrongPullback.surjective_of_isAnalyticModification
      hπ p
  change sectionFrameCoefficient f (m + 1) E (a.frame i) k _ (π z) =
    sectionFrameCoefficient f (m + 1) E (a.frame i) k _ (π z)
  rw [hs i z hp, sectionFrameCoefficient_towerSection a H hπ t i hp]

end SGPT.Okounkov.OkoTower

end
