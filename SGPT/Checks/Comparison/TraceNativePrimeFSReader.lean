import SGPT.Checks.Comparison.TraceNativeGenericIdealReader
import SGPT.Checks.Comparison.TraceNativeFSValue
import SGPT.PSH.CompactPrimeOver
import SGPT.Foundations.Analysis.Pending.GlobalPotentialPullback
import SGPT.Foundations.Analysis.Pending.ThetaPshIdentityPrinciple

/-! ORIGINAL physical FS/native divisorial equality, with an ACTUAL ambient
image semi-valuation and SAME original prime reader. No target algebraization.
Blueprint: `trace-native-prime-reader.tex`. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.NAPotential.TraceComparison.NativeImage

open Set Filter AlgebraicGeometry CategoryTheory SGPT.Foundations.Schemes SGPT.Okounkov SGPT.Foundations.Envelope
open SGPT.NAPotential.Berkovich SGPT.NAPotential.BJ SGPT.NAPotential.BJ.GfIm
open SGPT.PSH.CompactPrimeOver SGPT.PSH.VariableComplexAtlas
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.GlobalAnalyticSingularities
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open FixedGermNormalOrder DemaillyApproximantDivisorialLelong
open scoped Topology Manifold ContDiff ENNReal

/-- The unchanged atlas source reader and SAME entire original ideal order. -/
theorem atlasGenericLelong_eq_originalNormalOrder_of_globalAnalyticType
    {m : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (ComplexModel (m+1)) M]
    [IsComplexManifold (m+1) M] {u : M → EReal}
    (hu : IsGlobalQuasiPshPotential (n := m+1) u) {c : ℚ} {A : GermIdeal (m+1) M}
    (htype : HasAnalyticSingularitiesOfType (n := m+1) u c A)
    {E : Set M} (hE : IsClosedConnectedSubmanifold (m+1) E m)
    {y : M} (hy : y ∈ E) (Φ : DivisorFlattening (m := m) E y) :
    (ofFixedModel (m+1) M).sourceGenericLelong u E =
      ENNReal.ofReal (c : ℝ) * (originalStalkNormalOrder Φ A : ℝ≥0∞) := by
  simpa only [sourceGenericLelong, sourceLelong_ofFixedModel_eq,
    SourceGenericSubmanifoldMinimum.sourceGeneric_subtype_eq_iInf] using
    sourceGenericLelong_eq_originalNormalOrder_of_globalAnalyticType hu htype hE hy Φ

variable {X : Scheme.{0}} {L : X.Modules} (f : X ⟶ Spec (.of ℂ)) (n : ℕ)
  [SmoothOfRelativeDimension n f] [IsIntegral X] [IsProjective f]
  (EX : ClosedProjectiveEmbedding f)
local instance tracePrimeFSProper : IsProper f := (ProjectiveFactorizationRingIso.of_isProjective f).isProper
local instance tracePrimeFSTopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance tracePrimeFSCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f n
local instance tracePrimeFSManifold : IsComplexManifold n (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f n

/-- **The BOOK'S original physical FS/native divisorial restriction formula.**
The same actual native prime constructs its ambient image point; the target
is an arbitrary native connected complex manifold. Literal nontriviality
produces genuine PSH and all normal-order/generic-reader dictionaries internally. -/
theorem potentialAn_sectionMaximum_nativePrime_eq
    (a : LineBundleAtlas L) (H : SchemeLineBundleMetric f n EX L) (N K : ℕ) (hK : 0 < K)
    {I : Type} [Fintype I] [Nonempty I] (s : I → bundlePowerGlobalSections L N) (hs : ∀ j, s j ≠ 0)
    {m : ℕ} {V : Type} [TopologicalSpace V] [ChartedSpace (ComplexModel (m+1)) V]
    [IsComplexManifold (m+1) V] [ConnectedSpace V] (ι : V → SchemeComplexPoint f)
    (hι : ContMDiff 𝓘(ℂ, ComplexModel (m+1)) 𝓘(ℂ, ComplexModel n) ∞ ι)
    (hne : ∃ y, (((K : ℝ)⁻¹ : ℝ) : EReal) * sectionsMaxLog f n EX a N s H (ι y) ≠ ⊥)
    (p : PrimePresentation (m+1) V) {z : p.model} (hz : z ∈ p.divisor)
    (Φ : DivisorFlattening (m := m) p.divisor z) (c : ℝ) (hc : 0 < c) :
    potentialAn n EX (fun x => (((K : ℝ)⁻¹ : ℝ) : EReal) * sectionsMaxLog f n EX a N s H x)
      (nativeImagePoint f n (ι ∘ p.projection) (hι.comp p.modification.1) z Φ c hc) =
      -((c : EReal) * ((presentationReader
        (fun y => (((K : ℝ)⁻¹ : ℝ) : EReal) * sectionsMaxLog f n EX a N s H (ι y)) p : ℝ≥0∞) : EReal)) := by
  let φ : SchemeComplexPoint f → EReal := fun x => (((K : ℝ)⁻¹ : ℝ) : EReal) * sectionsMaxLog f n EX a N s H x
  have hφ := SGPT.Okounkov.TranscendentalCore.isThetaPshPotential_nonneg_smul
    (isThetaPshPotential_sectionsMaxLog f n EX a N s H hs)
    (inv_nonneg.mpr (Nat.cast_nonneg (α := ℝ) K))
  let β := ClosedRealOneOneForm.pullback hι (((K : ℝ)⁻¹) • (N : ℝ) • H.curvature a)
  have hV : IsThetaPshPotential β.val (fun y => φ (ι y)) :=
    ThetaPshIdentityPrinciple.isThetaPshPotential_of_exists_ne_bot
      (GlobalPotentialPullback.thetaPlurisubharmonic_comp hι hφ.1) hne
  have hZ := AnalyticModificationStrongPullback.isThetaPshPotential_comp_of_isAnalyticModification
    p.modification β hV
  have htype := normalized_sectionMaximum_nativeRestriction_has_global_actual_ideal_type
    f n EX a H N K hK s (ι ∘ p.projection) (hι.comp p.modification.1)
  have hdim : p.divisorDimension = m := by have hh := p.codimension_one; omega
  have hE : IsClosedConnectedSubmanifold (m+1) p.divisor m := by simpa only [hdim] using p.smooth
  have hread := atlasGenericLelong_eq_originalNormalOrder_of_globalAnalyticType
    hZ.quasiPshPotential htype hE hz Φ
  change presentationReader (fun y => φ (ι y)) p = _ at hread
  rw [potentialAn_sectionMaximum_nativeImagePoint_eq f n EX a H N K hK s hs
    (ι ∘ p.projection) (hι.comp p.modification.1) z Φ c hc]
  rw [hread]
  have hKR : (0 : ℝ) < K := by exact_mod_cast hK
  simp only [Rat.cast_inv, Rat.cast_natCast, ENNReal.ofReal_inv_of_pos hKR,
    ENNReal.ofReal_natCast]
  have hcc : (c : EReal) = ((ENNReal.ofReal c : ℝ≥0∞) : EReal) := by
    rw [EReal.coe_ennreal_ofReal, max_eq_left hc.le]
  rw [hcc, ← EReal.coe_ennreal_mul]
  congr 2
  simp only [div_eq_mul_inv]
  ac_rfl

end SGPT.NAPotential.TraceComparison.NativeImage
