import SGPT.PSH.HermitianProductsConvolutionResidual
import SGPT.Foundations.Analysis.Pending.HolomorphicPullback

/-!
# Decreasing approximation by the same actual radial kernels

The existing radial-kernel construction already proves smoothness,
plurisubharmonicity, monotonicity, and almost-everywhere convergence. This
module keeps the raw kernel system visible while upgrading convergence to
every point of the original PSH representative.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.HermitianProducts

open Set Filter Metric MeasureTheory TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open FirstPass.MongeAmpere StronglyPositiveForms LocalProductCurrents
  LocalBedfordTaylorProducts LocalBedfordTaylorForms TopDegreeDensity
  LocalBedfordTaylorSmoothProductDensity
open scoped Topology Distributions ContDiff

variable {n : ℕ} {U V : Opens (ComplexModel n)}

/-- A visible actual radial convolution system gives the genuine pointwise
decreasing smooth PSH approximation. The functions remain the literal scalar
pairings used in the coefficient-current identities. -/
theorem radialSystem_isDecreasingApproximation
    {K : Set (ComplexModel n)} {p : ComplexModel n → ℝ} {R : ℝ}
    (hp : IsLocallyBoundedPshOn U p) (hVU : V ≤ U)
    (S : RadialConvolutionSystem V K p R) (hK : IsCompact K) (hKU : K ⊆ U) :
    IsDecreasingApproximation V p
      (fun j => translationPairing volume (K.indicator p) (S.kernel j)) := by
  have hpL := locallyIntegrableOn_of_plurisubharmonicOn_real hp.1
  have hpLevi : HasNonnegativeDistributionalLevi (regularDistribution volume p hpL) :=
    hasNonnegativeDistributionalLevi_of_plurisubharmonicOn_real hp.1
  have hg : LocallyIntegrable (K.indicator p) volume :=
    (integrable_indicator_of_locallyIntegrableOn_isCompact hpL hK hKU).locallyIntegrable
  have hfPsh (j : ℕ) : PlurisubharmonicOn
      (fun x => (translationPairing volume (K.indicator p) (S.kernel j) x : EReal)) V :=
    (discPshOn_translationPairing_indicator hpL hpLevi
      (S.kernel_hasCompactSupport j) (S.kernel_contDiff j)
      (S.kernel_nonneg j) hK hKU (S.translated_tsupport j)).plurisubharmonicOn V.isOpen
  have hfSmooth (j : ℕ) : IsSmoothPshOn V
      (translationPairing volume (K.indicator p) (S.kernel j)) :=
    isSmoothPshOn_of_psh
      (contDiff_translationPairing hg (S.kernel_hasCompactSupport j)
        (S.kernel_contDiff j)).contDiffOn (hfPsh j)
  exact ⟨hfSmooth, S.antitone_pairing,
    tendsto_everywhere_of_ae_of_antitone_psh (hp.1.mono hVU) hfPsh
      S.antitone_pairing S.ae_tendsto_pairing⟩

/-- The original outer domain and relatively compact inner domain produce
one geometric buffer and actual radial systems for every given locally
bounded PSH function. Every slot uses the same explicit kernel profile. -/
theorem exists_common_radial_systems {ι : Type*} {A : Opens (ComplexModel n)}
    (hA : RelativelyCompactIn A U) (p : ι → ComplexModel n → ℝ)
    (hp : ∀ i, IsLocallyBoundedPshOn U (p i)) :
    ∃ (R : ℝ) (hR : 0 < R) (V : Opens (ComplexModel n)) (K : Set (ComplexModel n)),
      A ≤ V ∧ V ≤ U ∧ IsCompact K ∧ K ⊆ U ∧ (V : Set (ComplexModel n)) ⊆ K ∧
      ∃ S : (i : ι) → RadialConvolutionSystem V K (p i) R,
        ∀ i j z, (S i).kernel j z = HolomorphicPullback.explicitRadialKernel R hR j z := by
  classical
  let _ : ProperSpace (ComplexModel n) := FiniteDimensional.proper ℝ _
  obtain ⟨R, hR, N, K, hN, hclAN, hNK, hK, hKU, hball⟩ :=
    exists_open_compact_closedBall_neighborhood hA.1 U.isOpen hA.2
  let V : Opens (ComplexModel n) := ⟨N, hN⟩
  have hAV : A ≤ V := subset_closure.trans hclAN
  have hVU : V ≤ U := hNK.trans hKU
  have hsys : ∀ i, ∃ S : RadialConvolutionSystem V K (p i) R,
      ∀ j z, S.kernel j z = HolomorphicPullback.explicitRadialKernel R hR j z := by
    intro i
    exact HolomorphicPullback.exists_explicitRadialConvolutionSystem_of_locallyBoundedPsh
      (hp i) hR hN hVU hK hKU hball
  choose S hS using hsys
  exact ⟨R, hR, V, K, hAV, hVU, hK, hKU, hNK, S, hS⟩

/-- The actual exterior product of semipositive real two-forms is strongly
positive, including the empty product. -/
theorem wedgeProd_mem_spCone : ∀ (p : ℕ) (α : Fin p → RealForm n 2),
    (∀ i, IsSemipositiveOneOne (α i)) → wedgeProd p α ∈ spCone p
  | 0, _, _ => unit_mem_spCone
  | p + 1, α, hα => by
    rw [wedgeProd_succ]
    exact wedge_mem_spCone
      (wedgeProd_mem_spCone p (Fin.init α) (fun i => hα i.castSucc)) (hα (Fin.last p))

/-- A fixed positive current wedged with an actual smooth product of
semipositive forms is positive. No closedness of these forms is needed. -/
theorem isPositive_wedgeForm_smooth_product {p r m : ℕ} (h : r + p = m)
    {T : LocalProductCurrent n U m} (hT : IsPositive T)
    (α : Fin p → ComplexModel n → RealForm n 2)
    (hα : ∀ i, ContDiffOn ℝ ∞ (α i) U)
    (hpositive : ∀ i z, z ∈ U → IsSemipositiveOneOne (α i z)) :
    IsPositive (wedgeForm h T (contDiffOn_wedgeProd p α hα)) :=
  isPositive_wedgeForm h hT _ (fun z hz => wedgeProd_mem_spCone p _ (fun i => hpositive i z hz))

end SGPT.PSH.HermitianProducts
