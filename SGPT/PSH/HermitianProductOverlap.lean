import SGPT.PSH.HermitianProductFactors
import SGPT.PSH.HermitianPatchOverlap
import SGPT.PSH.HermitianProductsCovariance
import SGPT.PSH.HermitianProductsCorrectionShift
import SGPT.PSH.HermitianProductsTopTracePullback

/-!
# Actual nonclosed Hermitian products agree on chart overlaps

The background's own tensor law transports its smooth coefficients. The
normalized smooth Hessian commutes with the actual holomorphic transition.
The difference of the two genuine corrections then cancels by the proved
smooth-shift identity. This constructs both current and measure overlap
compatibility from the original bounded Hermitian tuple.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.HermitianGlobalProducts

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ContDiff Distributions Manifold
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.FirstPass.HolomorphicMaps
open SGPT.Foundations.Analysis.Pending
open StronglyPositiveForms LocalProductCurrents LocalBedfordTaylorProducts
  LocalBedfordTaylorLocality LocalBedfordTaylorCollar LocalBedfordTaylorForms
  LocalCurrentPullback LocalCurrentPullbackDdc BedfordTaylor
open Hermitian HermitianProducts

variable {m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]

private theorem restrict_unit {n : ℕ} {U V : Opens (ComplexModel n)}
    (hVU : V ≤ U) {k : ℕ} (hk : k = n) :
    restrict hVU (oneCurrentOf (U := U) hk) = oneCurrentOf (U := V) hk := by
  subst k
  exact LocalCurrentPullbackDdc.restrict_oneCurrent hVU

private theorem pullback_congr_current {n r : ℕ} {A B : Opens (ComplexModel n)}
    {τ ι : ComplexModel n → ComplexModel n} (h : IsBiholomorphicPair A B τ ι)
    {S T : LocalProductCurrent n B r} (hS : IsPositive S) (hT : IsPositive T)
    (heq : S = T) : pullback h hS = pullback h hT := by
  subst T
  rfl

private theorem locallyBoundedPsh_comp {n : ℕ} {A B : Opens (ComplexModel n)}
    {τ ι : ComplexModel n → ComplexModel n} (h : IsBiholomorphicPair A B τ ι)
    {w : ComplexModel n → ℝ} (hw : IsLocallyBoundedPshOn B w) :
    IsLocallyBoundedPshOn A (fun x => w (τ x)) := by
  refine ⟨HolomorphicPullback.plurisubharmonicOn_comp_holomorphic
    (u := fun z => (w z : EReal)) A.isOpen
    (h.holo.differentiableOn (by simp)) h.mapsTo hw.1, fun z hz => ?_⟩
  obtain ⟨V, hzV, hVB, C, hC⟩ := hw.2 (τ z) (h.mapsTo hz)
  exact ⟨preOpen h V, ⟨hz, hzV⟩, preOpen_le h V, C, fun x hx => hC (τ x) hx.2⟩

private theorem locallyBoundedPsh_congr {n : ℕ} {U : Opens (ComplexModel n)}
    {v w : ComplexModel n → ℝ} (hv : IsLocallyBoundedPshOn U v) (heq : EqOn v w U) :
    IsLocallyBoundedPshOn U w := by
  refine ⟨fun z hz => (hv.1 z hz).congr ?_, ?_⟩
  · filter_upwards [U.isOpen.mem_nhds hz] with y hy
    exact congrArg (fun a : ℝ => (a : EReal)) (heq hy)
  · intro z hz
    obtain ⟨V, hzV, hVU, C, hC⟩ := hv.2 z hz
    exact ⟨V, hzV, hVU, C, fun y hy => (heq (hVU hy)) ▸ hC y hy⟩

namespace BackgroundPatch

variable {omega : Background (m + 1) M}

/-- Actual unit-base mixed currents commute with open restriction. -/
theorem mixedCurrent_restrict (P : BackgroundPatch omega) (p : ℕ) (hp : p ≤ m + 1)
    (u : Fin p → M → EReal) (hu : ∀ i, IsHermitianPSH omega (u i))
    (hb : ∀ i, ∃ a b : ℝ, ∀ x, (a : EReal) ≤ u i x ∧ u i x ≤ (b : EReal))
    {V : Opens (ComplexModel (m + 1))} (hVP : V ≤ P.geometry.domain) :
    restrict hVP (P.mixedCurrent p hp u) =
      backgroundExpansion p (m + 1 - p) (fun i => P.correctedReal (u i))
        (P.residual_smooth.mono hVP)
        (oneCurrentOf (U := V) (Nat.sub_add_cancel hp)) := by
  rw [mixedCurrent, backgroundExpansion_restrict hVP p (m + 1 - p) _
    (isPositive_oneCurrentOf _) (isClosedAny_oneCurrentOf _)
    (fun i => P.correctedReal (u i))
    (fun i => P.correctedReal_isLocallyBoundedPshOn (hu i) (hb i)) P.residual_smooth,
    restrict_unit hVP]

/-- The original local factor positivity persists on every open subdomain. -/
theorem factor_isPositive_on (P : BackgroundPatch omega)
    {u : M → EReal} (hu : IsHermitianPSH omega u)
    (hb : ∃ a b : ℝ, ∀ x, (a : EReal) ≤ u x ∧ u x ≤ (b : EReal))
    {V : Opens (ComplexModel (m + 1))} (hVP : V ≤ P.geometry.domain) :
    IsPositive (ddcMul (oneCurrent V) (P.correctedReal u) +
      wedgeForm rfl (oneCurrent V) (P.residual_smooth.mono hVP)) := by
  have hpos := isPositive_restrict (P.factor_isPositive hu hb) hVP
  change IsPositive (restrict hVP (ddcMul (oneCurrent P.geometry.domain) (P.correctedReal u)) +
    restrict hVP (wedgeForm rfl (oneCurrent P.geometry.domain) P.residual_smooth)) at hpos
  rw [← ddcMul_restrict isPositive_oneCurrent hVP (P.correctedReal_isLocallyBoundedPshOn hu hb),
    wedgeForm_restrict hVP, LocalCurrentPullbackDdc.restrict_oneCurrent hVP] at hpos
  exact hpos

/-- The original unit-base expansion at any explicitly supplied product
and complementary bidimension. -/
def currentOfDegree (P : BackgroundPatch omega) (p r : ℕ) (hdeg : r + p = m + 1)
    (u : Fin p → M → EReal) : LocalProductCurrent (m + 1) P.geometry.domain r :=
  backgroundExpansion p r (fun i => P.correctedReal (u i)) P.residual_smooth
    (oneCurrentOf (U := P.geometry.domain) hdeg)

/-- Its positivity is produced from original bounded Hermitian potentials. -/
theorem currentOfDegree_isPositive (P : BackgroundPatch omega) (p r : ℕ)
    (hdeg : r + p = m + 1) (u : Fin p → M → EReal)
    (hu : ∀ i, IsHermitianPSH omega (u i))
    (hb : ∀ i, ∃ a b : ℝ, ∀ x, (a : EReal) ≤ u i x ∧ u i x ≤ (b : EReal)) :
    IsPositive (P.currentOfDegree p r hdeg u) :=
  isPositive_backgroundExpansion p r _ (isPositive_oneCurrentOf _) (isClosedAny_oneCurrentOf _)
    _ (fun i => P.correctedReal_isLocallyBoundedPshOn (hu i) (hb i))
    P.residual_smooth P.residual_isOneOne (fun i => P.factor_isPositive (hu i) (hb i))

/-- Literal open restriction in every explicitly supplied degree. -/
theorem currentOfDegree_restrict (P : BackgroundPatch omega) (p r : ℕ)
    (hdeg : r + p = m + 1) (u : Fin p → M → EReal)
    (hu : ∀ i, IsHermitianPSH omega (u i))
    (hb : ∀ i, ∃ a b : ℝ, ∀ x, (a : EReal) ≤ u i x ∧ u i x ≤ (b : EReal))
    {V : Opens (ComplexModel (m + 1))} (hVP : V ≤ P.geometry.domain) :
    restrict hVP (P.currentOfDegree p r hdeg u) =
      backgroundExpansion p r (fun i => P.correctedReal (u i))
        (P.residual_smooth.mono hVP) (oneCurrentOf (U := V) hdeg) := by
  rw [currentOfDegree, backgroundExpansion_restrict hVP p r _
    (isPositive_oneCurrentOf _) (isClosedAny_oneCurrentOf _)
    (fun i => P.correctedReal (u i))
    (fun i => P.correctedReal_isLocallyBoundedPshOn (hu i) (hb i)) P.residual_smooth,
    restrict_unit hVP]

/-- Actual bounded mixed currents satisfy holomorphic descent on every
pair of correction patches. Both corrections and the transported smooth
residual are handled internally. -/
theorem currentOfDegree_overlap (P Q : BackgroundPatch omega) (p r : ℕ) (hdeg : r + p = m + 1)
    (u : Fin p → M → EReal) (hu : ∀ i, IsHermitianPSH omega (u i))
    (hb : ∀ i, ∃ a b : ℝ, ∀ x, (a : EReal) ≤ u i x ∧ u i x ≤ (b : EReal)) :
    pullback (P.geometry.isBiholomorphicPair Q.geometry)
      (isPositive_restrict (Q.currentOfDegree_isPositive p r hdeg u hu hb)
        (Q.geometry.overlapDomain_le P.geometry)) =
      restrict (P.geometry.overlapDomain_le Q.geometry) (P.currentOfDegree p r hdeg u) := by
  let A := P.geometry.overlapDomain Q.geometry
  let B := Q.geometry.overlapDomain P.geometry
  let τ := P.geometry.transition Q.geometry
  let ι := Q.geometry.transition P.geometry
  let h : IsBiholomorphicPair A B τ ι := P.geometry.isBiholomorphicPair Q.geometry
  have hAP : A ≤ P.geometry.domain := P.geometry.overlapDomain_le Q.geometry
  have hBQ : B ≤ Q.geometry.domain := Q.geometry.overlapDomain_le P.geometry
  have hτQ : MapsTo τ (A : Set (ComplexModel (m + 1))) Q.geometry.domain :=
    fun z hz => hBQ (h.mapsTo hz)
  have hqQ := Q.smooth.comp (h.holo.restrict_scalars ℝ) hτQ
  have hqP := P.smooth.mono hAP
  let g : ComplexModel (m + 1) → ℝ := fun z => Q.correction (τ z) - P.correction z
  have hg : ContDiffOn ℝ ∞ g A := hqQ.sub hqP
  let σA : ComplexModel (m + 1) → RealForm (m + 1) 2 :=
    fun z => omega.form.coeff P.geometry.chart z - smoothDDC (fun y => Q.correction (τ y)) z
  have hσA : ContDiffOn ℝ ∞ σA A :=
    ((omega.form.smooth P.geometry.chart).mono (fun z hz => P.geometry.domain_le_target (hAP hz))).sub
      (contDiffOn_ddcForm hqQ)
  have hσcomp : ∀ z ∈ A, σA z =
      (Q.residual (τ z)).compContinuousLinearMap ((fderiv ℂ τ z).restrictScalars ℝ) := by
    intro z hz
    have hztrans : z ∈ (chartTransition P.geometry.chart Q.geometry.chart).source :=
      ⟨P.geometry.domain_le_target hz.1, hz.2.1⟩
    have hD := coordinateMap_fderiv_restrictScalars contMDiff_id
      P.geometry.chart Q.geometry.chart hztrans
    have hddc := HolomorphicDDC.smoothDDC_comp A.isOpen Q.geometry.domain.isOpen
      h.holo Q.smooth hτQ hz
    dsimp only [σA, residual]
    rw [hddc]
    ext v
    simp only [ContinuousAlternatingMap.sub_apply, ContinuousAlternatingMap.compContinuousLinearMap_apply]
    rw [omega.form.compatible P.geometry.chart Q.geometry.chart z hztrans v]
    change (omega.form.coeff Q.geometry.chart (τ z))
        (fun i => fderiv ℝ τ z (v i)) -
      (smoothDDC Q.correction (τ z)) (fun i => fderiv ℝ τ z (v i)) = _
    have hDτ : fderiv ℝ τ z = (fderiv ℂ τ z).restrictScalars ℝ := hD
    rw [hDτ]
    rfl
  have hvP (i : Fin p) := isLocallyBoundedPshOn_mono
    (P.correctedReal_isLocallyBoundedPshOn (hu i) (hb i)) hAP
  have hvQ (i : Fin p) := isLocallyBoundedPshOn_mono
    (Q.correctedReal_isLocallyBoundedPshOn (hu i) (hb i)) hBQ
  have heqv (i : Fin p) : EqOn (fun z => Q.correctedReal (u i) (τ z))
      (fun z => P.correctedReal (u i) z + g z) A := by
    intro z hz
    have hback : Q.geometry.chart.val.symm (τ z) = P.geometry.chart.val.symm z :=
      Q.geometry.chart.val.left_inv hz.2.1
    dsimp only [correctedReal, chartFunction, g]
    rw [hback]
    ring
  have hvg (i : Fin p) : IsLocallyBoundedPshOn A (fun z => P.correctedReal (u i) z + g z) :=
    locallyBoundedPsh_congr (locallyBoundedPsh_comp h (hvQ i)) (heqv i)
  have hres : EqOn σA (fun z => P.residual z - smoothDDC g z) A := by
    intro z hz
    dsimp only [σA, residual, g]
    have hdg := PositiveClasses.smoothDDC_sub A.isOpen hqQ hqP hz
    have hfun : Q.correction ∘ τ = (fun y => Q.correction (τ y)) := funext (fun _ => rfl)
    rw [hfun] at hdg
    rw [hdg]
    abel
  have hposQ := isPositive_backgroundExpansion p r
    (oneCurrentOf hdeg) (isPositive_oneCurrentOf _) (isClosedAny_oneCurrentOf _)
    (fun i => Q.correctedReal (u i)) hvQ (Q.residual_smooth.mono hBQ)
    (fun z hz => Q.residual_isOneOne z (hBQ hz))
    (fun i => Q.factor_isPositive_on (hu i) (hb i) hBQ)
  calc
    pullback h (isPositive_restrict (Q.currentOfDegree_isPositive p r hdeg u hu hb) hBQ) =
        pullback h hposQ := pullback_congr_current h _ _ (Q.currentOfDegree_restrict p r hdeg u hu hb hBQ)
    _ = backgroundExpansion p r (fun i z => Q.correctedReal (u i) (τ z))
        hσA (oneCurrentOf (U := A) hdeg) :=
      pullback_backgroundExpansion hdeg h _ hvQ _ hσA
        (fun z hz => Q.residual_isOneOne z (hBQ hz)) hσcomp
        (fun i => Q.factor_isPositive_on (hu i) (hb i) hBQ)
    _ = backgroundExpansion p r (fun i z => P.correctedReal (u i) z + g z)
        ((P.residual_smooth.mono hAP).sub (contDiffOn_ddcForm hg))
        (oneCurrentOf (U := A) hdeg) :=
      backgroundExpansion_congr p r _ _ _ heqv hσA _ hres
    _ = backgroundExpansion p r (fun i => P.correctedReal (u i))
        (P.residual_smooth.mono hAP) (oneCurrentOf (U := A) hdeg) :=
      backgroundExpansion_add_smooth p r _
        (isPositive_oneCurrentOf _) (isClosedAny_oneCurrentOf _) _ hvP hg hvg _
        (fun z hz => oneOne_mem_formSpan (P.residual_isOneOne z (hAP hz)))
    _ = restrict hAP (P.currentOfDegree p r hdeg u) := (P.currentOfDegree_restrict p r hdeg u hu hb hAP).symm

/-- Descent of the original mixed-current interface. -/
theorem mixedCurrent_overlap (P Q : BackgroundPatch omega) (p : ℕ) (hp : p ≤ m + 1)
    (u : Fin p → M → EReal) (hu : ∀ i, IsHermitianPSH omega (u i))
    (hb : ∀ i, ∃ a b : ℝ, ∀ x, (a : EReal) ≤ u i x ∧ u i x ≤ (b : EReal)) :
    pullback (P.geometry.isBiholomorphicPair Q.geometry)
      (isPositive_restrict (Q.mixedCurrent_isPositive p hp u hu hb)
        (Q.geometry.overlapDomain_le P.geometry)) =
      restrict (P.geometry.overlapDomain_le Q.geometry) (P.mixedCurrent p hp u) :=
  P.currentOfDegree_overlap Q p (m + 1 - p) (Nat.sub_add_cancel hp) u hu hb

/-- The same actual descent law in top degree, with the original top
product definition and no degree-cast wrapper in its statement. -/
theorem current_overlap (P Q : BackgroundPatch omega)
    (u : Fin (m + 1) → M → EReal) (hu : ∀ i, IsHermitianPSH omega (u i))
    (hb : ∀ i, ∃ a b : ℝ, ∀ x, (a : EReal) ≤ u i x ∧ u i x ≤ (b : EReal)) :
    pullback (P.geometry.isBiholomorphicPair Q.geometry)
      (isPositive_restrict (Q.current_isPositive u hu hb)
        (Q.geometry.overlapDomain_le P.geometry)) =
      restrict (P.geometry.overlapDomain_le Q.geometry) (P.current u) := by
  exact P.currentOfDegree_overlap Q (m + 1) 0 (Nat.zero_add (m + 1)) u hu hb

private theorem traceMeasure_congr {n r : ℕ} {U : Opens (ComplexModel n)}
    {S T : LocalProductCurrent n U r} (hS : IsPositive S) (hT : IsPositive T)
    (heq : S = T) : hS.traceMeasure = hT.traceMeasure := by
  subst T
  rfl

/-- The actual top-degree Riesz measures satisfy the literal inverse-chart
pushforward law. Holomorphic covariance, correction independence and the
trace-measure conversion are all manufactured from original class members. -/
theorem current_trace_overlap (P Q : BackgroundPatch omega)
    (u : Fin (m + 1) → M → EReal) (hu : ∀ i, IsHermitianPSH omega (u i))
    (hb : ∀ i, ∃ a b : ℝ, ∀ x, (a : EReal) ≤ u i x ∧ u i x ≤ (b : EReal)) :
    (P.current_isPositive u hu hb).traceMeasure.restrict (P.geometry.overlapDomain Q.geometry) =
      ((Q.current_isPositive u hu hb).traceMeasure.restrict (Q.geometry.overlapDomain P.geometry)).map
        (Q.geometry.transition P.geometry) := by
  let h := P.geometry.isBiholomorphicPair Q.geometry
  let hAP := P.geometry.overlapDomain_le Q.geometry
  let hBQ := Q.geometry.overlapDomain_le P.geometry
  let hTP := P.current_isPositive u hu hb
  let hTQ := Q.current_isPositive u hu hb
  let hQR := isPositive_restrict hTQ hBQ
  rw [← traceMeasure_restrict hTP hAP]
  rw [← traceMeasure_congr (isPositive_pullback h hQR) (isPositive_restrict hTP hAP)
    (P.current_overlap Q u hu hb)]
  rw [HermitianProducts.traceMeasure_pullback_top_eq_map h hQR,
    traceMeasure_restrict hTQ hBQ,
    Measure.restrict_restrict (Q.geometry.overlapDomain P.geometry).isOpen.measurableSet,
    inter_self]

end BackgroundPatch

end SGPT.PSH.HermitianGlobalProducts
