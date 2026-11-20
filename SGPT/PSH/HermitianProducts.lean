import SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorCalculus
import SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorWedgeAssociation
import SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorSmoothDensity
import SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorSmoothProductDensity
import SGPT.Foundations.Analysis.Pending.LocalCurrentDensityMatrix
import SGPT.Foundations.Analysis.Pending.LocalCurrentPullbackDdc
import SGPT.Foundations.Analysis.Pending.CompactVariableCurrentTests
import Mathlib.Data.Fin.Rev

/-!
# Smooth shifts and nonclosed-background local currents

The identities here concern the actual coefficient-distribution currents and
Bedford--Taylor recursion, rather than a formal product algebra. They are the
one-factor smooth-shift identity used in FPT, equation
`eq:hermitian-smooth-shift-expansion`, and the linearity and weak continuity of
wedging with an arbitrary smooth form. In particular, the smooth form is not
assumed closed or positive.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.HermitianProducts

open Set Filter MeasureTheory TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open FirstPass.MongeAmpere StronglyPositiveForms
open LocalProductCurrents LocalBedfordTaylorProducts LocalBedfordTaylorSmooth
  LocalBedfordTaylorForms LocalBedfordTaylorCalculus LocalBedfordTaylorCollar
  LocalBedfordTaylorContinuity
  LocalBedfordTaylorSmoothDensity LocalCurrentDensityMatrix CompactVariableCurrentTests
  LocalCurrentLebesgue TopDegreeDensity LocalCurrentPullbackDdc
  LocalBedfordTaylorSmoothProductDensity LocalBedfordTaylorDecreasing
open scoped Topology Distributions ContDiff

variable {n : ℕ} {U : Opens (ComplexModel n)}

attribute [local instance] LocalCurrentLebesgue.addCommGroupFormSpan

private theorem integrable_smooth_form_density_test {m : ℕ}
    {W : Opens (ComplexModel (m + 1))}
    {σ : ComplexModel (m + 1) → RealForm (m + 1) 2}
    (hσ : ContDiffOn ℝ ∞ σ W)
    (γ : formSpan (m + 1) m) (φ : 𝓓(W, ℝ)) :
    Integrable (fun z => φ z * formDensity (σ z) γ) := by
  have := ProductTestForms.realForm_finiteDimensional (n := m + 1) 2
  let L : RealForm (m + 1) 2 →L[ℝ] ℝ :=
    LinearMap.toContinuousLinearMap (wedgeDensity (γ : RealForm (m + 1) (2 * m)))
  have hL : ContDiffOn ℝ ∞ (fun z => formDensity (σ z) γ) W := by
    exact L.contDiff.comp_contDiffOn hσ
  exact (smoothMulTest W.isOpen hL φ φ.tsupport_subset).continuous.integrable_of_hasCompactSupport
    (smoothMulTest W.isOpen hL φ φ.tsupport_subset).hasCompactSupport

/-- A smooth, possibly nonclosed, one-one form gives its literal integral on
every full variable compact test form, not merely on decomposable tests. -/
theorem wedgeForm_oneCurrent_full_test_integral {m : ℕ}
    {W : Opens (ComplexModel (m + 1))}
    {σ : ComplexModel (m + 1) → RealForm (m + 1) 2}
    (hσ : ContDiffOn ℝ ∞ σ W)
    (hσS : ∀ z ∈ W, σ z ∈ formSpan (m + 1) 1)
    (β : 𝓓(W, RealForm (m + 1) (2 * m)))
    (hβ : ∀ z, β z ∈ formSpan (m + 1) m) :
    (∑ i, wedgeForm rfl (oneCurrent W) hσ (formBasis (m + 1) m i)
      (coeffTest β i)) = ∫ z, topDensity (coordinateWedge (β z) (σ z)) := by
  classical
  simp_rw [wedgeForm_oneCurrent_apply rfl hσ hσS]
  change (∑ i, ∫ z, coeffTest β i z * formDensity (σ z) (formBasis (m + 1) m i)) = _
  rw [← integral_finsetSum _ (fun i _ =>
    integrable_smooth_form_density_test hσ (formBasis (m + 1) m i) (coeffTest β i))]
  apply integral_congr_ae
  filter_upwards [] with z
  have he : (⟨β z, hβ z⟩ : formSpan (m + 1) m) =
      ∑ i, coeffTest β i z • formBasis (m + 1) m i := by
    apply Subtype.ext
    simpa only [Submodule.coe_sum, Submodule.coe_smul] using eq_sum_coeffTest β hβ z
  change ∑ i, coeffTest β i z * formDensity (σ z) (formBasis (m + 1) m i) =
    formDensity (σ z) ⟨β z, hβ z⟩
  rw [he, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul, smul_eq_mul]

/-- The one-factor Bedford--Taylor smooth-shift formula. The smooth summand
need not be plurisubharmonic: its contribution is the genuine smooth wedge. -/
theorem ddcMul_add_smooth {r : ℕ} {T : LocalProductCurrent n U (r + 1)}
    (hT : IsPositive T) (hTc : IsClosedCurrent T) {u g : ComplexModel n → ℝ}
    (hu : Measurable ((U : Set (ComplexModel n)).indicator u))
    (hub : IsLocallyBoundedOn ((U : Set (ComplexModel n)).indicator u) U)
    (hg : ContDiffOn ℝ ∞ g U) :
    ddcMul T (fun z => u z + g z) =
      ddcMul T u + wedgeForm rfl T (contDiffOn_ddcForm hg) := by
  rw [ddcMul_add hT hu hub
    (measurable_indicator_of_continuousOn hg.continuousOn)
    (isLocallyBoundedOn_indicator_of_continuousOn hg.continuousOn),
    ddcMul_eq_ddcWedge hT hTc hg, ddcWedge_eq_wedgeForm]

/-- Smooth wedging is additive in the smooth form, with no closedness or
positivity condition on either summand. -/
theorem wedgeForm_add {r k m : ℕ} (h : r + k = m)
    (T : LocalProductCurrent n U m)
    {α β : ComplexModel n → RealForm n (2 * k)}
    (hα : ContDiffOn ℝ ∞ α U) (hβ : ContDiffOn ℝ ∞ β U) :
    wedgeForm h T (hα.add hβ) = wedgeForm h T hα + wedgeForm h T hβ := by
  classical
  ext γ φ
  simp only [wedgeForm_apply, LinearMap.add_apply, _root_.add_apply]
  have heq (i : Fin (Module.finrank ℝ (formSpan n k))) :
      mulSmoothOnCLM (contDiffOn_formCoeff (hα.add hβ) i) φ =
        mulSmoothOnCLM (contDiffOn_formCoeff hα i) φ +
          mulSmoothOnCLM (contDiffOn_formCoeff hβ i) φ := by
    ext z
    simp [mulSmoothOnCLM_apply, formCoeff, map_add, mul_add]
  simp only [heq, map_add, Finset.sum_add_distrib]

/-- Smooth wedging respects subtraction, including for nonclosed forms. -/
theorem wedgeForm_sub {r k m : ℕ} (h : r + k = m)
    (T : LocalProductCurrent n U m)
    {α β : ComplexModel n → RealForm n (2 * k)}
    (hα : ContDiffOn ℝ ∞ α U) (hβ : ContDiffOn ℝ ∞ β U) :
    wedgeForm h T (hα.sub hβ) = wedgeForm h T hα - wedgeForm h T hβ := by
  classical
  ext γ φ
  simp only [wedgeForm_apply, LinearMap.sub_apply, _root_.sub_apply]
  have heq (i : Fin (Module.finrank ℝ (formSpan n k))) :
      mulSmoothOnCLM (contDiffOn_formCoeff (hα.sub hβ) i) φ =
        mulSmoothOnCLM (contDiffOn_formCoeff hα i) φ -
          mulSmoothOnCLM (contDiffOn_formCoeff hβ i) φ := by
    ext z
    simp [mulSmoothOnCLM_apply, formCoeff, map_sub, mul_sub]
  simp only [heq, map_sub, Finset.sum_sub_distrib]

/-- Smooth wedging is homogeneous under every real scalar, including
negative scalars; no positivity or closedness is assumed on the form. -/
theorem wedgeForm_smul {r k m : ℕ} (h : r + k = m)
    (T : LocalProductCurrent n U m)
    {σ : ComplexModel n → RealForm n (2 * k)}
    (hσ : ContDiffOn ℝ ∞ σ U) (c : ℝ) :
    wedgeForm h T (hσ.const_smul c) = c • wedgeForm h T hσ := by
  classical
  ext γ φ
  simp only [wedgeForm_apply, LinearMap.smul_apply, _root_.smul_apply, smul_eq_mul]
  have heq (i : Fin (Module.finrank ℝ (formSpan n k))) :
      mulSmoothOnCLM (contDiffOn_formCoeff (hσ.const_smul c) i) φ =
        c • mulSmoothOnCLM (contDiffOn_formCoeff hσ i) φ := by
    ext z
    simp only [mulSmoothOnCLM_apply, formCoeff, map_smul,
      _root_.smul_apply, smul_eq_mul]
    ring
  simp only [heq, map_smul, smul_eq_mul, Finset.mul_sum]

/-- Smooth wedging preserves weak convergence of actual currents. There is
no positivity or closedness restriction on the fixed smooth form. -/
theorem weakTendsto_wedgeForm {r k m : ℕ} (h : r + k = m)
    {T : ℕ → LocalProductCurrent n U m} {T₀ : LocalProductCurrent n U m}
    (hT : WeakTendsto T T₀) {α : ComplexModel n → RealForm n (2 * k)}
    (hα : ContDiffOn ℝ ∞ α U) :
    WeakTendsto (fun j => wedgeForm h (T j) hα) (wedgeForm h T₀ hα) := by
  classical
  intro γ φ
  simp only [wedgeForm_apply]
  exact tendsto_finsetSum _ fun i _ => hT _ _

/-- The degree-one local expansion `ddc(v) ∧ T + σ ∧ T`. This expression
allows an arbitrary smooth residual form `σ`, as required when the original
Hermitian background is not closed. -/
def factorCurrent {r : ℕ} (T : LocalProductCurrent n U (r + 1))
    (v : ComplexModel n → ℝ) {σ : ComplexModel n → RealForm n 2}
    (hσ : ContDiffOn ℝ ∞ σ U) : LocalProductCurrent n U r :=
  ddcMul T v + wedgeForm rfl T hσ

/-- The genuine degree-one expansion is independent of the smooth correction:
replacing `v` by `v + g` and `σ` by `σ - ddc g` leaves the current unchanged.
No closedness of `σ` or plurisubharmonicity of `g` is assumed. -/
theorem factorCurrent_smooth_shift {r : ℕ}
    {T : LocalProductCurrent n U (r + 1)} (hT : IsPositive T)
    (hTc : IsClosedCurrent T) {v g : ComplexModel n → ℝ}
    (hv : Measurable ((U : Set (ComplexModel n)).indicator v))
    (hvb : IsLocallyBoundedOn ((U : Set (ComplexModel n)).indicator v) U)
    {σ : ComplexModel n → RealForm n 2} (hσ : ContDiffOn ℝ ∞ σ U)
    (hg : ContDiffOn ℝ ∞ g U) :
    factorCurrent T (fun z => v z + g z) (hσ.sub (contDiffOn_ddcForm hg)) =
      factorCurrent T v hσ := by
  unfold factorCurrent
  rw [ddcMul_add_smooth hT hTc hv hvb hg,
    wedgeForm_sub rfl T hσ (contDiffOn_ddcForm hg)]
  abel_nf

/-- Smooth shifting the outermost slot of a Bedford--Taylor product separates
off the actual smooth wedge with the remaining, bounded PSH product. -/
theorem btProduct_smooth_shift_outer (p r : ℕ)
    (T : LocalProductCurrent n U (r + (p + 1))) (hT : IsPositive T)
    (hTc : IsClosedAny (r + (p + 1)) T)
    (v : Fin (p + 1) → ComplexModel n → ℝ)
    (hv : ∀ i, IsLocallyBoundedPshOn U (v i))
    {g : ComplexModel n → ℝ} (hg : ContDiffOn ℝ ∞ g U) :
    btProduct (p + 1) r (Function.update v 0 (fun z => v 0 z + g z)) T =
      btProduct (p + 1) r v T +
        wedgeForm rfl
          (btProduct p (r + 1) (Fin.tail v) (castLPC (by omega) T))
          (contDiffOn_ddcForm hg) := by
  have hdeg : r + (p + 1) = r + 1 + p := by omega
  have htail := isPositive_btProduct p (r + 1) (Fin.tail v) (castLPC hdeg T)
    (isPositive_castLPC hdeg hT) (isClosedAny_castLPC hdeg hTc) (fun i => hv _)
  simp only [btProduct_succ_eq_ddcMul p r _ T (castLPC hdeg T)
    (heq_castLPC hdeg T), Fin.tail_update_zero, Function.update_self]
  exact ddcMul_add_smooth htail.1 htail.2
    (measurable_indicator_of_isLocallyBoundedPshOn (hv 0))
    (isLocallyBoundedOn_indicator (hv 0)) hg

/-- Smooth shifting the last slot separates off the actual smooth wedge with
the product of the other slots. Both the original and shifted potentials are
PSH; the smooth difference itself need not be PSH. -/
theorem btProduct_smooth_shift_last (p r : ℕ)
    (T : LocalProductCurrent n U (r + (p + 1))) (hT : IsPositive T)
    (hTc : IsClosedAny (r + (p + 1)) T)
    (v : Fin (p + 1) → ComplexModel n → ℝ)
    (hv : ∀ i, IsLocallyBoundedPshOn U (v i))
    {g : ComplexModel n → ℝ} (hg : ContDiffOn ℝ ∞ g U)
    (hshift : IsLocallyBoundedPshOn U (fun z => v (Fin.last p) z + g z)) :
    btProduct (p + 1) r
        (Function.update v (Fin.last p) (fun z => v (Fin.last p) z + g z)) T =
      btProduct (p + 1) r v T +
        wedgeForm rfl
          (btProduct p (r + 1) (Fin.init v) (castLPC (by omega) T))
          (contDiffOn_ddcForm hg) := by
  classical
  have hdeg : r + (p + 1) = r + 1 + p := by omega
  let w := Function.update v (Fin.last p) (fun z => v (Fin.last p) z + g z)
  have hw : ∀ i, IsLocallyBoundedPshOn U (w i) := by
    intro i
    by_cases hi : i = Fin.last p
    · simpa [w, hi] using hshift
    · simpa [w, hi] using hv i
  have hreverse : w ∘ Fin.revPerm =
      Function.update (v ∘ Fin.revPerm) 0 (fun z => v (Fin.last p) z + g z) := by
    dsimp only [w]
    rw [Function.update_comp_equiv]
    simp
  have htail : Fin.tail (v ∘ Fin.revPerm) = Fin.init v ∘ Fin.revPerm := by
    ext i z
    simp [Fin.tail, Fin.init, Fin.rev_succ]
  rw [show Function.update v (Fin.last p) (fun z => v (Fin.last p) z + g z) = w
    from rfl, ← btProduct_comp_perm (p + 1) r T hT hTc w hw Fin.revPerm,
    hreverse]
  have houter := btProduct_smooth_shift_outer p r T hT hTc (v ∘ Fin.revPerm)
    (fun i => hv _) hg
  simp only [Function.comp_apply, Fin.revPerm_apply, Fin.rev_zero] at houter
  rw [houter, btProduct_comp_perm (p + 1) r T hT hTc v hv Fin.revPerm, htail,
    btProduct_comp_perm p (r + 1) (castLPC hdeg T)
      (isPositive_castLPC hdeg hT) (isClosedAny_castLPC hdeg hTc)
      (Fin.init v) (fun i => hv _) Fin.revPerm]

/-- The finite smooth-shift expansion, indexed recursively by choosing either
the original PSH factor or its smooth correction at each slot. Unfolding the
recursion gives the sum over all subsets of the slots in FPT's smooth-shift
formula. Every multiplication by a nonsmooth potential remains inside a
Bedford--Taylor product against an original positive closed base current. -/
def smoothShiftExpansion : (p r : ℕ) →
    (Fin p → ComplexModel n → ℝ) → (g : Fin p → ComplexModel n → ℝ) →
    (∀ i, ContDiffOn ℝ ∞ (g i) U) →
    LocalProductCurrent n U (r + p) → LocalProductCurrent n U r
  | 0, _, _, _, _, T => T
  | p + 1, r, v, g, hg, T =>
      smoothShiftExpansion p r (Fin.init v) (Fin.init g) (fun i => hg i.castSucc)
          (ddcMul T (v (Fin.last p))) +
        wedgeForm rfl
          (smoothShiftExpansion p (r + 1) (Fin.init v) (Fin.init g)
            (fun i => hg i.castSucc) (castLPC (by omega) T))
          (contDiffOn_ddcForm (hg (Fin.last p)))

/-- The full smooth-shift expansion for locally bounded PSH factors and
arbitrary smooth shifts which leave the shifted factors PSH. In particular,
the shifts themselves are not required to be PSH. -/
theorem btProduct_smooth_shift_expansion : ∀ (p r : ℕ)
    (T : LocalProductCurrent n U (r + p))
    (_hT : IsPositive T) (_hTc : IsClosedAny (r + p) T)
    (v g : Fin p → ComplexModel n → ℝ)
    (hg : ∀ i, ContDiffOn ℝ ∞ (g i) U)
    (_hv : ∀ i, IsLocallyBoundedPshOn U (v i))
    (_hshift : ∀ i, IsLocallyBoundedPshOn U (fun z => v i z + g i z)),
    btProduct p r (fun i z => v i z + g i z) T =
      smoothShiftExpansion p r v g hg T
  | 0, _, _, _, _, _, _, _, _, _ => rfl
  | p + 1, r, T, hT, hTc, v, g, hg, hv, hshift => by
    classical
    let w := Function.update (fun i z => v i z + g i z) (Fin.last p) (v (Fin.last p))
    have hw : ∀ i, IsLocallyBoundedPshOn U (w i) := by
      intro i
      by_cases hi : i = Fin.last p
      · simpa [w, hi] using hv (Fin.last p)
      · simpa [w, hi] using hshift i
    have hwinit : Fin.init w = fun i z => v i.castSucc z + g i.castSucc z := by
      simp [w, Fin.init_update_last]
      rfl
    have hwlast : w (Fin.last p) = v (Fin.last p) := by simp [w]
    have hupdate : Function.update w (Fin.last p)
        (fun z => w (Fin.last p) z + g (Fin.last p) z) =
        fun i z => v i z + g i z := by
      ext i z
      by_cases hi : i = Fin.last p <;> simp [w, hi]
    have hlast := btProduct_smooth_shift_last p r T hT hTc w hw
      (hg (Fin.last p)) (by simpa only [hwlast] using hshift (Fin.last p))
    rw [hupdate, hwinit] at hlast
    rw [hlast, btProduct_succ, hwinit, hwlast]
    obtain ⟨hbase, hbasec⟩ := isPositive_ddcMul hT hTc (hv (Fin.last p))
    have hdeg : r + (p + 1) = r + 1 + p := by omega
    change btProduct p r (fun i z => Fin.init v i z + Fin.init g i z)
        (ddcMul T (v (Fin.last p))) +
      wedgeForm rfl (btProduct p (r + 1)
        (fun i z => Fin.init v i z + Fin.init g i z) (castLPC hdeg T))
        (contDiffOn_ddcForm (hg (Fin.last p))) = _
    rw [btProduct_smooth_shift_expansion p r _ hbase hbasec
      (Fin.init v) (Fin.init g) (fun i => hg i.castSucc)
      (fun i => hv i.castSucc) (fun i => hshift i.castSucc),
      btProduct_smooth_shift_expansion p (r + 1) (castLPC hdeg T)
        (isPositive_castLPC hdeg hT) (isClosedAny_castLPC hdeg hTc)
        (Fin.init v) (Fin.init g) (fun i => hg i.castSucc)
        (fun i => hv i.castSucc) (fun i => hshift i.castSucc)]
    rfl

/-- One actual subset term in the local Hermitian product expansion. The
selected factors are ordinary Bedford--Taylor currents; all other factors
are exterior products with the given arbitrary smooth residual form. -/
def backgroundExpansionTerm (p r : ℕ)
    (v : Fin p → ComplexModel n → ℝ)
    {σ : ComplexModel n → RealForm n 2} (hσ : ContDiffOn ℝ ∞ σ U)
    (T : LocalProductCurrent n U (r + p)) (s : Finset (Fin p)) :
    LocalProductCurrent n U r := by
  classical
  have hs : s.card ≤ p := by simpa using Finset.card_le_univ s
  exact wedgeForm rfl
    (btProduct s.card (r + (p - s.card)) (fun i => v (s.orderEmbOfFin rfl i))
      (castLPC (by omega : r + p = r + (p - s.card) + s.card) T))
    (contDiffOn_wedgeProd (p - s.card) (fun _ => σ) (fun _ => hσ))

/-- FPT's local expansion for a nonclosed Hermitian background: sum the
actual mixed Bedford--Taylor/smooth-form currents over every subset. For a
correction `q`, take `v_l=u_l+q` and `σ=ω-ddc q`. No positivity or independence
of this expression is built into its definition. -/
def backgroundExpansion (p r : ℕ)
    (v : Fin p → ComplexModel n → ℝ)
    {σ : ComplexModel n → RealForm n 2} (hσ : ContDiffOn ℝ ∞ σ U)
    (T : LocalProductCurrent n U (r + p)) : LocalProductCurrent n U r :=
  ∑ s : Finset (Fin p), backgroundExpansionTerm p r v hσ T s

/-- Each subset term of the nonclosed-background expansion is weakly
continuous for decreasing locally bounded PSH factors. -/
theorem backgroundExpansionTerm_decreasing (p r : ℕ)
    (T : LocalProductCurrent n U (r + p)) (hT : IsPositive T)
    (hTc : IsClosedAny (r + p) T)
    (v : ℕ → Fin p → ComplexModel n → ℝ) (v₀ : Fin p → ComplexModel n → ℝ)
    (hv : ∀ j i, IsLocallyBoundedPshOn U (v j i))
    (hv₀ : ∀ i, IsLocallyBoundedPshOn U (v₀ i))
    (hanti : ∀ i z, z ∈ U → Antitone (fun j => v j i z))
    (hlim : ∀ i z, z ∈ U → Tendsto (fun j => v j i z) atTop (𝓝 (v₀ i z)))
    {σ : ComplexModel n → RealForm n 2} (hσ : ContDiffOn ℝ ∞ σ U)
    (s : Finset (Fin p)) :
    WeakTendsto (fun j => backgroundExpansionTerm p r (v j) hσ T s)
      (backgroundExpansionTerm p r v₀ hσ T s) := by
  classical
  unfold backgroundExpansionTerm
  apply weakTendsto_wedgeForm
  exact weakTendsto_btProduct_of_antitone s.card (r + (p - s.card)) _
    (isPositive_castLPC _ hT) (isClosedAny_castLPC _ hTc)
    (fun j i => v j (s.orderEmbOfFin rfl i)) (fun i => v₀ (s.orderEmbOfFin rfl i))
    (fun j i => hv j _) (fun i => hv₀ _)
    (fun i z hz => hanti _ z hz) (fun i z hz => hlim _ z hz)

/-- The actual finite nonclosed-background expansion is weakly continuous
under decreasing sequences of locally bounded PSH factors. -/
theorem backgroundExpansion_decreasing (p r : ℕ)
    (T : LocalProductCurrent n U (r + p)) (hT : IsPositive T)
    (hTc : IsClosedAny (r + p) T)
    (v : ℕ → Fin p → ComplexModel n → ℝ) (v₀ : Fin p → ComplexModel n → ℝ)
    (hv : ∀ j i, IsLocallyBoundedPshOn U (v j i))
    (hv₀ : ∀ i, IsLocallyBoundedPshOn U (v₀ i))
    (hanti : ∀ i z, z ∈ U → Antitone (fun j => v j i z))
    (hlim : ∀ i z, z ∈ U → Tendsto (fun j => v j i z) atTop (𝓝 (v₀ i z)))
    {σ : ComplexModel n → RealForm n 2} (hσ : ContDiffOn ℝ ∞ σ U) :
    WeakTendsto (fun j => backgroundExpansion p r (v j) hσ T)
      (backgroundExpansion p r v₀ hσ T) := by
  classical
  intro γ φ
  simp only [backgroundExpansion, LinearMap.sum_apply, _root_.sum_apply]
  exact tendsto_finsetSum _ fun s _ =>
    backgroundExpansionTerm_decreasing p r T hT hTc v v₀ hv hv₀ hanti hlim hσ s γ φ

end SGPT.PSH.HermitianProducts
