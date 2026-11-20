import SGPT.NPP.BedfordTaylorManifold
import SGPT.Foundations.Analysis.FirstPass.HolomorphicDDC

/-!
# Biholomorphic invariance of relative Bedford–Taylor products

Source: `chapter_npp.tex`, `rmk:extensionBT` (the product `dd^c φ₁ ∧ ⋯ ∧ dd^c φ_p ∧ T` for a
closed positive current `T`, "defined in a very similar way"); Xia, *Foundations of
pluripotential theory*, `prop:bt-positive-recursion` (5) (biholomorphic invariance).

Let `τ : A → B` be biholomorphic with inverse `σ` (`BedfordTaylor.IsBiholomorphicPair`), `S` a
positive current on `B` which is closed and whose pull-back `τ^* S` is closed, and `u₁, …, u_q`
locally bounded psh on `B`.  Then

`τ^* (dd^c u₁ ∧ ⋯ ∧ dd^c u_q ∧ S) = dd^c (u₁ ∘ τ) ∧ ⋯ ∧ dd^c (u_q ∘ τ) ∧ τ^* S`
(`pullback_btProduct_rel`).

TN proves this for `S = [B]` only (`LocalBedfordTaylorBiholomorphicProducts.pullback_btProduct`).

* `pullback_ddcMul_of_smooth` — **the smooth case**: for `g` smooth psh on `B`,
  `τ^*(dd^c g ∧ S) = dd^c(g ∘ τ) ∧ τ^* S`.  Both sides are computed as
  `∫_B φ(σ y) L_y(Dσ(y)^* γ ∧ dd^c g(y)) dσ_S(y)` on the test form `φ γ`: the left side through
  `pullback_apply_eq_sum_mulBorel` and `mulBorel_wedgeForm`, the right side through
  `pullback_apply`, and `Dσ(y)^*(γ ∧ dd^c(g ∘ τ)(σ y)) = Dσ(y)^* γ ∧ dd^c g(y)` (chain rule and
  naturality of `dd^c` under holomorphic maps).
* `pullback_ddcMul_rel` — locally bounded psh `w`, by decreasing smooth approximation on a
  relatively compact subset (weak continuity of `dd^c(w S)` along decreasing sequences, of the
  pull-back, and locality), as in TN's `LocalCurrentPullbackDdc.pullback_ddcMul`.
* `pullback_btProduct_rel` — induction on the number of factors.
* `SGPT.NPP.bedfordTaylorRelInChart_compatible`, `SGPT.NPP.bedfordTaylorRel`,
  `SGPT.NPP.isClosed_bedfordTaylorRel` — **`rmk:extensionBT` on a complex manifold**: for a closed
  positive current `T` on `M` the chart expressions of `dd^c u₁ ∧ ⋯ ∧ dd^c u_p ∧ T` agree on
  overlaps, so they define a closed positive current on `M`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Distributions ContDiff

namespace SGPT.NPP.RelativeBT

open SGPT.Foundations.Analysis
open SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.StronglyPositiveForms
open SGPT.Foundations.Analysis.Pending.ConstantFormProducts
open SGPT.Foundations.Analysis.Pending.LocalProductCurrents
open SGPT.Foundations.Analysis.Pending.LocalCurrentLebesgue
open SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorProducts
open SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorLocality
open SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorSmooth
open SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorForms
open SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorCollar
open SGPT.Foundations.Analysis.Pending.LocalCurrentPullback
open SGPT.Foundations.Analysis.Pending.LocalCurrentPullbackDdc
open SGPT.Foundations.Analysis.Pending.BedfordTaylor

attribute [local instance] addCommGroupFormSpan

variable {N : ℕ} {A B : Opens (ComplexModel N)} {τ σ : ComplexModel N → ComplexModel N}

/-- The inverse biholomorphic pair. -/
theorem isBiholomorphicPair_symm (h : IsBiholomorphicPair A B τ σ) :
    IsBiholomorphicPair B A σ τ :=
  ⟨h.holo_inv, h.holo, h.mapsTo_inv, h.mapsTo, h.right_inv, h.left_inv⟩

/-- `Dτ(σ y) ∘ Dσ(y) = id` on `B`. -/
theorem fderiv_comp_inv (h : IsBiholomorphicPair A B τ σ) {y : ComplexModel N} (hy : y ∈ B) :
    (fderiv ℂ τ (σ y)).comp (fderiv ℂ σ y) = ContinuousLinearMap.id ℂ (ComplexModel N) := by
  have := fderiv_inv_comp (isBiholomorphicPair_symm h) hy
  exact this

theorem pullback_congr' (h : IsBiholomorphicPair A B τ σ) {q : ℕ}
    {T T' : LocalProductCurrent N B q} (hT : IsPositive T) (hT' : IsPositive T') (e : T = T') :
    pullback h hT = pullback h hT' := by
  subst e
  rfl

theorem isLocallyBoundedPshOn_comp' (h : IsBiholomorphicPair A B τ σ) {w : ComplexModel N → ℝ}
    (hw : IsLocallyBoundedPshOn B w) : IsLocallyBoundedPshOn A (fun x => w (τ x)) := by
  refine ⟨HolomorphicPullback.plurisubharmonicOn_comp_holomorphic (u := fun z => (w z : EReal))
    A.isOpen (h.holo.differentiableOn (by simp)) h.mapsTo hw.1, fun z hz => ?_⟩
  obtain ⟨V, hzV, hVB, C, hC⟩ := hw.2 (τ z) (h.mapsTo hz)
  exact ⟨preOpen h V, ⟨hz, hzV⟩, preOpen_le h V, C, fun x hx => hC (τ x) hx.2⟩

/-! ### The smooth case -/

section Smooth

variable {r : ℕ}

/-- The `(1,1)`-form `dd^c g(x)`, projected to `Λ₁`. -/
def ddcSpan (g : ComplexModel N → ℝ) (x : ComplexModel N) : formSpan N 1 :=
  formProj N 1 (ddcForm g x)

theorem coe_ddcSpan {U : Opens (ComplexModel N)} {g : ComplexModel N → ℝ}
    (hg : ContDiffOn ℝ ∞ g U) {x : ComplexModel N} (hx : x ∈ U) :
    (ddcSpan g x : RealForm N (2 * 1)) = ddcForm g x := by
  have h2 : ContDiffAt ℝ 2 g x :=
    (hg.contDiffAt (U.isOpen.mem_nhds hx)).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hmem : ddcForm g x ∈ formSpan N 1 := oneOne_mem_formSpan (smoothDDC_isOneOne h2)
  rw [ddcSpan, show ddcForm g x = ((⟨ddcForm g x, hmem⟩ : formSpan N 1) : RealForm N (2 * 1))
    from rfl, formProj_coe]

/-- **Pointwise algebra**: `Dσ(y)^*(γ ∧ dd^c(g ∘ τ)(σ y)) = Dσ(y)^* γ ∧ dd^c g(y)`. -/
theorem pullSpan_wedgeSpan_ddcSpan (h : IsBiholomorphicPair A B τ σ) {g : ComplexModel N → ℝ}
    (hg : ContDiffOn ℝ ∞ g B) {y : ComplexModel N} (hy : y ∈ B) (γ : formSpan N r) :
    pullSpan (r + 1) (fderiv ℂ σ y) (wedgeSpan N rfl γ (ddcSpan (fun x => g (τ x)) (σ y))) =
      wedgeSpan N rfl (pullSpan r (fderiv ℂ σ y) γ) (ddcSpan g y) := by
  have hgA : ContDiffOn ℝ ∞ (fun x => g (τ x)) A := hg.comp (h.holo.restrict_scalars ℝ) h.mapsTo
  have hσy : σ y ∈ A := h.mapsTo_inv hy
  apply Subtype.ext
  rw [coe_pullSpan, coe_wedgeSpan_apply rfl _ _ (by omega), coe_wedgeSpan_apply rfl _ _ (by omega),
    wedgeTo_compContinuousLinearMap, coe_pullSpan, coe_ddcSpan hgA hσy, coe_ddcSpan hg hy]
  congr 1
  have hcomp : smoothDDC (fun x => g (τ x)) (σ y) =
      (smoothDDC g (τ (σ y))).compContinuousLinearMap (fderiv ℝ τ (σ y)) :=
    FirstPass.HolomorphicDDC.smoothDDC_comp A.isOpen B.isOpen h.holo hg h.mapsTo hσy
  rw [ddcForm, hcomp, h.right_inv y hy]
  ext v
  simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply, ddcForm]
  congr 1
  funext i
  simp only [Function.comp_apply, ContinuousLinearMap.coe_restrictScalars']
  have hτ : HasFDerivAt τ (fderiv ℂ τ (σ y)) (σ y) :=
    ((h.holo.differentiableOn (by simp)) (σ y) hσy).differentiableAt
      (A.isOpen.mem_nhds hσy) |>.hasFDerivAt
  rw [hτ.restrictScalars ℝ |>.fderiv]
  simp only [ContinuousLinearMap.coe_restrictScalars']
  rw [← ContinuousLinearMap.comp_apply, fderiv_comp_inv h hy, ContinuousLinearMap.id_apply]

theorem sum_formCoeff_smul (g : ComplexModel N → ℝ) (x : ComplexModel N) :
    ∑ j, formCoeff (ddcForm g) j x • formBasis N 1 j = ddcSpan g x := by
  simp only [formCoeff_apply]
  exact (formBasis N 1).sum_repr _

/-- **The smooth case**: `τ^*(S ∧ dd^c g) = τ^*S ∧ dd^c(g ∘ τ)` for a positive current `S` on `B`
and `g` smooth on `B` with `dd^c g ≥ 0`. -/
theorem pullback_wedgeForm_ddcForm (h : IsBiholomorphicPair A B τ σ)
    {S : LocalProductCurrent N B (r + 1)} (hS : IsPositive S) {g : ComplexModel N → ℝ}
    (hg : ContDiffOn ℝ ∞ g B) (hgp : ∀ x ∈ B, ddcForm g x ∈ spCone 1) :
    pullback h (isPositive_wedgeForm rfl hS (contDiffOn_ddcForm hg) hgp) =
      wedgeForm rfl (pullback h hS) (contDiffOn_ddcForm (U := A) (g := fun x => g (τ x))
        (hg.comp (h.holo.restrict_scalars ℝ) h.mapsTo)) := by
  classical
  have hgA : ContDiffOn ℝ ∞ (fun x => g (τ x)) A := hg.comp (h.holo.restrict_scalars ℝ) h.mapsTo
  set hαB := contDiffOn_ddcForm hg
  set hαA := contDiffOn_ddcForm (U := A) hgA
  set hW := isPositive_wedgeForm rfl hS hαB hgp
  ext γ φ
  set σS := hS.traceMeasure
  set Φ : ComplexModel N → ℝ := (B : Set (ComplexModel N)).indicator fun y =>
    φ (σ y) * densityForm hS y (wedgeSpan N rfl (pullSpan r (fderiv ℂ σ y) γ) (ddcSpan g y))
    with hΦ
  -- the right side
  have hR : wedgeForm rfl (pullback h hS) hαA γ φ = ∫ y, Φ y ∂σS := by
    rw [wedgeForm_apply]
    simp only [pullback_apply h hS]
    rw [← integral_finsetSum _ (fun j _ => integrableOn_pullback_integrand h hS _ _), hΦ,
      integral_indicator B.isOpen.measurableSet]
    refine setIntegral_congr_fun B.isOpen.measurableSet fun y hy => ?_
    simp only [mulSmoothOnCLM_apply]
    rw [← pullSpan_wedgeSpan_ddcSpan h hg hy γ, ← sum_formCoeff_smul]
    simp only [map_sum, map_smul, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  -- the left side
  have hK : IsCompact (τ '' tsupport φ) :=
    φ.hasCompactSupport.image_of_continuousOn (h.holo.continuousOn.mono φ.tsupport_subset)
  obtain ⟨χ, hχ⟩ := exists_testFunction_eq_one hK
    (image_subset_iff.mpr fun x hx => h.mapsTo (φ.tsupport_subset hx))
  have hL : pullback h hW γ φ = ∫ y, Φ y ∂σS := by
    rw [pullback_apply_eq_sum_mulBorel h hW γ φ hχ]
    simp only [mulBorel_wedgeForm rfl hS hαB hgp (measurable_pbCoeffFun h γ φ _)
      (isLocallyBoundedOn_pbCoeffFun h γ φ _), wedgeForm_apply,
      mulBorel_apply hS (measurable_pbCoeffFun h γ φ _) (isLocallyBoundedOn_pbCoeffFun h γ φ _)]
    have hint (i : Fin (Module.finrank ℝ (formSpan N r)))
        (j : Fin (Module.finrank ℝ (formSpan N 1))) :=
      hS.integrable_mul_density (measurable_pbCoeffFun h γ φ i)
        (isLocallyBoundedOn_pbCoeffFun h γ φ i) (wedgeSpan N rfl (formBasis N r i)
          (formBasis N 1 j)) (mulSmoothOnCLM (contDiffOn_formCoeff hαB j) χ)
    simp only [← integral_finsetSum _ fun j _ => hint _ j]
    rw [← integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hint i j]
    have hall := ae_all_iff.mpr fun ij : Fin (Module.finrank ℝ (formSpan N r)) ×
        Fin (Module.finrank ℝ (formSpan N 1)) =>
      densityForm_ae hS (wedgeSpan N rfl (formBasis N r ij.1) (formBasis N 1 ij.2))
    refine integral_congr_ae ?_
    filter_upwards [hall] with y hy
    have hy' (i : Fin (Module.finrank ℝ (formSpan N r)))
        (j : Fin (Module.finrank ℝ (formSpan N 1))) :
        hS.density (wedgeSpan N rfl (formBasis N r i) (formBasis N 1 j)) y =
          densityForm hS y (wedgeSpan N rfl (formBasis N r i) (formBasis N 1 j)) :=
      (hy (i, j)).symm
    simp only [hy', mulSmoothOnCLM_apply]
    by_cases hyB : y ∈ (B : Set (ComplexModel N))
    · rw [hΦ, indicator_of_mem hyB]
      simp only [pbCoeffFun, indicator_of_mem hyB]
      have hχy : χ y * φ (σ y) = φ (σ y) := by
        by_cases h0 : φ (σ y) = 0
        · rw [h0, mul_zero]
        · rw [hχ y ⟨σ y, subset_tsupport φ h0, h.right_inv y hyB⟩, one_mul]
      have key : densityForm hS y (wedgeSpan N rfl (pullSpan r (fderiv ℂ σ y) γ) (ddcSpan g y)) =
          ∑ i, ∑ j, (formBasis N r).repr (pullSpan r (fderiv ℂ σ y) γ) i *
            formCoeff (ddcForm g) j y *
              densityForm hS y (wedgeSpan N rfl (formBasis N r i) (formBasis N 1 j)) := by
        conv_lhs => rw [← (formBasis N r).sum_repr (pullSpan r (fderiv ℂ σ y) γ),
          ← sum_formCoeff_smul g y]
        simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
          Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        ring
      calc _ = ∑ i, ∑ j, (χ y * φ (σ y)) * ((formBasis N r).repr (pullSpan r (fderiv ℂ σ y) γ) i *
            formCoeff (ddcForm g) j y *
              densityForm hS y (wedgeSpan N rfl (formBasis N r i) (formBasis N 1 j))) :=
            Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
        _ = _ := by rw [hχy, key, Finset.mul_sum]; simp only [Finset.mul_sum]
    · rw [hΦ, indicator_of_notMem hyB]
      simp [pbCoeffFun, indicator_of_notMem hyB]
  rw [hL, hR]

end Smooth

/-! ### Locally bounded potentials -/

section Bounded

variable {r : ℕ}

theorem ddcMul_eq_wedgeForm_ddcForm {U : Opens (ComplexModel N)}
    {S : LocalProductCurrent N U (r + 1)} (hS : IsPositive S) (hSc : IsClosedCurrent S)
    {g : ComplexModel N → ℝ} (hg : ContDiffOn ℝ ∞ g U) :
    ddcMul S g = wedgeForm rfl S (contDiffOn_ddcForm hg) := by
  rw [ddcMul_eq_ddcWedge hS hSc hg, ddcWedge_eq_wedgeForm]

/-- **`τ^*(dd^c g ∧ S) = dd^c(g ∘ τ) ∧ τ^* S`** for `g` smooth psh. -/
theorem pullback_ddcMul_of_smooth (h : IsBiholomorphicPair A B τ σ)
    {S : LocalProductCurrent N B (r + 1)} (hS : IsPositive S) (hSc : IsClosedCurrent S)
    (hS'c : IsClosedCurrent (pullback h hS)) {g : ComplexModel N → ℝ} (hg : IsSmoothPshOn B g) :
    pullback h (isPositive_ddcMul hS hSc (isLocallyBoundedPshOn_of_isSmoothPshOn hg)).1 =
      ddcMul (pullback h hS) (fun x => g (τ x)) := by
  have hgA : ContDiffOn ℝ ∞ (fun x => g (τ x)) A := hg.1.comp (h.holo.restrict_scalars ℝ) h.mapsTo
  have hgp : ∀ x ∈ B, ddcForm g x ∈ spCone 1 := fun x hx =>
    mem_spCone_one (isSemipositiveOneOne_smoothDDC hg.1 hg.2.1 hx)
  rw [pullback_congr' h _ (isPositive_wedgeForm rfl hS (contDiffOn_ddcForm hg.1) hgp)
      (ddcMul_eq_wedgeForm_ddcForm hS hSc hg.1),
    pullback_wedgeForm_ddcForm h hS hg.1 hgp,
    ddcMul_eq_wedgeForm_ddcForm (isPositive_pullback h hS) hS'c hgA]

/-- Decreasing continuity of `dd^c(w S)` for a positive closed base `S`. -/
theorem weakTendsto_ddcMul_of_antitone {U : Opens (ComplexModel N)}
    {S : LocalProductCurrent N U (r + 1)} (hS : IsPositive S) (hSc : IsClosedCurrent S)
    {f : ℕ → ComplexModel N → ℝ} {w : ComplexModel N → ℝ}
    (hf : ∀ j, IsLocallyBoundedPshOn U (f j)) (hw : IsLocallyBoundedPshOn U w)
    (hanti : ∀ z ∈ (U : Set (ComplexModel N)), Antitone fun j => f j z)
    (hlim : ∀ z ∈ (U : Set (ComplexModel N)), Tendsto (fun j => f j z) atTop (𝓝 (w z))) :
    LocalBedfordTaylorContinuity.WeakTendsto (fun j => ddcMul S (f j)) (ddcMul S w) :=
  LocalBedfordTaylorDecreasing.weakTendsto_btProduct_of_antitone 1 r S hS hSc
    (fun j _ => f j) (fun _ => w) (fun j _ => hf j) (fun _ => hw) (fun _ => hanti)
    (fun _ => hlim)

/-- **`τ^*(dd^c(w S)) = dd^c((w ∘ τ) τ^* S)`** for a locally bounded psh `w` and a positive
closed `S` with closed pull-back. -/
theorem pullback_ddcMul_rel (h : IsBiholomorphicPair A B τ σ)
    {S : LocalProductCurrent N B (r + 1)} (hS : IsPositive S) (hSc : IsClosedCurrent S)
    (hS'c : IsClosedCurrent (pullback h hS)) {w : ComplexModel N → ℝ}
    (hw : IsLocallyBoundedPshOn B w) :
    pullback h (isPositive_ddcMul hS hSc hw).1 = ddcMul (pullback h hS) (fun x => w (τ x)) := by
  ext γ φ
  have hK : IsCompact (τ '' tsupport φ) :=
    φ.hasCompactSupport.image_of_continuousOn (h.holo.continuousOn.mono φ.tsupport_subset)
  have hKB : τ '' tsupport φ ⊆ B :=
    image_subset_iff.mpr fun x hx => h.mapsTo (φ.tsupport_subset hx)
  obtain ⟨V₀, hVo, hKV, hVcl, hVc⟩ := exists_open_between_and_isCompact_closure hK B.isOpen hKB
  set V : Opens (ComplexModel N) := ⟨V₀, hVo⟩ with hVdef
  have hVB : V ≤ B := subset_closure.trans hVcl
  have hVrc : RelativelyCompactIn V B := ⟨hVc, hVcl⟩
  obtain ⟨f, hfs, hfa, hfl⟩ := HolomorphicPullback.exists_decreasingMollifierApproximation hw hVrc
  have h' := isBiholomorphicPair_preOpen h hVB
  have hφA' : tsupport φ ⊆ preOpen h V := fun x hx => ⟨φ.tsupport_subset hx, hKV ⟨x, hx, rfl⟩⟩
  let φ' : 𝓓(preOpen h V, ℝ) := ⟨φ, φ.contDiff, φ.hasCompactSupport, hφA'⟩
  have hext : extTest (preOpen_le h V) φ' = φ := by
    ext x
    rw [extTest_apply]
    rfl
  have hwV : IsLocallyBoundedPshOn V w := isLocallyBoundedPshOn_mono hw hVB
  have hfV : ∀ j, IsLocallyBoundedPshOn V (f j) := fun j =>
    isLocallyBoundedPshOn_of_isSmoothPshOn (hfs j)
  set SV := restrict hVB S
  have hSV : IsPositive SV := isPositive_restrict hS hVB
  have hSVc : IsClosedCurrent SV := isClosedCurrent_restrict hSc hVB
  have hpbV : pullback h' hSV = restrict (preOpen_le h V) (pullback h hS) :=
    pullback_restrict h hS hVB
  have hSV'c : IsClosedCurrent (pullback h' hSV) := by
    rw [hpbV]
    exact isClosedCurrent_restrict hS'c _
  -- the left side, on `A ∩ τ⁻¹(V)`
  have e1 : pullback h (isPositive_ddcMul hS hSc hw).1 γ φ =
      pullback h' (isPositive_ddcMul hSV hSVc hwV).1 γ φ' := by
    rw [← hext, ← LocalBedfordTaylorLocality.restrict_apply, ← pullback_restrict h _ hVB]
    have e : restrict hVB (ddcMul S w) = ddcMul SV w := (ddcMul_restrict hS hVB hw).symm
    rw [pullback_congr' h' _ (isPositive_ddcMul hSV hSVc hwV).1 e]
  -- the limits
  have hpb := weakTendsto_pullback h' (fun j => (isPositive_ddcMul hSV hSVc (hfV j)).1)
    (isPositive_ddcMul hSV hSVc hwV).1
    (weakTendsto_ddcMul_of_antitone hSV hSVc hfV hwV hfa hfl) γ φ'
  have hsm : ∀ j, pullback h' (isPositive_ddcMul hSV hSVc (hfV j)).1 =
      ddcMul (pullback h' hSV) (fun x => f j (τ x)) := fun j =>
    pullback_ddcMul_of_smooth h' hSV hSVc hSV'c (hfs j)
  have hconvA := weakTendsto_ddcMul_of_antitone (isPositive_pullback h' hSV) hSV'c
    (fun j => isLocallyBoundedPshOn_comp' h' (hfV j)) (isLocallyBoundedPshOn_comp' h' hwV)
    (fun z hz => hfa (τ z) hz.2) (fun z hz => hfl (τ z) hz.2) γ φ'
  have e2 : pullback h' (isPositive_ddcMul hSV hSVc hwV).1 γ φ' =
      ddcMul (pullback h' hSV) (fun x => w (τ x)) γ φ' := by
    refine tendsto_nhds_unique hpb ?_
    simp only [hsm]
    exact hconvA
  -- back on `A`
  rw [e1, e2, hpbV, ddcMul_restrict (isPositive_pullback h hS) (preOpen_le h V)
    (isLocallyBoundedPshOn_comp' h hw), LocalBedfordTaylorLocality.restrict_apply, hext]

end Bounded

/-! ### The relative Bedford–Taylor product -/

/-- **Biholomorphic invariance of the relative Bedford–Taylor product**
(FPT `prop:bt-positive-recursion` (5)): for a positive closed `S` on `B` whose pull-back is closed
and locally bounded psh `u₁, …, u_q` on `B`,
`τ^*(dd^c u₁ ∧ ⋯ ∧ dd^c u_q ∧ S) = dd^c(u₁ ∘ τ) ∧ ⋯ ∧ dd^c(u_q ∘ τ) ∧ τ^* S`. -/
theorem pullback_btProduct_rel (h : IsBiholomorphicPair A B τ σ) :
    ∀ (q r : ℕ) (u : Fin q → ComplexModel N → ℝ) (S : LocalProductCurrent N B (r + q))
      (hS : IsPositive S) (hSc : IsClosedAny (r + q) S)
      (_hS'c : IsClosedAny (r + q) (pullback h hS)) (hu : ∀ i, IsLocallyBoundedPshOn B (u i)),
      pullback h (isPositive_btProduct q r u S hS hSc hu).1 =
        btProduct q r (fun i x => u i (τ x)) (pullback h hS)
  | 0, _, _, _, _, _, _, _ => rfl
  | q + 1, r, u, S, hS, hSc, hS'c, hu => by
    obtain ⟨h1, h2⟩ := isPositive_ddcMul (m := r + q) hS hSc (hu (Fin.last q))
    have hpb := pullback_ddcMul_rel (r := r + q) h hS hSc hS'c (hu (Fin.last q))
    have h2' : IsClosedAny (r + q) (pullback h h1) := by
      rw [hpb]
      exact (isPositive_ddcMul (m := r + q) (isPositive_pullback h hS) hS'c
        (isLocallyBoundedPshOn_comp' h (hu (Fin.last q)))).2
    have ih := pullback_btProduct_rel h q r (Fin.init u) _ h1 h2 h2' fun i => hu _
    refine ih.trans ?_
    rw [btProduct_succ]
    exact congrArg (btProduct q r (fun i x => Fin.init u i (τ x))) hpb

end SGPT.NPP.RelativeBT

/-! ### The product `dd^c u₁ ∧ ⋯ ∧ dd^c u_p ∧ T` on a complex manifold -/

namespace SGPT.NPP

open SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.LocalProductCurrents
open SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorProducts
open SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorLocality
open SGPT.Foundations.Analysis.Pending.LocalCurrentPullback
open SGPT.Foundations.Analysis.Pending.BedfordTaylor
open scoped Manifold

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsManifold (𝓘(ℂ, ComplexModel n)) ∞ M]

/-- **`rmk:extensionBT`, gluing**: for a closed positive current `T` on `M` and locally bounded psh
`u₁, …, u_p`, the chart expressions of `dd^c u₁ ∧ ⋯ ∧ dd^c u_p ∧ T` agree on overlaps (the
expression in `e` is the pull-back of the expression in `f` along the coordinate change), by the
biholomorphic invariance of relative Bedford–Taylor products
(`RelativeBT.pullback_btProduct_rel`). -/
theorem bedfordTaylorRelInChart_compatible {p r : ℕ} (T : PositiveCurrent n M (r + p))
    (hT : T.IsClosed) {u : Fin p → M → ℝ} (hu : ∀ i, IsLocallyBoundedPSH (n := n) (u i))
    (e f : ComplexChart n M) :
    restrict (overlapSource_le e f) (bedfordTaylorRelInChart T u e) =
      pullback (chartTransition_isBiholomorphicPair e f)
        (isPositive_restrict (isPositive_bedfordTaylorRelInChart T hT hu f).1
          (overlapTarget_le e f)) := by
  set A := overlapSource e f
  set B := overlapTarget e f
  have hAe : A ≤ chartTarget e := overlapSource_le e f
  have hBf : B ≤ chartTarget f := overlapTarget_le e f
  set τh := chartTransition_isBiholomorphicPair e f
  have hue : ∀ i, MongeAmpere.IsLocallyBoundedPshOn (chartTarget e)
      (fun z => u i (e.val.symm z)) := fun i => (hu i).chart e
  have huf : ∀ i, MongeAmpere.IsLocallyBoundedPshOn (chartTarget f)
      (fun z => u i (f.val.symm z)) := fun i => (hu i).chart f
  have huB : ∀ i, MongeAmpere.IsLocallyBoundedPshOn B (fun z => u i (f.val.symm z)) :=
    fun i => isLocallyBoundedPshOn_mono (huf i) hBf
  set TB := restrict hBf (T.inChart f)
  have hTB : IsPositive TB := isPositive_restrict (T.isPositive f) hBf
  have hTBc : IsClosedAny (r + p) TB := isClosedAny_restrict (hT f) hBf
  have hcomp : restrict hAe (T.inChart e) = pullback τh hTB := T.compatible e f
  have hTBc' : IsClosedAny (r + p) (pullback τh hTB) := by
    rw [← hcomp]
    exact isClosedAny_restrict (hT e) hAe
  have eA : restrict hAe (bedfordTaylorRelInChart T u e) =
      btProduct p r (fun i z => u i (e.val.symm z)) (pullback τh hTB) := by
    rw [bedfordTaylorRelInChart, ← btProduct_restrict hAe p r _ _ (T.isPositive e) (hT e) hue,
      hcomp]
  have eB : restrict hBf (bedfordTaylorRelInChart T u f) =
      btProduct p r (fun i z => u i (f.val.symm z)) TB := by
    rw [bedfordTaylorRelInChart, ← btProduct_restrict hBf p r _ _ (T.isPositive f) (hT f) huf]
  rw [eA, RelativeBT.pullback_congr' τh _ (isPositive_btProduct p r _ TB hTB hTBc huB).1 eB,
    RelativeBT.pullback_btProduct_rel τh p r _ TB hTB hTBc hTBc' huB]
  refine LocalBedfordTaylorDecreasing.btProduct_congr p r _ _ _ fun i x hx => ?_
  have hx' : x ∈ (chartTransition e f).source := hx
  have hxf : e.val.symm x ∈ f.val.source := by
    simp only [chartTransition, OpenPartialHomeomorph.trans_source,
      OpenPartialHomeomorph.symm_source, mem_inter_iff, mem_preimage] at hx'
    exact hx'.2
  simp only [chartTransition, OpenPartialHomeomorph.coe_trans, Function.comp_apply,
    f.val.left_inv hxf]

/-- **`rmk:extensionBT`**: the relative Bedford–Taylor product `dd^c u₁ ∧ ⋯ ∧ dd^c u_p ∧ T` of a
closed positive current `T` of bidimension `(r + p, r + p)` on the complex manifold `M` and
locally bounded psh `u₁, …, u_p`, a positive current of bidimension `(r, r)` on `M` whose chart
expressions are the recursive local products `bedfordTaylorRelInChart`. -/
def bedfordTaylorRel {p r : ℕ} (T : PositiveCurrent n M (r + p)) (hT : T.IsClosed)
    (u : Fin p → M → ℝ) (hu : ∀ i, IsLocallyBoundedPSH (n := n) (u i)) : PositiveCurrent n M r where
  inChart e := bedfordTaylorRelInChart T u e
  isPositive e := (isPositive_bedfordTaylorRelInChart T hT hu e).1
  compatible e f := bedfordTaylorRelInChart_compatible T hT hu e f

theorem bedfordTaylorRel_inChart {p r : ℕ} (T : PositiveCurrent n M (r + p)) (hT : T.IsClosed)
    (u : Fin p → M → ℝ) (hu : ∀ i, IsLocallyBoundedPSH (n := n) (u i)) (e : ComplexChart n M) :
    (bedfordTaylorRel T hT u hu).inChart e = bedfordTaylorRelInChart T u e := rfl

/-- The relative Bedford–Taylor product is a **closed** positive current. -/
theorem isClosed_bedfordTaylorRel {p r : ℕ} (T : PositiveCurrent n M (r + p)) (hT : T.IsClosed)
    (u : Fin p → M → ℝ) (hu : ∀ i, IsLocallyBoundedPSH (n := n) (u i)) :
    (bedfordTaylorRel T hT u hu).IsClosed :=
  fun e => (isPositive_bedfordTaylorRelInChart T hT hu e).2

end SGPT.NPP
