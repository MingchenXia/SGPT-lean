import SGPT.Foundations.Analysis.Pending.ProductStokesLevi
import SGPT.Foundations.Analysis.Pending.ContinuousThetaPsh

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Stokes on `V × X`: `R_α = m [V] ∧ a + ddᶜ v` on the Levi test forms

Source: Demailly--Păun, proof of Theorem 2.12 (`dp04-kahler-cone:2.12`), Boucksom, proof of
Theorem 4.8 (`bou02-volume:4.8`), in the GRAPH form of the TN.4 plan (§1 F6 "(P) GRAPH ROUTE",
step U3): Boucksom's Lemma 4.10 is run on `V × X`
(`V` a blowup of `X`, same dimension `n = q + 1`) with the class `p₁^*a + p₂^*c`.

This is `ProductStokesLevi` (the case `V = X`, `a = c = b`) for two different factors: for
`α = p₁^*a + p₂^*c + ddᶜg` on `V × X` and a Kähler form `ω_X` on `X`, the fibre integral
`R = p₁_*([V × X] ∧ αⁿ ∧ p₂^*ω_X)` satisfies the Levi identity
`R = m · a + ddᶜ v` on the Levi test forms of `V`, with `m = n ∫_X c^{n-1} ∧ ω_X` and the
continuous fibre potential `v = fibreV` (`leviTestIdentity_fibrePushforward`), and `v` is an
`(m a)`-psh FUNCTION when `α ≥ 0` (`thetaPlurisubharmonic_fibreV`).  The proofs are those of
`ProductStokesLevi` and `FibrePotentialKahlerLimit` with the first factor `V` and the second `X`;
all the underlying tools (`VerticalDensityFactorization`, `FibrePushforwardProductForm`,
`SlotFormCompactIBP`, `FibrePotentialLevi`) are already stated for two factors.
-/

noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ContDiff Distributions

namespace SGPT.Foundations.Analysis.Pending.TwoFactorStokesLevi

open FirstPass FirstPass.MongeAmpere FirstPass.PositiveClasses StronglyPositiveForms
  ProductTestForms PositiveProductCurrents IntegrationCurrent TopDegreeDensity
  SmoothCurrentTraceMeasure CurrentTraceMeasure SmoothDDCForm ChartPartition SlotTestForms
  ManifoldTubePositivity DirectionalLeviDensity PositivityLeviLink ClosedProductCurrents
  FibrePotentialLevi VerticalDensityFactorization FibrePushforwardProductForm ProductStokesLevi

open scoped ProductComplexManifold Manifold
open ProductComplexManifold ProductMixedMeasure DiagonalFibreIntegration

variable {q : ℕ} {V : Type*} [TopologicalSpace V] [ChartedSpace (ComplexModel (q + 1)) V]
  [IsComplexManifold (q + 1) V] {X : Type*} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (q + 1)) X] [IsComplexManifold (q + 1) X]

/-- The lifted test function `h = (φ ∘ e) ∘ p₁` on `V × X`. -/
def liftTest (e : ComplexChart (q + 1) V) (φ : 𝓓(chartTarget e, ℝ)) : V × X → ℝ :=
  fun p => chartExtend e φ p.1

theorem chartSmooth_liftTest (e : ComplexChart (q + 1) V) (φ : 𝓓(chartTarget e, ℝ)) :
    ChartSmooth (n := (q + 1) + (q + 1)) (liftTest (X := X) e φ) :=
  chartSmooth_comp contMDiff_fst (chartSmooth_testFunction e φ)

/-- The fibre family `p₁^*β_a, …, p₁^*β_a, p₂^*ω_X` (`q + 1` closed slots). -/
def fibreFam (wX : KahlerBackground (q + 1) X) (e : ComplexChart (q + 1) V)
    (ψ : 𝓓(chartTarget e, ℝ)) (a : ComplexModel (q + 1)) :
    Fin (q + 1) → ClosedRealOneOneForm ((q + 1) + (q + 1)) (V × X) :=
  Fin.snoc (fun _ : Fin q => ClosedRealOneOneForm.pullback contMDiff_fst (leviSlot e ψ a))
    (ClosedRealOneOneForm.pullback contMDiff_snd wX.form)

/-- The test form `p₁^*((φ ∘ e) β_a^q) ∧ p₂^*ω_X` against which `Θ` is evaluated. -/
def fibreLeviTest (wX : KahlerBackground (q + 1) X) (e : ComplexChart (q + 1) V)
    (ψ φ : 𝓓(chartTarget e, ℝ)) (a : ComplexModel (q + 1)) :
    testSpace ((q + 1) + (q + 1)) (V × X) (q + 1) :=
  wedgeTestLM (isTypeOneOne_pullback contMDiff_snd wX.form.2.2) q
    (pullbackTestLM contMDiff_fst q (leviTest e ψ a φ))

theorem fibreFam_coeff (wX : KahlerBackground (q + 1) X) (e : ComplexChart (q + 1) V)
    (ψ : 𝓓(chartTarget e, ℝ)) (a : ComplexModel (q + 1))
    (E : ComplexChart ((q + 1) + (q + 1)) (V × X)) (z : ComplexModel ((q + 1) + (q + 1))) :
    (fun j => (fibreFam wX e ψ a j).val.coeff E z) =
      Fin.snoc (fun _ : Fin q =>
        (SmoothRealForm.pullback contMDiff_fst (leviSlot e ψ a).val).coeff E z)
        ((SmoothRealForm.pullback contMDiff_snd wX.form.val).coeff E z) := by
  funext j
  refine Fin.lastCases ?_ (fun j => ?_) j
  · simp [fibreFam]
  · simp [fibreFam]

/-- The coefficient of the fibre test form: `h · p₁^*β_a ∧ ⋯ ∧ p₁^*β_a ∧ p₂^*ω_X`. -/
theorem fibreLeviTest_coeff (wX : KahlerBackground (q + 1) X) (e : ComplexChart (q + 1) V)
    (ψ φ : 𝓓(chartTarget e, ℝ)) (a : ComplexModel (q + 1))
    (E : ComplexChart ((q + 1) + (q + 1)) (V × X)) (z : ComplexModel ((q + 1) + (q + 1))) :
    ((fibreLeviTest wX e ψ φ a : testSpace ((q + 1) + (q + 1)) (V × X) (q + 1)) :
        SmoothRealForm ((q + 1) + (q + 1)) (V × X) (2 * (q + 1))).coeff E z =
      liftTest e φ (E.val.symm z) •
        wedgeProd (q + 1) (fun j => (fibreFam wX e ψ a j).val.coeff E z) := by
  rw [fibreFam_coeff, fibreLeviTest, coe_fibreTest wX.form.2.2, wedgeTwo_coeff]
  have hη : ((leviTest e ψ a φ : testSpace (q + 1) V q) : SmoothRealForm (q + 1) V (2 * q)) =
      smulFun (chartExtend e φ) (chartSmooth_testFunction e φ) (formPow (leviSlot e ψ a).val q) :=
    rfl
  rw [hη, pullback_smulFun, pullback_formPow, smulFun_coeff, formPow_coeff,
    formPower_eq_wedgeProd, coordinateWedge_smul_left, wedgeProd_snoc]
  rfl

/-- The density of `Ψ ∧ γ^{q+1}` at a chart point. -/
theorem topDensity_chain_fibreLeviTest (wX : KahlerBackground (q + 1) X)
    (e : ComplexChart (q + 1) V) (ψ φ : 𝓓(chartTarget e, ℝ)) (a : ComplexModel (q + 1))
    (γ : ClosedRealOneOneForm ((q + 1) + (q + 1)) (V × X))
    (E : ComplexChart ((q + 1) + (q + 1)) (V × X)) (z : ComplexModel ((q + 1) + (q + 1))) :
    topDensity (((chainTestLM (q + 1) (fun _ => γ.val) (fun _ => γ.2.2) (q + 1)
        (fibreLeviTest wX e ψ φ a) : testSpace ((q + 1) + (q + 1)) (V × X) ((q + 1) + (q + 1))) :
          SmoothRealForm ((q + 1) + (q + 1)) (V × X) (2 * ((q + 1) + (q + 1)))).coeff E z) =
      liftTest e φ (E.val.symm z) * actualMixedTopDensity
        (Fin.append (fun j => (fibreFam wX e ψ a j).val.coeff E z)
          (fun _ : Fin (q + 1) => γ.val.coeff E z)) := by
  rw [chainTestLM_coeff_eq, fibreLeviTest_coeff, map_smul, coordChain_wedgeProd, topDensity_smul,
    topDensity_wedgeProd]

/-- The density of the slot form `h ddᶜg ∧ p₁^*β_a^q ∧ p₂^*ω_X ∧ α^k ∧ A^{q-k}` at a chart point. -/
theorem topDensity_slot_fibre (wX : KahlerBackground (q + 1) X) (e : ComplexChart (q + 1) V)
    (ψ φ : 𝓓(chartTarget e, ℝ)) (a : ComplexModel (q + 1))
    (A : ClosedRealOneOneForm ((q + 1) + (q + 1)) (V × X)) {g : V × X → ℝ}
    (hg : ChartSmooth (n := (q + 1) + (q + 1)) g) (k : ℕ)
    (E : ComplexChart ((q + 1) + (q + 1)) (V × X)) {z : ComplexModel ((q + 1) + (q + 1))}
    (hz : z ∈ E.val.target) :
    topDensity (((slotForm (smulFun (liftTest e φ) (chartSmooth_liftTest e φ) (ddcForm g hg))
        (q + 1 + q) (Fin.append (fibreFam wX e ψ a) (teleForms A (A + ddcClosedForm g hg) k q)) :
          testSpace ((q + 1) + (q + 1)) (V × X) ((q + 1) + (q + 1))) :
            SmoothRealForm ((q + 1) + (q + 1)) (V × X) (2 * ((q + 1) + (q + 1)))).coeff E z) =
      liftTest e φ (E.val.symm z) * actualMixedTopDensity
        (Fin.cons (smoothDDC (fun y => g (E.val.symm y)) z)
          (Fin.append (fun j => (fibreFam wX e ψ a j).val.coeff E z)
            (teleSlots (A.val.coeff E z) (smoothDDC (fun y => g (E.val.symm y)) z) k q)) :
          Fin ((q + 1) + (q + 1)) → RealForm ((q + 1) + (q + 1)) 2) := by
  set D := smoothDDC (fun y => g (E.val.symm y)) z with hD
  have hg2 : ContDiffAt ℝ 2 (fun y => g (E.val.symm y)) z :=
    ((hg E).contDiffAt (E.val.open_target.mem_nhds hz)).of_le (WithTop.coe_le_coe.mpr le_top)
  have hslots : (fun j => (Fin.append (fibreFam wX e ψ a)
      (teleForms A (A + ddcClosedForm g hg) k q) j).val.coeff E z) =
      Fin.append (fun j => (fibreFam wX e ψ a j).val.coeff E z)
        (teleSlots (A.val.coeff E z) D k q) := by
    funext j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · simp only [Fin.append_left]
    · simp only [Fin.append_right, teleForms, teleSlots]
      split_ifs
      · rw [ClosedRealOneOneForm.coeff_add, hD]
        rfl
      · rfl
  have hfirst : pi11 ((smulFun (liftTest e φ) (chartSmooth_liftTest e φ) (ddcForm g hg)).coeff E z) =
      liftTest e φ (E.val.symm z) • D := by
    rw [smulFun_coeff, pi11_smul, ddcForm_coeff, ← hD, pi11_eq_self (MongeAmpere.smoothDDC_isOneOne hg2)]
  rw [slotForm_coeff, hfirst, hslots]
  change topDensity (wedgeProd ((q + 1) + (q + 1)) (Fin.cons (liftTest e φ (E.val.symm z) • D)
    (Fin.append (fun j => (fibreFam wX e ψ a j).val.coeff E z)
      (teleSlots (A.val.coeff E z) D k q)))) = _
  rw [topDensity_wedgeProd]
  have hupd : (Fin.cons (liftTest e φ (E.val.symm z) • D)
      (Fin.append (fun j => (fibreFam wX e ψ a j).val.coeff E z) (teleSlots (A.val.coeff E z) D k q)) :
        Fin ((q + 1) + (q + 1)) → RealForm ((q + 1) + (q + 1)) 2) =
      Function.update (Fin.cons D (Fin.append (fun j => (fibreFam wX e ψ a j).val.coeff E z)
        (teleSlots (A.val.coeff E z) D k q))) 0 (liftTest e φ (E.val.symm z) • D) := by
    rw [Fin.update_cons_zero]
  rw [hupd, ← actualMixedTopDensityMultilinear_apply, MultilinearMap.map_update_smul,
    Fin.update_cons_zero, smul_eq_mul, actualMixedTopDensityMultilinear_apply]

variable [CompactSpace V] [MeasurableSpace V] [BorelSpace V]
  [CompactSpace X] [MeasurableSpace X] [BorelSpace X]

/-- **Telescoping on `V × X`**: for `α = A + ddᶜg`,
`[V × X] ∧ α^{q+1} (Ψ) - [V × X] ∧ A^{q+1} (Ψ) = Σ_k [V × X](h ddᶜg ∧ p₁^*β_a^q ∧ p₂^*ω_X ∧ α^k ∧ A^{q-k})`
on the fibre test form `Ψ = p₁^*((φ ∘ e) β_a^q) ∧ p₂^*ω_X`, `h = φ ∘ e ∘ p₁`. -/
theorem smoothCurrent_sub_eq_sum_slot (wV : KahlerBackground (q + 1) V)
    (wX : KahlerBackground (q + 1) X)
    (A : ClosedRealOneOneForm ((q + 1) + (q + 1)) (V × X)) {g : V × X → ℝ}
    (hg : ChartSmooth (n := (q + 1) + (q + 1)) g) (e : ComplexChart (q + 1) V)
    (ψ φ : 𝓓(chartTarget e, ℝ)) (a : ComplexModel (q + 1)) :
    smoothCurrent (q := q + 1) (p := q + 1) (prodKahlerBackground wV wX)
        (fun _ => A + ddcClosedForm g hg) (fibreLeviTest wX e ψ φ a) -
      smoothCurrent (q := q + 1) (p := q + 1) (prodKahlerBackground wV wX) (fun _ => A)
        (fibreLeviTest wX e ψ φ a) =
      ∑ k : Fin (q + 1), integrationCurrent (prodKahlerBackground wV wX)
        (slotForm (smulFun (liftTest e φ) (chartSmooth_liftTest e φ) (ddcForm g hg)) (q + 1 + q)
          (Fin.append (fibreFam wX e ψ a) (teleForms A (A + ddcClosedForm g hg) k q))) := by
  set W := prodKahlerBackground wV wX
  rw [smoothCurrent_apply, smoothCurrent_apply, integrationCurrent_apply, integrationCurrent_apply,
    ← integral_sub (integrable_topRatio _ _) (integrable_topRatio _ _)]
  simp only [integrationCurrent_apply]
  rw [← integral_finsetSum _ fun k _ => integrable_topRatio _ _]
  refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
  simp only [topRatio, chartRatio]
  set E := complexChartAt (n := (q + 1) + (q + 1)) p
  have hz : E.val p ∈ E.val.target := E.val.map_source (mem_complexChartAt_source p)
  rw [← sub_div, ← Finset.sum_div, topDensity_chain_fibreLeviTest,
    topDensity_chain_fibreLeviTest]
  congr 1
  simp_rw [topDensity_slot_fibre wX e ψ φ a A hg _ E hz]
  rw [← mul_sub, ← Finset.mul_sum]
  congr 1
  have hα : (A + ddcClosedForm g hg).val.coeff E (E.val p) =
      A.val.coeff E (E.val p) + smoothDDC (fun y => g (E.val.symm y)) (E.val p) := by
    rw [ClosedRealOneOneForm.coeff_add]
    rfl
  rw [hα]
  exact actualMixedTopDensity_telescope _ _ _

omit [CompactSpace V] [MeasurableSpace V] [BorelSpace V] [CompactSpace X] [MeasurableSpace X]
  [BorelSpace X] in
/-- In a product chart, `ddᶜ h = p₁^* ddᶜ(φ ∘ e)`. -/
theorem smoothDDC_liftTest (e : ComplexChart (q + 1) V) (φ : 𝓓(chartTarget e, ℝ))
    (e₁ : ComplexChart (q + 1) V) (e₂ : ComplexChart (q + 1) X) {z₁ z₂ : ComplexModel (q + 1)}
    (hz₁ : z₁ ∈ e₁.val.target) :
    smoothDDC (fun y => liftTest e φ ((prodComplexChart e₁ e₂).val.symm y))
        (prodModelEquiv (q + 1) (q + 1) (z₁, z₂)) =
      ((ddcTest e φ).val.coeff e₁ z₁).compContinuousLinearMap (projFst (q + 1) (q + 1)) := by
  set ρ : ComplexModel (q + 1) → ℝ := fun y₁ => chartExtend e φ (e₁.val.symm y₁) with hρ
  have hfun : (fun y => liftTest (X := X) e φ ((prodComplexChart e₁ e₂).val.symm y)) =
      fun y => ρ (projFst (q + 1) (q + 1) y) := rfl
  have hF : ContDiff ℂ ∞ (projFst (q + 1) (q + 1) : ComplexModel ((q + 1) + (q + 1)) →
      ComplexModel (q + 1)) :=
    ((ContinuousLinearMap.fst ℂ (ComplexModel (q + 1)) (ComplexModel (q + 1))).comp
      ((prodModelEquiv (q + 1) (q + 1)).symm :
        ComplexModel ((q + 1) + (q + 1)) →L[ℂ] _)).contDiff
  have hproj : projFst (q + 1) (q + 1) (prodModelEquiv (q + 1) (q + 1) (z₁, z₂)) = z₁ := by
    simp [projFst_apply]
  have hU : IsOpen ((projFst (q + 1) (q + 1)) ⁻¹' e₁.val.target) :=
    e₁.val.open_target.preimage (projFst (q + 1) (q + 1)).continuous
  rw [hfun, HolomorphicDDC.smoothDDC_comp hU e₁.val.open_target hF.contDiffOn
    (chartSmooth_testFunction e φ e₁) (fun y hy => hy) (by simpa [hproj] using hz₁), hproj,
    ContinuousLinearMap.fderiv]
  rfl

/-- `p₂^*ω_X, α, …, α, A, …, A` (`k` copies of `α`): the vertical slots of the `k`-th term. -/
def vertSlots (wX : KahlerBackground (q + 1) X)
    (A α : ClosedRealOneOneForm ((q + 1) + (q + 1)) (V × X)) (k : ℕ) :
    Fin (q + 1) → ClosedRealOneOneForm ((q + 1) + (q + 1)) (V × X) :=
  Fin.cons (ClosedRealOneOneForm.pullback contMDiff_snd wX.form) (teleForms A α k q)

/-- **The integration by parts output is the Fubini form**: on `V × X`,
`[V × X](g ddᶜh ∧ p₁^*β_a^q ∧ p₂^*ω_X ∧ α^k ∧ A^{q-k}) =
[V × X](g · p₁^*(ddᶜ(φ ∘ e) ∧ β_a^q) ∧ p₂^*ω_X ∧ α^k ∧ A^{q-k})`. -/
theorem integrationCurrent_slot_ibp_eq_chain (wV : KahlerBackground (q + 1) V)
    (wX : KahlerBackground (q + 1) X) (A α : ClosedRealOneOneForm ((q + 1) + (q + 1)) (V × X))
    {g : V × X → ℝ} (hg : ChartSmooth (n := (q + 1) + (q + 1)) g) (e : ComplexChart (q + 1) V)
    (ψ φ : 𝓓(chartTarget e, ℝ)) (a : ComplexModel (q + 1)) (k : ℕ) :
    integrationCurrent (prodKahlerBackground wV wX)
        (slotForm (smulFun g hg (ddcForm (liftTest e φ) (chartSmooth_liftTest e φ))) (q + 1 + q)
          (Fin.append (fibreFam wX e ψ a) (teleForms A α k q))) =
      integrationCurrent (prodKahlerBackground wV wX)
        (chainTestLM (q + 1) (fun j => (vertSlots wX A α k j).val)
          (fun j => (vertSlots wX A α k j).2.2)
          (q + 1) (smulTest g hg (pullbackTestLM contMDiff_fst (q + 1) (leviDDCTest e ψ φ a)))) := by
  rw [integrationCurrent_apply, integrationCurrent_apply]
  refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
  obtain ⟨x, y⟩ := p
  simp only [topRatio, chartRatio]
  set e₁ := complexChartAt (n := q + 1) x
  set e₂ := complexChartAt (n := q + 1) y
  have hz₁ : e₁.val x ∈ e₁.val.target := e₁.val.map_source (mem_complexChartAt_source x)
  have hz₂ : e₂.val y ∈ e₂.val.target := e₂.val.map_source (mem_complexChartAt_source y)
  have hE : complexChartAt (n := (q + 1) + (q + 1)) (x, y) = prodComplexChart e₁ e₂ := rfl
  have hEx : (prodComplexChart e₁ e₂).val (x, y) =
      prodModelEquiv (q + 1) (q + 1) (e₁.val x, e₂.val y) := rfl
  have hsrc : (x, y) ∈ (prodComplexChart e₁ e₂).val.source :=
    hE ▸ mem_complexChartAt_source (x, y)
  have hg' : g ((prodComplexChart e₁ e₂).val.symm
      (prodModelEquiv (q + 1) (q + 1) (e₁.val x, e₂.val y))) = g (x, y) := by
    rw [← hEx, (prodComplexChart e₁ e₂).val.left_inv hsrc]
  rw [hE, hEx]
  congr 1
  -- the two coefficients
  set z := prodModelEquiv (q + 1) (q + 1) (e₁.val x, e₂.val y)
  set Dφ := (ddcTest e φ).val.coeff e₁ (e₁.val x)
  set B := (leviSlot e ψ a).val.coeff e₁ (e₁.val x)
  set W := wX.form.val.coeff e₂ (e₂.val y)
  set T := fun j : Fin q => (teleForms A α k q j).val.coeff (prodComplexChart e₁ e₂) z
  have hφ2 : ContDiffAt ℝ 2 (fun y₁ => chartExtend e φ (e₁.val.symm y₁)) (e₁.val x) :=
    ((chartSmooth_testFunction e φ e₁).contDiffAt (e₁.val.open_target.mem_nhds hz₁)).of_le
      (WithTop.coe_le_coe.mpr le_top)
  have hDφ : IsOneOne Dφ := MongeAmpere.smoothDDC_isOneOne hφ2
  have hfam : (fun j => (fibreFam wX e ψ a j).val.coeff (prodComplexChart e₁ e₂) z) =
      Fin.snoc (fun _ : Fin q => B.compContinuousLinearMap (projFst (q + 1) (q + 1)))
        (W.compContinuousLinearMap (projSnd (q + 1) (q + 1))) := by
    rw [fibreFam_coeff, pullback_fst_coeff _ e₁ e₂ hz₁ hz₂, pullback_snd_coeff _ e₁ e₂ hz₁ hz₂]
  have hvert : (fun j => (vertSlots wX A α k j).val.coeff (prodComplexChart e₁ e₂) z) =
      Fin.cons (W.compContinuousLinearMap (projSnd (q + 1) (q + 1))) T := by
    funext j
    refine Fin.cases ?_ (fun j => ?_) j
    · simp only [vertSlots, Fin.cons_zero, ClosedRealOneOneForm.pullback_val]
      exact pullback_snd_coeff _ e₁ e₂ hz₁ hz₂
    · simp only [vertSlots, Fin.cons_succ, T]
  -- left side
  have hL : topDensity (((slotForm (smulFun g hg (ddcForm (liftTest e φ) (chartSmooth_liftTest e φ)))
      (q + 1 + q) (Fin.append (fibreFam wX e ψ a) (teleForms A α k q)) :
        testSpace ((q + 1) + (q + 1)) (V × X) ((q + 1) + (q + 1))) :
          SmoothRealForm ((q + 1) + (q + 1)) (V × X) (2 * ((q + 1) + (q + 1)))).coeff
            (prodComplexChart e₁ e₂) z) =
      g (x, y) * actualMixedTopDensity (Fin.cons (Dφ.compContinuousLinearMap (projFst (q + 1) (q + 1)))
        (Fin.append (Fin.snoc (fun _ : Fin q => B.compContinuousLinearMap (projFst (q + 1) (q + 1)))
          (W.compContinuousLinearMap (projSnd (q + 1) (q + 1)))) T) :
            Fin ((q + 1) + (q + 1)) → RealForm ((q + 1) + (q + 1)) 2) := by
    have hslots : (fun j => (Fin.append (fibreFam wX e ψ a) (teleForms A α k q) j).val.coeff
        (prodComplexChart e₁ e₂) z) =
        Fin.append (Fin.snoc (fun _ : Fin q => B.compContinuousLinearMap (projFst (q + 1) (q + 1)))
          (W.compContinuousLinearMap (projSnd (q + 1) (q + 1)))) T := by
      rw [← hfam]
      funext j
      refine Fin.addCases (fun i => ?_) (fun i => ?_) j
      · simp only [Fin.append_left]
      · simp only [Fin.append_right, T]
    have hfirst : pi11 ((smulFun g hg (ddcForm (liftTest e φ) (chartSmooth_liftTest e φ))).coeff
        (prodComplexChart e₁ e₂) z) =
        g (x, y) • Dφ.compContinuousLinearMap (projFst (q + 1) (q + 1)) := by
      rw [smulFun_coeff, hg', pi11_smul, ddcForm_coeff, smoothDDC_liftTest e φ e₁ e₂ hz₁,
        pi11_eq_self (isOneOne_comp_projFst hDφ)]
    rw [slotForm_coeff, hfirst, hslots]
    change topDensity (wedgeProd ((q + 1) + (q + 1)) (Fin.cons
      (g (x, y) • Dφ.compContinuousLinearMap (projFst (q + 1) (q + 1)))
      (Fin.append (Fin.snoc (fun _ : Fin q => B.compContinuousLinearMap (projFst (q + 1) (q + 1)))
        (W.compContinuousLinearMap (projSnd (q + 1) (q + 1)))) T))) = _
    rw [topDensity_wedgeProd, ← Fin.update_cons_zero (Dφ.compContinuousLinearMap (projFst (q + 1) (q + 1))),
      ← actualMixedTopDensityMultilinear_apply, MultilinearMap.map_update_smul,
      Fin.update_cons_zero, smul_eq_mul, actualMixedTopDensityMultilinear_apply]
  -- right side
  have hR : topDensity (((chainTestLM (q + 1) (fun j => (vertSlots wX A α k j).val)
      (fun j => (vertSlots wX A α k j).2.2) (q + 1)
        (smulTest g hg (pullbackTestLM contMDiff_fst (q + 1) (leviDDCTest e ψ φ a))) :
          testSpace ((q + 1) + (q + 1)) (V × X) ((q + 1) + (q + 1))) :
            SmoothRealForm ((q + 1) + (q + 1)) (V × X) (2 * ((q + 1) + (q + 1)))).coeff
              (prodComplexChart e₁ e₂) z) =
      g (x, y) * actualMixedTopDensity (Fin.append
        (Fin.cons (Dφ.compContinuousLinearMap (projFst (q + 1) (q + 1)))
          (fun _ : Fin q => B.compContinuousLinearMap (projFst (q + 1) (q + 1))))
        (Fin.cons (W.compContinuousLinearMap (projSnd (q + 1) (q + 1))) T)) := by
    rw [coeff_chain_pullback _ _ g hg e₁ e₂ hz₁ hz₂, hg', topDensity_smul, hvert]
    have hΛ : ((leviDDCTest e ψ φ a : testSpace (q + 1) V (q + 1)) :
        SmoothRealForm (q + 1) V (2 * (q + 1))).coeff e₁ (e₁.val x) =
        wedgeProd (q + 1) (Fin.cons Dφ fun _ : Fin q => B) := by
      rw [leviDDCTest, slotForm_coeff, pi11_eq_self hDφ]
    rw [hΛ, wedgeProd_compContinuousLinearMap, map_cons_comp, coordChain_wedgeProd,
      topDensity_wedgeProd]
  rw [hL, hR, append_cons_cons]

/-! ### The `ε`-level Levi identity on `V × X` -/

/-- **The fibre potential of `R_α`**: `v = Σ_k v_k`, `v_k` the fibre potential of `g` against the
vertical slots `p₂^*ω_X, α^k, A^{q-k}`. -/
def fibreV (wV : KahlerBackground (q + 1) V) (wX : KahlerBackground (q + 1) X)
    (A α : ClosedRealOneOneForm ((q + 1) + (q + 1)) (V × X)) (g : V × X → ℝ) (x : V) : ℝ :=
  ∑ k : Fin (q + 1), fibrePotential wV wX (vertSlots wX A α k) g x

theorem continuous_fibreV (wV : KahlerBackground (q + 1) V) (wX : KahlerBackground (q + 1) X)
    (A α : ClosedRealOneOneForm ((q + 1) + (q + 1)) (V × X)) {g : V × X → ℝ} (hg : Continuous g) :
    Continuous (fibreV wV wX A α g) :=
  continuous_finsetSum _ fun _ _ => continuous_fibrePotential wV wX _ hg

theorem locallyIntegrableOn_fibreV (wV : KahlerBackground (q + 1) V)
    (wX : KahlerBackground (q + 1) X)
    (A α : ClosedRealOneOneForm ((q + 1) + (q + 1)) (V × X)) {g : V × X → ℝ} (hg : Continuous g)
    (e : ComplexChart (q + 1) V) :
    LocallyIntegrableOn (fun z => fibreV wV wX A α g (e.val.symm z)) (chartTarget e) volume :=
  ((continuous_fibreV wV wX A α hg).comp_continuousOn e.val.continuousOn_symm).locallyIntegrableOn
    (chartTarget e).isOpen.measurableSet

/-- **The `ε`-level Levi identity on `V × X`** (step U3 of the graph route): for closed real
`(1,1)`-forms `a` on `V`, `c` on `X` and a chart-smooth `g` on `V × X`, the current
`R = p₁_*([V × X] ∧ (p₁^*a + p₂^*c + ddᶜg)^{q+1} ∧ p₂^*ω_X)` satisfies `R = m · a + ddᶜ v` on the Levi
test forms of `V`, with `m = (q + 1) ∫_X c^q ∧ ω_X` and the continuous fibre potential `v = fibreV`.
No positivity is assumed. -/
theorem leviTestIdentity_fibrePushforward (wV : KahlerBackground (q + 1) V)
    (wX : KahlerBackground (q + 1) X) (a : ClosedRealOneOneForm (q + 1) V)
    (c : ClosedRealOneOneForm (q + 1) X) {g : V × X → ℝ}
    (hg : ChartSmooth (n := (q + 1) + (q + 1)) g) :
    LeviTestIdentity wV
      (fibrePushforward wX.form.2.2 (smoothCurrent (q := q + 1) (p := q + 1)
        (prodKahlerBackground wV wX) (fun _ => prodForm a c + ddcClosedForm g hg)))
      ((((q + 1 : ℕ) : ℝ) * fibreIntegral wX c wX.form.val) • a)
      (fun e => regularDistribution volume
        (fun z => fibreV wV wX (prodForm a c) (prodForm a c + ddcClosedForm g hg) g (e.val.symm z))
        (locallyIntegrableOn_fibreV wV wX _ _ (ChartSmooth.continuous hg) e)) := by
  intro e ψ φ b hb hφ hψ
  set A := prodForm a c with hAdef
  set α := A + ddcClosedForm g hg with hαdef
  set W := prodKahlerBackground wV wX with hWdef
  have hgc : Continuous g := ChartSmooth.continuous hg
  -- `R(η) = Θ_α(Ψ)` and `Θ_A(Ψ) = m [V] ∧ a (η)`
  have hR : fibrePushforward wX.form.2.2 (smoothCurrent (q := q + 1) (p := q + 1) W (fun _ => α))
      (leviTest e ψ b φ) = smoothCurrent (q := q + 1) (p := q + 1) W (fun _ => α)
        (fibreLeviTest wX e ψ φ b) := rfl
  have hA : smoothCurrent (q := q + 1) (p := q + 1) W (fun _ => A) (fibreLeviTest wX e ψ φ b) =
      (((q + 1 : ℕ) : ℝ) * fibreIntegral wX c wX.form.val) *
        smoothCurrent (q := q) (p := 1) wV ![a] (leviTest e ψ b φ) := by
    have h := congrArg (fun T => T (leviTest e ψ b φ))
      (fibrePushforward_smoothCurrent_prodForm wV wX a c wX.form.2.2)
    simp only [LinearMap.smul_apply, smul_eq_mul] at h
    exact h
  -- telescoping, integration by parts, Fubini
  have htel := smoothCurrent_sub_eq_sum_slot wV wX A hg e ψ φ b
  have hterm : ∀ k : Fin (q + 1), integrationCurrent W
      (slotForm (smulFun (liftTest e φ) (chartSmooth_liftTest e φ) (ddcForm g hg)) (q + 1 + q)
        (Fin.append (fibreFam wX e ψ b) (teleForms A α k q))) =
      ∫ x, fibrePotential wV wX (vertSlots wX A α k) g x *
        topRatio wV.form.val ((leviDDCTest e ψ φ b : testSpace (q + 1) V (q + 1)) :
          SmoothRealForm (q + 1) V (2 * (q + 1))) x ∂(kahlerVolume wV) := by
    intro k
    rw [SlotFormCompactIBP.slotForm_ibp_of_compact (n := (q + 1) + (q + 1)) (M := V × X)
      (T := integrationCurrent W) (k := q + 1 + q)
      (isPositive_integrationCurrent W) (isClosedCurrent_integrationCurrent W) _
      (chartSmooth_liftTest e φ) hg, integrationCurrent_slot_ibp_eq_chain,
      integrationCurrent_chain_pullback]
  have hsum : ∑ k : Fin (q + 1), ∫ x, fibrePotential wV wX (vertSlots wX A α k) g x *
      topRatio wV.form.val ((leviDDCTest e ψ φ b : testSpace (q + 1) V (q + 1)) :
        SmoothRealForm (q + 1) V (2 * (q + 1))) x ∂(kahlerVolume wV) =
      ∫ x, fibreV wV wX A α g x * topRatio wV.form.val ((leviDDCTest e ψ φ b :
        testSpace (q + 1) V (q + 1)) : SmoothRealForm (q + 1) V (2 * (q + 1))) x
          ∂(kahlerVolume wV) := by
    rw [← integral_finsetSum]
    · refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp only [fibreV, Finset.sum_mul]
    · intro k _
      exact ((continuous_fibrePotential wV wX _ hgc).mul
        (continuous_topRatio wV.isKahler.1 _)).integrable_of_hasCompactSupport
          (isCompact_univ.of_isClosed_subset (isClosed_tsupport _) (subset_univ _))
  have hchart := integral_mul_topRatio_leviDDCTest wV hb hψ (continuous_fibreV wV wX A α hgc)
    (locallyIntegrableOn_fibreV wV wX A α hgc e)
  rw [hR, smoothCurrent_smul_apply, ← hA, ← hchart, ← hsum, ← Finset.sum_congr rfl
    (fun k _ => hterm k), ← htel]
  ring

/-- **The `ε`-level link on `V × X`**: if `α = p₁^*a + p₂^*c + ddᶜg ≥ 0` and `θ = m · a` has smooth
local potentials, the chart distributions of the fibre potential are locally `θ`-psh. -/
theorem isLocallyThetaPshDistribution_fibreV (wV : KahlerBackground (q + 1) V)
    (wX : KahlerBackground (q + 1) X) (a : ClosedRealOneOneForm (q + 1) V)
    (c : ClosedRealOneOneForm (q + 1) X) {g : V × X → ℝ}
    (hg : ChartSmooth (n := (q + 1) + (q + 1)) g)
    (hα : ThetaPlurisubharmonic (prodForm a c + ddcClosedForm g hg).val (fun _ => 0))
    (hθ : HasSmoothLocalPotentials ((((q + 1 : ℕ) : ℝ) * fibreIntegral wX c wX.form.val) • a).val)
    (e : ComplexChart (q + 1) V) :
    ThetaPshChartLimitGluing.IsLocallyThetaPshDistribution volume
      ((((q + 1 : ℕ) : ℝ) * fibreIntegral wX c wX.form.val) • a).val e
      (regularDistribution volume
        (fun z => fibreV wV wX (prodForm a c) (prodForm a c + ddcClosedForm g hg) g (e.val.symm z))
        (locallyIntegrableOn_fibreV wV wX _ _ (ChartSmooth.continuous hg) e)) := by
  have hΘ : IsPositive (smoothCurrent (q := q + 1) (p := q + 1) (prodKahlerBackground wV wX)
      (fun _ => prodForm a c + ddcClosedForm g hg)) :=
    isPositive_smoothCurrent _ _ fun _ => hα
  have hP := IsPositive.fibrePushforward wX.form.2.2
    (fun e' z hz => isSemipositiveOneOne_of_isHermitian wX.isKahler.1 e' hz) hΘ
  exact isLocallyThetaPshDistribution_of_leviTest wV hP _ hθ _
    (leviTestIdentity_fibrePushforward wV wX a c hg) e

/-- **The fibre potential of a semipositive `α` is `(m a)`-psh**, `m = (q + 1) ∫_X c^q ∧ ω_X`. -/
theorem thetaPlurisubharmonic_fibreV (wV : KahlerBackground (q + 1) V)
    (wX : KahlerBackground (q + 1) X) (a : ClosedRealOneOneForm (q + 1) V)
    (c : ClosedRealOneOneForm (q + 1) X) {g : V × X → ℝ}
    (hg : ChartSmooth (n := (q + 1) + (q + 1)) g)
    (hα : ThetaPlurisubharmonic (prodForm a c + ddcClosedForm g hg).val (fun _ => 0)) :
    ThetaPlurisubharmonic ((((q + 1 : ℕ) : ℝ) * fibreIntegral wX c wX.form.val) • a).val
      fun x => ((fibreV wV wX (prodForm a c) (prodForm a c + ddcClosedForm g hg) g x : ℝ) : EReal) :=
  ContinuousThetaPsh.thetaPlurisubharmonic_of_continuous_of_isLocallyThetaPshDistribution volume
    (continuous_fibreV wV wX _ _ (ChartSmooth.continuous hg))
    (locallyIntegrableOn_fibreV wV wX _ _ (ChartSmooth.continuous hg))
    fun e => isLocallyThetaPshDistribution_fibreV wV wX a c hg hα
      (LocalPotentials.closedRealOneOne_hasLocalPotentials _) e

end SGPT.Foundations.Analysis.Pending.TwoFactorStokesLevi
