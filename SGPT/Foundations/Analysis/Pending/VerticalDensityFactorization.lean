import SGPT.Foundations.Analysis.Pending.FibrePushforwardProductForm

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The density of `p₁^*Λ ∧ Φ` factors through the vertical part of `Φ`

Source: integration along the fibres of `p₁ : X × Y → X` (Demailly--Păun, proof of Theorem 2.12,
`dp04-kahler-cone:2.12`; Boucksom, proof of Theorem 4.8, `bou02-volume:4.8`).  TN.4 plan, step B6,
finding F6 route (i), piece (i-1): the potential of
`R_ε = p₁_*([X × X] ∧ α_εⁿ ∧ p₂^*ω)` is a fibre integral, and the pairing of `R_ε - m_ε b` with a
test form is computed by Fubini once the density of `p₁^*Λ ∧ Φ` (`Λ` of top degree on the first
factor) is known.

In the coordinates `ℂⁿ⁺ᵐ = ℂⁿ × ℂᵐ`: for `n` real two-forms `P` on `ℂⁿ` and `m` real `(1,1)`-forms
`G` on `ℂⁿ⁺ᵐ` (no product structure),

`D(p₁^*P₀, …, p₁^*P_{n-1}, G₀, …, G_{m-1}) = D(P) · D(ι₂^*G₀, …, ι₂^*G_{m-1})`

with `ι₂(w) = (0, w)` (`actualMixedTopDensity_append_comp_inclSnd`): the scaling
`S_t(x, y) = (t x, y)` multiplies the left side by `t^{2n}` and each `p₁^*P_i` by `t²`, so
`t ↦ D(p₁^*P, S_t^*G)` is constant for `t ≠ 0`; it is continuous, and `S_0 = ι₂ ∘ p₂`, so the value
at `t = 0` is the density of a block family (`ProductMixedMeasure.actualMixedTopDensity_append_comp`).
-/

open Set Filter
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.VerticalDensityFactorization

open FirstPass FirstPass.MongeAmpere StronglyPositiveForms ProductComplexManifold
  ProductMixedMeasure FibrePushforwardProductForm SmoothMixedMeasureDensity TopDegreeDensity

noncomputable section

variable {n m : ℕ}

/-- The inclusion `ℂⁿ → ℂⁿ⁺ᵐ`, `x ↦ (x, 0)`. -/
def inclFst (n m : ℕ) : ComplexModel n →L[ℝ] ComplexModel (n + m) :=
  (((prodModelEquiv n m : (ComplexModel n × ComplexModel m) ≃L[ℂ] ComplexModel (n + m)) :
    (ComplexModel n × ComplexModel m) →L[ℂ] ComplexModel (n + m)).comp
      (ContinuousLinearMap.inl ℂ (ComplexModel n) (ComplexModel m))).restrictScalars ℝ

/-- The inclusion `ℂᵐ → ℂⁿ⁺ᵐ`, `y ↦ (0, y)`. -/
def inclSnd (n m : ℕ) : ComplexModel m →L[ℝ] ComplexModel (n + m) :=
  (((prodModelEquiv n m : (ComplexModel n × ComplexModel m) ≃L[ℂ] ComplexModel (n + m)) :
    (ComplexModel n × ComplexModel m) →L[ℂ] ComplexModel (n + m)).comp
      (ContinuousLinearMap.inr ℂ (ComplexModel n) (ComplexModel m))).restrictScalars ℝ

theorem inclFst_apply (x : ComplexModel n) : inclFst n m x = prodModelEquiv n m (x, 0) := rfl

theorem inclSnd_apply (y : ComplexModel m) : inclSnd n m y = prodModelEquiv n m (0, y) := rfl

theorem inclSnd_smul (c : ℂ) (y : ComplexModel m) : inclSnd n m (c • y) = c • inclSnd n m y := by
  rw [inclSnd_apply, inclSnd_apply, ← map_smul, Prod.smul_mk, smul_zero]

/-- `S_t = t ι₁ p₁ + ι₂ p₂`. -/
theorem scaleFst_eq (t : ℝ) :
    scaleFst n m t = t • (inclFst n m).comp (projFst n m) + (inclSnd n m).comp (projSnd n m) := by
  ext1 v
  rw [scaleFst_apply, add_apply, smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, inclFst_apply, inclSnd_apply,
    projFst_apply, projSnd_apply]
  have h : ((t • ((prodModelEquiv n m).symm v).1, ((prodModelEquiv n m).symm v).2) :
      ComplexModel n × ComplexModel m) =
      (t : ℂ) • (((prodModelEquiv n m).symm v).1, (0 : ComplexModel m)) +
        ((0 : ComplexModel n), ((prodModelEquiv n m).symm v).2) := by
    ext <;> simp [Complex.coe_smul]
  rw [h, map_add, map_smul, ← Complex.coe_smul]

theorem scaleFst_zero : scaleFst n m 0 = (inclSnd n m).comp (projSnd n m) := by
  ext1 v
  rw [scaleFst_eq]
  simp

/-- The pullback of a two-form along `t • L₁ + L₂` is a polynomial in `t`. -/
theorem compContinuousLinearMap_smul_add {k l : ℕ} (G : CoordinateRealTwoForm k)
    (L₁ L₂ : ComplexModel l →L[ℝ] ComplexModel k) (t : ℝ) :
    G.compContinuousLinearMap (t • L₁ + L₂) =
      t ^ 2 • G.compContinuousLinearMap L₁ +
        t • (G.compContinuousLinearMap (L₁ + L₂) - G.compContinuousLinearMap L₁ -
          G.compContinuousLinearMap L₂) + G.compContinuousLinearMap L₂ := by
  ext v
  have hv : v = ![v 0, v 1] := by
    funext i
    fin_cases i <;> rfl
  rw [hv]
  have hc : ∀ L : ComplexModel l →L[ℝ] ComplexModel k,
      ⇑L ∘ (![v 0, v 1] : Fin 2 → ComplexModel l) = ![L (v 0), L (v 1)] := fun L => by
    funext i
    fin_cases i <;> rfl
  simp only [ContinuousAlternatingMap.add_apply, ContinuousAlternatingMap.smul_apply,
    ContinuousAlternatingMap.sub_apply, ContinuousAlternatingMap.compContinuousLinearMap_apply,
    smul_eq_mul]
  simp only [hc, add_apply, smul_apply]
  rw [coordinateFrame_twoForm_add_left, coordinateFrame_twoForm_add_right,
    coordinateFrame_twoForm_add_right, coordinateFrame_twoForm_add_left,
    coordinateFrame_twoForm_add_right, coordinateFrame_twoForm_add_right,
    coordinateFrame_twoForm_smul_left, coordinateFrame_twoForm_smul_right,
    coordinateFrame_twoForm_smul_left, coordinateFrame_twoForm_smul_right]
  ring

theorem isOneOne_comp_inclSnd {G : CoordinateRealTwoForm (n + m)} (hG : IsOneOne G) :
    IsOneOne (G.compContinuousLinearMap (inclSnd n m)) :=
  ProductTestForms.isOneOne_compContinuousLinearMap hG _ fun v => inclSnd_smul Complex.I v

/-- The pullback of the slots along the scaling `S_t`. -/
def scaledFamily (P : Fin n → CoordinateRealTwoForm n) (G : Fin m → CoordinateRealTwoForm (n + m))
    (t : ℝ) : Fin (n + m) → CoordinateRealTwoForm (n + m) :=
  Fin.append (fun i => (P i).compContinuousLinearMap (projFst n m))
    (fun j => (G j).compContinuousLinearMap (scaleFst n m t))

theorem continuous_scaledFamily (P : Fin n → CoordinateRealTwoForm n)
    (G : Fin m → CoordinateRealTwoForm (n + m)) :
    Continuous fun t => actualMixedTopDensity (scaledFamily P G t) := by
  refine continuous_actualMixedTopDensity.comp (continuous_pi fun i => ?_)
  refine Fin.addCases (fun i => ?_) (fun j => ?_) i
  · simp only [scaledFamily, Fin.append_left]
    exact continuous_const
  · simp only [scaledFamily, Fin.append_right, scaleFst_eq, compContinuousLinearMap_smul_add]
    fun_prop

/-- The scaling multiplies the left side by `t^{2n}` and the first-factor slots by `t²`, so the
density of the scaled family does not depend on `t ≠ 0`. -/
theorem actualMixedTopDensity_scaledFamily (P : Fin n → CoordinateRealTwoForm n)
    (G : Fin m → CoordinateRealTwoForm (n + m)) {t : ℝ} (ht : t ≠ 0) :
    actualMixedTopDensity (scaledFamily P G t) =
      actualMixedTopDensity (Fin.append (fun i => (P i).compContinuousLinearMap (projFst n m)) G) := by
  set F := Fin.append (fun i => (P i).compContinuousLinearMap (projFst n m)) G with hF
  have h1 := actualMixedTopDensity_compContinuousLinearMap F (scaleFst n m t)
  rw [det_scaleFst] at h1
  set c : Fin (n + m) → ℝ := Fin.append (fun _ : Fin n => t ^ 2) (fun _ : Fin m => 1) with hc
  have hfam : (fun i => (F i).compContinuousLinearMap (scaleFst n m t)) =
      fun i => c i • scaledFamily P G t i := by
    funext i
    refine Fin.addCases (fun i => ?_) (fun j => ?_) i
    · simp only [hF, hc, scaledFamily, Fin.append_left, comp_projFst_comp_scaleFst]
    · simp only [hF, hc, scaledFamily, Fin.append_right, one_smul]
  have h2 := actualMixedTopDensityMultilinear.map_smul_univ c (scaledFamily P G t)
  simp only [actualMixedTopDensityMultilinear_apply] at h2
  have hprod : ∏ i, c i = t ^ (2 * n) := by
    rw [hc, Fin.prod_univ_add]
    simp only [Fin.append_left, Fin.append_right, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin, one_pow, mul_one]
    ring
  rw [hfam, h2, hprod] at h1
  exact mul_left_cancel₀ (pow_ne_zero _ ht) h1

/-- **Vertical factorization**: for `n` two-forms `P` on `ℂⁿ` and `m` real `(1,1)`-forms `G` on
`ℂⁿ⁺ᵐ`, `D(p₁^*P, G) = D(P) · D(ι₂^*G)`. -/
theorem actualMixedTopDensity_append_comp_inclSnd (P : Fin n → CoordinateRealTwoForm n)
    (G : Fin m → CoordinateRealTwoForm (n + m)) (hP : ∀ i, IsOneOne (P i))
    (hG : ∀ j, IsOneOne (G j)) :
    actualMixedTopDensity (Fin.append (fun i => (P i).compContinuousLinearMap (projFst n m)) G) =
      actualMixedTopDensity P *
        actualMixedTopDensity (fun j => (G j).compContinuousLinearMap (inclSnd n m)) := by
  have hlim₀ : Tendsto (fun t => actualMixedTopDensity (scaledFamily P G t)) (𝓝[≠] 0)
      (𝓝 (actualMixedTopDensity (scaledFamily P G 0))) :=
    (continuous_scaledFamily P G).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hlim₁ : Tendsto (fun t => actualMixedTopDensity (scaledFamily P G t)) (𝓝[≠] 0)
      (𝓝 (actualMixedTopDensity
        (Fin.append (fun i => (P i).compContinuousLinearMap (projFst n m)) G))) :=
    tendsto_const_nhds.congr' (eventually_nhdsWithin_of_forall fun t ht =>
      (actualMixedTopDensity_scaledFamily P G ht).symm)
  rw [← tendsto_nhds_unique hlim₀ hlim₁, scaledFamily]
  simp only [scaleFst_zero, ← compContinuousLinearMap_comp]
  exact actualMixedTopDensity_append_comp P (fun j => (G j).compContinuousLinearMap (inclSnd n m))
    hP fun j => isOneOne_comp_inclSnd (hG j)

/-- **The pointwise identity for coordinate top forms**: for a top-degree form `Λ` on `ℂⁿ` in the
span of products of `(1,1)`-forms, `p₁^*Λ ∧ G₀ ∧ ⋯ ∧ G_{m-1}` has density `D(Λ) · D(ι₂^*G)`. -/
theorem topDensity_coordChain_comp_projFst {Λ : RealForm n (2 * n)} (hΛ : Λ ∈ wedgeProdSpan n n)
    (G : Fin m → CoordinateRealTwoForm (n + m)) (hG : ∀ j, IsOneOne (G j)) :
    topDensity (coordChain m G n (Λ.compContinuousLinearMap (projFst n m))) =
      topDensity Λ * actualMixedTopDensity (fun j => (G j).compContinuousLinearMap (inclSnd n m)) := by
  induction hΛ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨α, hα, rfl⟩ := hx
    rw [wedgeProd_compContinuousLinearMap, coordChain_wedgeProd, topDensity_wedgeProd,
      topDensity_wedgeProd]
    exact actualMixedTopDensity_append_comp_inclSnd α G hα hG
  | zero =>
    have h0 : (0 : RealForm n (2 * n)).compContinuousLinearMap (projFst n m) = 0 := by ext v; rfl
    rw [h0, map_zero, topDensity_zero, topDensity_zero, zero_mul]
  | add x y _ _ hx hy =>
    have hadd : (x + y).compContinuousLinearMap (projFst n m) =
        x.compContinuousLinearMap (projFst n m) + y.compContinuousLinearMap (projFst n m) := by
      ext v; rfl
    rw [hadd, map_add, topDensity_add, hx, hy, topDensity_add]
    ring
  | smul c x _ hx =>
    have hsmul : (c • x).compContinuousLinearMap (projFst n m) =
        c • x.compContinuousLinearMap (projFst n m) := by ext v; rfl
    rw [hsmul, map_smul, topDensity_smul, hx, topDensity_smul]
    ring

end

/-! ### Fibre integration on `X × Y` -/

section Global

open ProductTestForms PositiveProductCurrents IntegrationCurrent SmoothCurrentTraceMeasure
  TopDegreeDensity FirstPass.PositiveClasses CurrentTraceMeasure
open scoped ProductComplexManifold Manifold ContDiff

variable {n m : ℕ} {X : Type*} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] {Y : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel m) Y]
  [IsComplexManifold m Y]

/-- The vertical form `p₁^*ω_Xⁿ ∧ G₀ ∧ ⋯ ∧ G_{m-1}` on `X × Y`. -/
noncomputable def vertForm (wX : KahlerBackground n X)
    (G : Fin m → ClosedRealOneOneForm (n + m) (X × Y)) : testSpace (n + m) (X × Y) (n + m) :=
  chainTestLM m (fun j => (G j).val) (fun j => (G j).2.2) n
    (pullbackTestLM contMDiff_fst n (kahlerTest wX n))

/-- **The vertical density** of `G₀ ∧ ⋯ ∧ G_{m-1}` along the fibres of `p₁`: the ratio of
`p₁^*ω_Xⁿ ∧ G₀ ∧ ⋯ ∧ G_{m-1}` to the volume form of `X × Y`.  It is continuous
(`continuous_vertRatio`). -/
noncomputable def vertRatio (wX : KahlerBackground n X) (wY : KahlerBackground m Y)
    (G : Fin m → ClosedRealOneOneForm (n + m) (X × Y)) (p : X × Y) : ℝ :=
  topRatio (prodKahlerBackground wX wY).form.val
    ((vertForm wX G : testSpace (n + m) (X × Y) (n + m)) :
      SmoothRealForm (n + m) (X × Y) (2 * (n + m))) p

theorem continuous_vertRatio (wX : KahlerBackground n X) (wY : KahlerBackground m Y)
    (G : Fin m → ClosedRealOneOneForm (n + m) (X × Y)) : Continuous (vertRatio wX wY G) :=
  continuous_topRatio (prodKahlerBackground wX wY).isKahler.1 _

/-- The coefficient of `g · p₁^*Λ ∧ G₀ ∧ ⋯ ∧ G_{m-1}` in a product chart. -/
theorem coeff_chain_pullback (G : Fin m → ClosedRealOneOneForm (n + m) (X × Y))
    (Λ : testSpace n X n) (g : X × Y → ℝ) (hg : ChartSmooth (n := n + m) g)
    (e : ComplexChart n X) (e' : ComplexChart m Y) {z : ComplexModel n} {z' : ComplexModel m}
    (hz : z ∈ e.val.target) (hz' : z' ∈ e'.val.target) :
    ((chainTestLM m (fun j => (G j).val) (fun j => (G j).2.2) n
        (smulTest g hg (pullbackTestLM contMDiff_fst n Λ)) : testSpace (n + m) (X × Y) (n + m)) :
          SmoothRealForm (n + m) (X × Y) (2 * (n + m))).coeff (prodComplexChart e e')
        (prodModelEquiv n m (z, z')) =
      g ((prodComplexChart e e').val.symm (prodModelEquiv n m (z, z'))) •
        coordChain m (fun j => (G j).val.coeff (prodComplexChart e e') (prodModelEquiv n m (z, z')))
          n (((Λ : SmoothRealForm n X (2 * n)).coeff e z).compContinuousLinearMap (projFst n m)) := by
  rw [chainTestLM_coeff_eq, ← map_smul]
  congr 1
  change (smulFun g hg (SmoothRealForm.pullback contMDiff_fst
    (Λ : SmoothRealForm n X (2 * n)))).coeff _ _ = _
  rw [smulFun_coeff, pullback_fst_coeff _ e e' hz hz']

/-- **Fibrewise factorization of the ratio**: at `(x, y)`, the ratio of `g · p₁^*Λ ∧ G` is
`g(x, y)` times the ratio of `Λ` at `x` times the vertical density. -/
theorem topRatio_chain_pullback (wX : KahlerBackground n X) (wY : KahlerBackground m Y)
    (G : Fin m → ClosedRealOneOneForm (n + m) (X × Y)) (Λ : testSpace n X n) (g : X × Y → ℝ)
    (hg : ChartSmooth (n := n + m) g) (x : X) (y : Y) :
    topRatio (prodKahlerBackground wX wY).form.val
        ((chainTestLM m (fun j => (G j).val) (fun j => (G j).2.2) n
          (smulTest g hg (pullbackTestLM contMDiff_fst n Λ)) : testSpace (n + m) (X × Y) (n + m)) :
            SmoothRealForm (n + m) (X × Y) (2 * (n + m))) (x, y) =
      g (x, y) * topRatio wX.form.val (Λ : SmoothRealForm n X (2 * n)) x *
        vertRatio wX wY G (x, y) := by
  set e := complexChartAt (n := n) x
  set e' := complexChartAt (n := m) y
  have hz : e.val x ∈ e.val.target := e.val.map_source (mem_complexChartAt_source x)
  have hz' : e'.val y ∈ e'.val.target := e'.val.map_source (mem_complexChartAt_source y)
  have hE : complexChartAt (n := n + m) (x, y) = prodComplexChart e e' := rfl
  have hEx : (prodComplexChart e e').val (x, y) = prodModelEquiv n m (e.val x, e'.val y) := rfl
  have hsrc : (x, y) ∈ (prodComplexChart e e').val.source :=
    hE ▸ mem_complexChartAt_source (x, y)
  have hg' : g ((prodComplexChart e e').val.symm (prodModelEquiv n m (e.val x, e'.val y))) =
      g (x, y) := by
    rw [← hEx, (prodComplexChart e e').val.left_inv hsrc]
  have hpt := mem_prodComplexChart_target (e := e) (e' := e') hz hz'
  have hGone : ∀ j, IsOneOne ((G j).val.coeff (prodComplexChart e e')
      (prodModelEquiv n m (e.val x, e'.val y))) := fun j => (G j).2.2 _ _ hpt
  have hvert : vertRatio wX wY G (x, y) =
      topDensity ((formPow wX.form.val n).coeff e (e.val x)) *
        actualMixedTopDensity (fun j => ((G j).val.coeff (prodComplexChart e e')
          (prodModelEquiv n m (e.val x, e'.val y))).compContinuousLinearMap (inclSnd n m)) /
        topDensity ((formPow (prodKahlerBackground wX wY).form.val (n + m)).coeff
          (prodComplexChart e e') (prodModelEquiv n m (e.val x, e'.val y))) := by
    simp only [vertRatio, vertForm, topRatio, chartRatio]
    rw [hE, hEx, chainTestLM_coeff_eq]
    change topDensity (coordChain m _ n ((SmoothRealForm.pullback contMDiff_fst
      (formPow wX.form.val n)).coeff _ _)) / _ = _
    rw [pullback_fst_coeff _ e e' hz hz',
      topDensity_coordChain_comp_projFst (coeff_mem_wedgeProdSpan n
        (formPow_mem_testSpace (fun e z hz => (wX.isKahler.1 e z hz).1) n) e _ hz) _ hGone]
  have hpos : 0 < topDensity ((formPow wX.form.val n).coeff e (e.val x)) :=
    topDensity_formPow_pos wX.isKahler.1 hz
  have hΛ : topRatio wX.form.val (Λ : SmoothRealForm n X (2 * n)) x =
      topDensity ((Λ : SmoothRealForm n X (2 * n)).coeff e (e.val x)) /
        topDensity ((formPow wX.form.val n).coeff e (e.val x)) := rfl
  rw [hvert, hΛ]
  simp only [topRatio, chartRatio]
  rw [hE, hEx, coeff_chain_pullback G Λ g hg e e' hz hz', hg', topDensity_smul,
    topDensity_coordChain_comp_projFst (coeff_mem_wedgeProdSpan n Λ.2 e _ hz) _ hGone]
  field_simp

/-! ### Fubini: the fibre potential -/

section Fubini

open MeasureTheory

variable [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [MeasurableSpace Y] [BorelSpace Y]
  [CompactSpace Y]

/-- **The fibre potential** `v(x) = C(n+m, n) ∫_Y g(x, y) · vert(x, y) dV_Y(y)`. -/
noncomputable def fibrePotential (wX : KahlerBackground n X) (wY : KahlerBackground m Y)
    (G : Fin m → ClosedRealOneOneForm (n + m) (X × Y)) (g : X × Y → ℝ) (x : X) : ℝ :=
  ((n + m).choose n : ℝ) * ∫ y, g (x, y) * vertRatio wX wY G (x, y) ∂(kahlerVolume wY)

/-- The fibre potential of a continuous function is continuous. -/
theorem continuous_fibrePotential (wX : KahlerBackground n X) (wY : KahlerBackground m Y)
    (G : Fin m → ClosedRealOneOneForm (n + m) (X × Y)) {g : X × Y → ℝ} (hg : Continuous g) :
    Continuous (fibrePotential wX wY G g) := by
  have h := continuous_parametric_integral_of_continuous (μ := kahlerVolume wY)
    (f := fun x y => g (x, y) * vertRatio wX wY G (x, y))
    (hg.mul (continuous_vertRatio wX wY G)) isCompact_univ
  simp only [Measure.restrict_univ] at h
  exact continuous_const.mul h

/-- **Fubini along the fibres of `p₁`**: `∫_{X × Y} g · p₁^*Λ ∧ G₀ ∧ ⋯ ∧ G_{m-1} = ∫_X v · Λ` with
`v` the fibre potential. -/
theorem integrationCurrent_chain_pullback (wX : KahlerBackground n X) (wY : KahlerBackground m Y)
    (G : Fin m → ClosedRealOneOneForm (n + m) (X × Y)) (Λ : testSpace n X n) (g : X × Y → ℝ)
    (hg : ChartSmooth (n := n + m) g) :
    integrationCurrent (prodKahlerBackground wX wY)
        (chainTestLM m (fun j => (G j).val) (fun j => (G j).2.2) n
          (smulTest g hg (pullbackTestLM contMDiff_fst n Λ))) =
      ∫ x, fibrePotential wX wY G g x * topRatio wX.form.val (Λ : SmoothRealForm n X (2 * n)) x
        ∂(kahlerVolume wX) := by
  set F := topRatio (prodKahlerBackground wX wY).form.val
    ((chainTestLM m (fun j => (G j).val) (fun j => (G j).2.2) n
      (smulTest g hg (pullbackTestLM contMDiff_fst n Λ)) : testSpace (n + m) (X × Y) (n + m)) :
        SmoothRealForm (n + m) (X × Y) (2 * (n + m))) with hF
  have hFc : Continuous F := continuous_topRatio (prodKahlerBackground wX wY).isKahler.1 _
  have hint : Integrable F ((kahlerVolume wX).prod (kahlerVolume wY)) :=
    integrableOn_univ.mp (hFc.continuousOn.integrableOn_compact isCompact_univ)
  rw [integrationCurrent_apply, ← hF, kahlerVolume_prodKahlerBackground, integral_smul_measure,
    integral_prod _ hint]
  simp only [hF, topRatio_chain_pullback, ENNReal.toReal_natCast, smul_eq_mul]
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [fibrePotential]
  rw [mul_assoc, mul_comm _ (topRatio _ _ x), ← integral_const_mul, ← integral_const_mul,
    ← integral_const_mul]
  congr 1
  funext y
  ring

end Fubini

end Global

end SGPT.Foundations.Analysis.Pending.VerticalDensityFactorization
