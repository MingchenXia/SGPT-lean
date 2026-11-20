import SGPT.PSH.SiuL2Gluing
import SGPT.PSH.GlobalL2CoverSystem
import SGPT.NAPotential.NAGagaDisc

/-!
# The product `X × Δ`: charts, the measure `μ ⊗ dλ`, and sections of `p₁^*E`

Blueprint `claude-siu-l2.tex`, nodes `claude-siu-l2:product`, `claude-siu-l2:product-measure`
.

`X × Δ` is the product complex manifold of `SGPT.Foundations.Analysis.Pending.ProductComplexManifold`
(`Δ = NAGaga.unitDisc`), modelled on `ℂⁿ⁺¹` through `prodL n = prodModelEquiv n 1`.  For a chart
`c` of `X` at `x₀` the product chart at `(x₀, δ₀)` is `(x, t) ↦ prodL (c x, t)`; its target is
`prodL (c.target × Δ)`.

* `discMeasure`: Lebesgue measure on `Δ` (a finite measure); `prodMeasure μ = μ ⊗ dλ`.
* `map_prodChart`: if `μ = ρ(z) dz` in the chart `c`, then `μ ⊗ dλ = ρ(z) dz dt` in the product
  chart.
* `IsHolomorphicProdSectionOn E F U`: `F`, a section of `p₁^*E` (a function
  `(q : X × Δ) → E.Fiber q.1`), is holomorphic on `U`: its coefficient in every atlas frame of `E`
  is holomorphic (for the product manifold structure).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace SGPT.PSH.SiuL2

open Set Filter Metric MeasureTheory Bundle
open scoped Topology ENNReal ContDiff Manifold
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.ChartwiseGlobalL1
open SGPT.Foundations.Analysis.Pending.ProductComplexManifold
open scoped ProductComplexManifold
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.PolynomialH0Growth
  SGPT.Bergman.CompactHolomorphicSectionsDraft
open HermitianHolomorphicLineBundle
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.PSH.GlobalL2 SGPT.NAPotential.NAGaga

/-! ### Lebesgue measure on the disc -/

/-- Lebesgue measure on the unit disc `Δ`. -/
def discMeasure : Measure unitDisc := Measure.comap Subtype.val volume

theorem map_val_discMeasure :
    Measure.map Subtype.val discMeasure = volume.restrict (unitDisc : Set (ComplexModel 1)) :=
  map_comap_subtype_coe unitDisc.isOpen.measurableSet _

instance : IsFiniteMeasure discMeasure := by
  refine ⟨?_⟩
  have h := congrArg (fun ν : Measure (ComplexModel 1) => ν univ) map_val_discMeasure
  simp only [Measure.restrict_apply MeasurableSet.univ, univ_inter] at h
  rw [Measure.map_apply measurable_subtype_coe MeasurableSet.univ, preimage_univ] at h
  rw [h]
  exact measure_ball_lt_top

variable {n : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X]

/-! ### Product charts -/

/-- The product chart at `(x₀, δ₀)`. -/
abbrev pChart (q₀ : X × unitDisc) : ComplexChart (n + 1) (X × unitDisc) :=
  complexChartAt (n := n + 1) q₀

theorem pChart_apply (q₀ q : X × unitDisc) :
    (pChart (n := n) q₀).val q = prodL n ((complexChartAt (n := n) q₀.1).val q.1, q.2.val) := rfl

theorem pChart_source (q₀ : X × unitDisc) :
    (pChart (n := n) q₀).val.source = (complexChartAt (n := n) q₀.1).val.source ×ˢ univ := by
  change (chartAt (ComplexModel (n + 1)) q₀).source = _
  rw [chartAt_prod, prodChart_source, discChart_source]
  rfl

theorem pChart_target (q₀ : X × unitDisc) :
    (pChart (n := n) q₀).val.target =
      (prodL n).symm ⁻¹' ((complexChartAt (n := n) q₀.1).val.target ×ˢ
        (unitDisc : Set (ComplexModel 1))) :=
  prodChartAt_target q₀

theorem pChart_symm_apply (q₀ : X × unitDisc) (z : ComplexModel n) {w : ComplexModel 1}
    (hw : w ∈ (unitDisc : Set (ComplexModel 1))) :
    (pChart (n := n) q₀).val.symm (prodL n (z, w)) =
      ((complexChartAt (n := n) q₀.1).val.symm z, ⟨w, hw⟩) :=
  prodChartAt_symm_apply q₀ z hw

theorem pChart_symm_fst (q₀ : X × unitDisc) {w : ComplexModel (n + 1)}
    (hw : w ∈ (pChart (n := n) q₀).val.target) :
    ((pChart (n := n) q₀).val.symm w).1 = (complexChartAt (n := n) q₀.1).val.symm ((prodL n).symm w).1 := by
  have hw' := hw
  rw [pChart_target] at hw'
  have h := pChart_symm_apply q₀ ((prodL n).symm w).1 hw'.2
  rw [show prodL n (((prodL n).symm w).1, ((prodL n).symm w).2) = w from
    (prodL n).apply_symm_apply w] at h
  rw [h]

theorem pChart_symm_snd (q₀ : X × unitDisc) {w : ComplexModel (n + 1)}
    (hw : w ∈ (pChart (n := n) q₀).val.target) :
    ((pChart (n := n) q₀).val.symm w).2.val = ((prodL n).symm w).2 := by
  have hw' := hw
  rw [pChart_target] at hw'
  have h := pChart_symm_apply q₀ ((prodL n).symm w).1 hw'.2
  rw [show prodL n (((prodL n).symm w).1, ((prodL n).symm w).2) = w from
    (prodL n).apply_symm_apply w] at h
  rw [h]

theorem norm_prodL_sq (z : ComplexModel n) (w : ComplexModel 1) :
    ‖prodL n (z, w)‖ ^ 2 = ‖z‖ ^ 2 + ‖w‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq,
    Fin.sum_univ_add]
  simp [prodL, prodModelEquiv]

/-! ### The measure `μ ⊗ dλ` -/

variable [MeasurableSpace X] [BorelSpace X]

/-- The measure `μ ⊗ dλ` on `X × Δ`. -/
def prodMeasure (μ : Measure X) : Measure (X × unitDisc) := μ.prod discMeasure

/-- Pushing a density forward along the measure-preserving `prodL`. -/
theorem map_prodL_withDensity (S : Set (ComplexModel n × ComplexModel 1)) (hS : MeasurableSet S)
    (f : ComplexModel n × ComplexModel 1 → ℝ≥0∞) :
    Measure.map (prodL n) (((volume : Measure (ComplexModel n)).prod
        (volume : Measure (ComplexModel 1))).restrict S |>.withDensity f) =
      (volume.restrict ((prodL n).symm ⁻¹' S)).withDensity (fun w => f ((prodL n).symm w)) := by
  set e : (ComplexModel n × ComplexModel 1) ≃ᵐ ComplexModel (n + 1) :=
    (prodL n).toHomeomorph.toMeasurableEquiv with he
  have hmp : MeasurePreserving e (volume.prod volume) volume :=
    ProductMixedMeasure.measurePreserving_prodModelEquiv n 1
  have hS' : MeasurableSet ((prodL n).symm ⁻¹' S) :=
    (prodL n).symm.continuous.measurable hS
  ext A hA
  have hpre : (prodL n) ⁻¹' ((prodL n).symm ⁻¹' S) = S := by
    ext p; simp
  rw [Measure.map_apply (prodL n).continuous.measurable hA,
    withDensity_apply _ ((prodL n).continuous.measurable hA), withDensity_apply _ hA,
    Measure.restrict_restrict ((prodL n).continuous.measurable hA),
    Measure.restrict_restrict hA]
  have h := hmp.setLIntegral_comp_preimage_emb e.measurableEmbedding
    (fun w => f ((prodL n).symm w)) (A ∩ (prodL n).symm ⁻¹' S)
  have hpre2 : e ⁻¹' (A ∩ (prodL n).symm ⁻¹' S) = (prodL n) ⁻¹' A ∩ S := by
    rw [preimage_inter]
    congr 1
  rw [hpre2] at h
  rw [← h]
  refine setLIntegral_congr_fun (((prodL n).continuous.measurable hA).inter hS) fun p _ => ?_
  simp [he]

/-- **The product measure in a product chart** (`claude-siu-l2:product-measure`).  If `μ = ρ(z) dz`
in the chart of `X` at `q₀.1`, then `μ ⊗ dλ = ρ(z) dz dt` in the product chart at `q₀`. -/
theorem map_pChart {μ : Measure X} [SFinite μ] (q₀ : X × unitDisc) {ρ : ComplexModel n → ℝ}
    (hρc : ContinuousOn ρ (complexChartAt (n := n) q₀.1).val.target)
    (hmap : Measure.map (complexChartAt (n := n) q₀.1).val
        (μ.restrict (complexChartAt (n := n) q₀.1).val.source) =
      (volume.restrict (complexChartAt (n := n) q₀.1).val.target).withDensity
        (fun z => ENNReal.ofReal (ρ z))) :
    Measure.map (pChart (n := n) q₀).val ((prodMeasure μ).restrict (pChart (n := n) q₀).val.source) =
      (volume.restrict (pChart (n := n) q₀).val.target).withDensity
        (fun w => ENNReal.ofReal (ρ ((prodL n).symm w).1)) := by
  classical
  set c := (complexChartAt (n := n) q₀.1).val with hc
  set S := c.source with hSdef
  have hSm : MeasurableSet S := c.open_source.measurableSet
  have hsrc : (prodMeasure μ).restrict (pChart (n := n) q₀).val.source =
      (μ.restrict S).prod discMeasure := by
    rw [pChart_source, prodMeasure, ← Measure.prod_restrict, Measure.restrict_univ]
  set c' : X → ComplexModel n := S.piecewise c (fun _ => 0) with hc'
  have hc'm : Measurable c' :=
    ContinuousOn.measurable_piecewise c.continuousOn continuousOn_const hSm
  have hae1 : ∀ᵐ q ∂((μ.restrict S).prod discMeasure), q.1 ∈ S :=
    Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem hSm)
  have hcongr : (pChart (n := n) q₀).val =ᵐ[(μ.restrict S).prod discMeasure]
      (prodL n ∘ Prod.map c' Subtype.val) := by
    filter_upwards [hae1] with q hq
    rw [pChart_apply]
    change prodL n (c q.1, q.2.val) = prodL n (c' q.1, q.2.val)
    rw [hc', Set.piecewise_eq_of_mem _ _ _ hq]
  have hcc' : c' =ᵐ[μ.restrict S] c := by
    filter_upwards [ae_restrict_mem hSm] with x hx
    exact Set.piecewise_eq_of_mem _ _ _ hx
  have hmapX : Measure.map c' (μ.restrict S) =
      (volume.restrict c.target).withDensity (fun z => ENNReal.ofReal (ρ z)) := by
    rw [Measure.map_congr hcc']
    exact hmap
  have hρm : AEMeasurable (fun z => ENNReal.ofReal (ρ z)) (volume.restrict c.target) :=
    (ENNReal.continuous_ofReal.comp_continuousOn hρc).aemeasurable c.open_target.measurableSet
  have hTm : MeasurableSet (c.target ×ˢ (unitDisc : Set (ComplexModel 1))) :=
    c.open_target.measurableSet.prod unitDisc.isOpen.measurableSet
  rw [hsrc, Measure.map_congr hcongr, ← Measure.map_map (prodL n).continuous.measurable
    (hc'm.prodMap measurable_subtype_coe), ← Measure.map_prod_map _ _ hc'm measurable_subtype_coe,
    hmapX, map_val_discMeasure, prod_withDensity_left₀ hρm, Measure.prod_restrict,
    map_prodL_withDensity _ hTm, pChart_target]

/-! ### The projections of `ℂⁿ⁺¹ = ℂⁿ × ℂ` -/

/-- The `ℂⁿ`-component `w ↦ (prodL⁻¹ w).1`. -/
def projX (n : ℕ) : ComplexModel (n + 1) →L[ℂ] ComplexModel n :=
  (ContinuousLinearMap.fst ℂ (ComplexModel n) (ComplexModel 1)).comp
    (prodL n).symm.toContinuousLinearMap

/-- The `ℂ`-component `w ↦ (prodL⁻¹ w).2`. -/
def projT (n : ℕ) : ComplexModel (n + 1) →L[ℂ] ComplexModel 1 :=
  (ContinuousLinearMap.snd ℂ (ComplexModel n) (ComplexModel 1)).comp
    (prodL n).symm.toContinuousLinearMap

theorem projX_apply (w : ComplexModel (n + 1)) : projX n w = ((prodL n).symm w).1 := rfl

theorem projT_apply (w : ComplexModel (n + 1)) : projT n w = ((prodL n).symm w).2 := rfl

theorem prodL_proj (w : ComplexModel (n + 1)) : prodL n (projX n w, projT n w) = w :=
  (prodL n).apply_symm_apply w

theorem projX_prodL (z : ComplexModel n) (t : ComplexModel 1) : projX n (prodL n (z, t)) = z := by
  simp [projX_apply]

theorem projT_prodL (z : ComplexModel n) (t : ComplexModel 1) : projT n (prodL n (z, t)) = t := by
  simp [projT_apply]

theorem norm_sub_sq_prodL (w w' : ComplexModel (n + 1)) :
    ‖w - w'‖ ^ 2 = ‖projX n w - projX n w'‖ ^ 2 + ‖projT n w - projT n w'‖ ^ 2 := by
  rw [← prodL_proj (w - w'), norm_prodL_sq, map_sub, map_sub]

theorem dbarDir_comp_projX {g : ComplexModel n → ℂ} {w : ComplexModel (n + 1)}
    (hg : DifferentiableAt ℝ g (projX n w)) (v : ComplexModel (n + 1)) :
    CauchyGreen.dbarDir v (fun y => g (projX n y)) w =
      CauchyGreen.dbarDir (projX n v) g (projX n w) := by
  unfold CauchyGreen.dbarDir
  have hL : fderiv ℝ (⇑(projX n)) w = (projX n).restrictScalars ℝ :=
    ((projX n).restrictScalars ℝ).fderiv
  have h : fderiv ℝ (fun y => g (projX n y)) w =
      (fderiv ℝ g (projX n w)).comp ((projX n).restrictScalars ℝ) := by
    have := fderiv_comp (𝕜 := ℝ) w hg ((projX n).restrictScalars ℝ).differentiableAt
    rw [hL] at this
    exact this
  rw [h]
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply,
    ContinuousLinearMap.coe_restrictScalars', map_smul]

theorem projX_coordVec_castAdd (i : Fin n) :
    projX n (Hormander.coordVec (Fin.castAdd 1 i)) = Hormander.coordVec i := by
  have h := ProductMixedMeasure.prodModelEquiv_symm_coordinateVector_castAdd (n := n) (m := 1) i
  rw [projX_apply]
  exact congrArg Prod.fst h

theorem projX_coordVec_natAdd (j : Fin 1) :
    projX n (Hormander.coordVec (Fin.natAdd n j)) = 0 := by
  have h := ProductMixedMeasure.prodModelEquiv_symm_coordinateVector_natAdd (n := n) (m := 1) j
  rw [projX_apply]
  exact congrArg Prod.fst h

/-- `|∂̄(g ∘ π_X)|² = |∂̄g|² ∘ π_X`. -/
theorem dbarNormSq_comp_projX {g : ComplexModel n → ℂ} {w : ComplexModel (n + 1)}
    (hg : DifferentiableAt ℝ g (projX n w)) :
    dbarNormSq (fun y => g (projX n y)) w = dbarNormSq g (projX n w) := by
  unfold dbarNormSq
  rw [Fin.sum_univ_add]
  simp only [dbarDir_comp_projX hg, projX_coordVec_castAdd, projX_coordVec_natAdd]
  simp [CauchyGreen.dbarDir]

/-! ### Sections of `p₁^*E` -/

/-- `F`, a section of `p₁^*E` over `X × Δ` (a function `(q : X × Δ) → E.Fiber q.1`), is
holomorphic on `U`: its coefficient in every atlas frame of `E` is holomorphic near every point of
`U` over the base set of the frame. -/
def IsHolomorphicProdSectionOn (E : HermitianHolomorphicLineBundle.{0, 0} n X)
    (F : (q : X × unitDisc) → E.Fiber q.1) (U : Set (X × unitDisc)) : Prop :=
  ∀ q ∈ U, ∀ e : AtlasFrame E, q.1 ∈ e.val.baseSet →
    HolomorphicAt (n + 1) (fun q' : X × unitDisc => e.val.continuousLinearMapAt ℂ q'.1 (F q')) q

end SGPT.PSH.SiuL2
