import SGPT.Foundations.Analysis.Pending.ProductMixedMeasure
import SGPT.Foundations.Analysis.Pending.ChartWeightedL2Transfer
import SGPT.PSH.SourceTestCurveLegendrePSH

/-!
# The unit disc `Δ` and the product `X × Δ`

Source: `chapter_NApotential.tex`, `prop:psiandPhi` and `def:subgeoray`: the complexification `Ψ`
of a test curve lives on `X × Δ`, `Δ` the unit disc. Blueprint `claude-na-gaga.tex`, node
`claude-na-gaga:disc`.

`Δ` is the open unit ball of `ℂ¹ = ComplexModel 1` (`unitDisc`), with its open-subset manifold
structure; `X × Δ` is the product complex manifold of `SGPT.Foundations.Analysis.Pending.
ProductComplexManifold` (`open scoped ProductComplexManifold`), modelled on `ℂⁿ⁺¹` through
`L = prodModelEquiv n 1 : ℂⁿ × ℂ¹ ≃ ℂⁿ⁺¹`. This file records the chart computations, the
holomorphy of `(y, δ) ↦ g(y) δ^i`, the product neighbourhoods of `(x, 0)`, the transfer of set
integrals through `L` (which preserves Lebesgue measure) and the volume of an annulus in `Δ`.
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.NAPotential.NAGaga

open Set Filter MeasureTheory TopologicalSpace Metric
open scoped Topology Manifold ContDiff ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open ProductComplexManifold
open scoped ProductComplexManifold

/-! ### The disc -/

/-- The unit disc `Δ ⊆ ℂ`, the open unit ball of `ℂ¹`. -/
def unitDisc : Opens (ComplexModel 1) := ⟨ball 0 1, isOpen_ball⟩

theorem mem_unitDisc {w : ComplexModel 1} : w ∈ unitDisc ↔ ‖w‖ < 1 := by
  change w ∈ ball (0 : ComplexModel 1) 1 ↔ _
  rw [mem_ball_zero_iff]

/-- The origin `0 ∈ Δ`. -/
def discOrigin : unitDisc := ⟨0, mem_unitDisc.mpr (by simp)⟩

/-- The complex coordinate `δ` of `Δ`. -/
def discCoord (δ : unitDisc) : ℂ := δ.val 0

/-- On `ℂ¹` the norm is the modulus of the coordinate. -/
theorem norm_apply_zero (w : ComplexModel 1) : ‖w 0‖ = ‖w‖ := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_one, Real.sqrt_sq (norm_nonneg _)]

theorem norm_discCoord (δ : unitDisc) : ‖discCoord δ‖ = ‖δ.val‖ := norm_apply_zero _

theorem discChart_apply (δ δ' : unitDisc) : chartAt (ComplexModel 1) δ δ' = δ'.val := rfl

theorem discChart_target (δ : unitDisc) :
    (chartAt (ComplexModel 1) δ).target = (unitDisc : Set (ComplexModel 1)) := by
  rw [TopologicalSpace.Opens.chartAt_eq]
  simp [OpenPartialHomeomorph.subtypeRestr_def, chartAt_self_eq]

theorem discChart_source (δ : unitDisc) : (chartAt (ComplexModel 1) δ).source = univ := by
  simp [TopologicalSpace.Opens.chartAt_eq, OpenPartialHomeomorph.subtypeRestr_source,
    chartAt_self_eq]

theorem discChart_symm_val (δ : unitDisc) {w : ComplexModel 1}
    (hw : w ∈ (unitDisc : Set (ComplexModel 1))) :
    ((chartAt (ComplexModel 1) δ).symm w).val = w := by
  have h := (chartAt (ComplexModel 1) δ).right_inv (by rw [discChart_target]; exact hw)
  rwa [discChart_apply] at h

/-- The coordinate `δ` is holomorphic on `Δ`. -/
theorem contMDiff_discCoord :
    ContMDiff 𝓘(ℂ, ComplexModel 1) 𝓘(ℂ, ℂ) ∞ discCoord := by
  have h1 : ContMDiff 𝓘(ℂ, ComplexModel 1) 𝓘(ℂ, ComplexModel 1) ∞
      (Subtype.val : unitDisc → ComplexModel 1) := contMDiff_subtype_val
  have h2 : ContMDiff 𝓘(ℂ, ComplexModel 1) 𝓘(ℂ, ℂ) ∞
      (fun w : ComplexModel 1 => w 0) :=
    (EuclideanSpace.proj (0 : Fin 1) : ComplexModel 1 →L[ℂ] ℂ).contMDiff
  exact h2.comp h1

/-! ### Charts of `X × Δ` -/

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]

/-- The identification `ℂⁿ × ℂ¹ ≃ ℂⁿ⁺¹` of the product atlas. -/
abbrev prodL (n : ℕ) : (ComplexModel n × ComplexModel 1) ≃L[ℂ] ComplexModel (n + 1) :=
  prodModelEquiv n 1

theorem prodChartAt_apply (p q : M × unitDisc) :
    chartAt (ComplexModel (n + 1)) p q = prodL n (chartAt (ComplexModel n) p.1 q.1, q.2.val) :=
  rfl

theorem prodChartAt_symm_apply (p : M × unitDisc) (z : ComplexModel n) {w : ComplexModel 1}
    (hw : w ∈ (unitDisc : Set (ComplexModel 1))) :
    (chartAt (ComplexModel (n + 1)) p).symm (prodL n (z, w)) =
      ((chartAt (ComplexModel n) p.1).symm z, ⟨w, hw⟩) := by
  rw [chartAt_prod, prodChart_symm_apply]
  simp only [prodL, ContinuousLinearEquiv.symm_apply_apply]
  exact Prod.ext rfl (Subtype.ext (discChart_symm_val p.2 hw))

theorem prodChartAt_target (p : M × unitDisc) :
    (chartAt (ComplexModel (n + 1)) p).target =
      (prodL n).symm ⁻¹' ((chartAt (ComplexModel n) p.1).target ×ˢ (unitDisc : Set _)) := by
  rw [chartAt_prod, prodChart_target, discChart_target]

theorem complexChartAt_prod_val (p : M × unitDisc) :
    (complexChartAt (n := n + 1) p).val = chartAt (ComplexModel (n + 1)) p := rfl

theorem prodChartAt_origin (x : M) :
    chartAt (ComplexModel (n + 1)) (x, discOrigin) (x, discOrigin) =
      prodL n (chartAt (ComplexModel n) x x, 0) := rfl

/-- **Holomorphy of `(y, δ) ↦ g(y) δ^i`** near `(x, δ)` when `g` is holomorphic near `x`. -/
theorem holomorphicAt_mul_coord_pow [IsComplexManifold n M] {g : M → ℂ} {x : M}
    (hg : HolomorphicAt n g x) (δ : unitDisc) (i : ℕ) :
    HolomorphicAt (n + 1) (fun p : M × unitDisc => g p.1 * discCoord p.2 ^ i) (x, δ) := by
  have hev : ∀ᶠ p : M × unitDisc in 𝓝 (x, δ),
      MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) g p.1 :=
    continuous_fst.continuousAt.eventually hg
  filter_upwards [hev] with p hp
  have hfst : MDifferentiableAt 𝓘(ℂ, ComplexModel (n + 1)) 𝓘(ℂ, ComplexModel n)
      (Prod.fst : M × unitDisc → M) p :=
    (contMDiff_fst (n := n) (m := 1)).mdifferentiableAt (by simp)
  have hsnd : MDifferentiableAt 𝓘(ℂ, ComplexModel (n + 1)) 𝓘(ℂ, ComplexModel 1)
      (Prod.snd : M × unitDisc → unitDisc) p :=
    (contMDiff_snd (n := n) (m := 1)).mdifferentiableAt (by simp)
  have h1 : MDifferentiableAt 𝓘(ℂ, ComplexModel (n + 1)) 𝓘(ℂ, ℂ)
      (fun q : M × unitDisc => g q.1) p := hp.comp p hfst
  have h2 : MDifferentiableAt 𝓘(ℂ, ComplexModel (n + 1)) 𝓘(ℂ, ℂ)
      (fun q : M × unitDisc => discCoord q.2) p :=
    (contMDiff_discCoord.mdifferentiableAt (by simp)).comp p hsnd
  exact h1.mul (h2.pow i)

/-! ### Product neighbourhoods and integrals -/

/-- A neighbourhood of `L(z₀, 0)` contains `L(U₁ × B(0, r))` for an open `U₁ ∋ z₀` inside a given
open set and some `0 < r ≤ 1`. -/
theorem exists_prod_subset {U' : Set (ComplexModel (n + 1))} (hU' : IsOpen U')
    {z₀ : ComplexModel n} (h : prodL n (z₀, 0) ∈ U') {V : Set (ComplexModel n)} (hV : IsOpen V)
    (hz₀ : z₀ ∈ V) :
    ∃ U₁ : Set (ComplexModel n), IsOpen U₁ ∧ z₀ ∈ U₁ ∧ U₁ ⊆ V ∧ ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧
      ∀ z ∈ U₁, ∀ w ∈ ball (0 : ComplexModel 1) r, prodL n (z, w) ∈ U' := by
  have ho : IsOpen ((prodL n) ⁻¹' U') := hU'.preimage (prodL n).continuous
  obtain ⟨u, v, hu, hv, hzu, h0v, huv⟩ := isOpen_prod_iff.mp ho z₀ 0 h
  obtain ⟨r, hr, hrv⟩ := isOpen_iff.mp hv 0 h0v
  refine ⟨u ∩ V, hu.inter hV, ⟨hzu, hz₀⟩, inter_subset_right, min r 1, lt_min hr one_pos,
    min_le_right _ _, fun z hz w hw => ?_⟩
  have hw' : w ∈ v := hrv (ball_subset_ball (min_le_left _ _) hw)
  exact huv (mk_mem_prod hz.1 hw')

/-- Set integrals transfer through `L`, which preserves Lebesgue measure. -/
theorem setLIntegral_prodL (F : ComplexModel (n + 1) → ℝ≥0∞)
    (s : Set (ComplexModel n × ComplexModel 1)) :
    ∫⁻ z in (prodL n).symm ⁻¹' s, F z = ∫⁻ p in s, F (prodL n p) ∂(volume.prod volume) := by
  have h := (ProductMixedMeasure.measurePreserving_prodModelEquiv n 1).setLIntegral_comp_preimage_emb
    (prodL n).toHomeomorph.measurableEmbedding F ((prodL n).symm ⁻¹' s)
  have hpre : (prodModelEquiv n 1) ⁻¹' ((prodL n).symm ⁻¹' s) = s := by
    ext p; simp [prodL]
  rw [hpre] at h
  exact h.symm

/-- The image `L(s)` is the preimage `L⁻¹⁻¹(s)`. -/
theorem prodL_image (s : Set (ComplexModel n × ComplexModel 1)) :
    (prodL n) '' s = (prodL n).symm ⁻¹' s :=
  (prodL n).toEquiv.image_eq_preimage_symm s

/-- `L` transports a.e.-measurability from `L(s)` to `s`. -/
theorem aemeasurable_comp_prodL {F : ComplexModel (n + 1) → ℝ≥0∞}
    {s : Set (ComplexModel n × ComplexModel 1)}
    (hF : AEMeasurable F (volume.restrict ((prodL n).symm ⁻¹' s))) :
    AEMeasurable (fun p => F (prodL n p)) ((volume.prod volume).restrict s) := by
  have hmp := (ProductMixedMeasure.measurePreserving_prodModelEquiv n 1).restrict_preimage_emb
    (prodL n).toHomeomorph.measurableEmbedding ((prodL n).symm ⁻¹' s)
  have hpre : (prodModelEquiv n 1) ⁻¹' ((prodL n).symm ⁻¹' s) = s := by
    ext p; simp [prodL]
  rw [hpre] at hmp
  exact AEMeasurable.comp_quasiMeasurePreserving hF hmp.quasiMeasurePreserving

/-! ### Annuli -/

theorem finrank_complexModel_one : Module.finrank ℝ (ComplexModel 1) = 2 := by
  rw [finrank_real_of_complex, finrank_euclideanSpace, Fintype.card_fin]

/-- `vol({ρ/2 < |w| < ρ}) = (3/4) ρ² vol(B(0,1))` in `ℂ¹`. -/
theorem volume_annulus {ρ : ℝ} (hρ : 0 < ρ) :
    volume (ball (0 : ComplexModel 1) ρ \ closedBall 0 (ρ / 2)) =
      ENNReal.ofReal (3 / 4 * ρ ^ 2) * volume (ball (0 : ComplexModel 1) 1) := by
  have hsub : closedBall (0 : ComplexModel 1) (ρ / 2) ⊆ ball 0 ρ :=
    closedBall_subset_ball (by linarith)
  rw [measure_sdiff hsub measurableSet_closedBall.nullMeasurableSet
    (measure_closedBall_lt_top (x := (0 : ComplexModel 1)) (r := ρ / 2)).ne,
    Measure.addHaar_ball _ _ hρ.le, Measure.addHaar_closedBall _ _ (by linarith),
    finrank_complexModel_one, ← ENNReal.sub_mul (fun _ _ => (measure_ball_lt_top).ne),
    ← ENNReal.ofReal_sub _ (by positivity)]
  congr 2
  ring

theorem volume_unitBall_pos : 0 < volume (ball (0 : ComplexModel 1) 1) :=
  measure_ball_pos _ _ one_pos

theorem volume_unitBall_ne_top : volume (ball (0 : ComplexModel 1) 1) ≠ ⊤ :=
  measure_ball_lt_top.ne

end SGPT.NAPotential.NAGaga
