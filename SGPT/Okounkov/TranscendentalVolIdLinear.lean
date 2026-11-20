import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import SGPT.Foundations.Analysis.FirstPass.FormPullbackFunctorial

/-!
# Auxiliary linear algebra and form functoriality for the volume identity

Package VOL (blueprint `claude-tok-volid`, nodes `tok-volid:block-volume` and
`tok-volid:pullback-comp`), used in `tok:Bn-implies-Cn`:

* `volume_image_tail_vecMul`: if `G` is a real `(k+1) × (k+1)` matrix of determinant `1` acting on
  row vectors and preserving the first coordinate (`(x G)_0 = x_0`, i.e. its first column is
  `e_0`), then `y ↦ tail((c + (0, y)) G)` preserves Lebesgue measure on `ℝᵏ` (its linear part is
  the lower right block of `G`, of determinant `det G = 1`). This is how the correction matrix of
  a flag lifting acts on the slice `{x_0 = 0}` (`def:lifting`).
* `SmoothRealForm.pullback_comp_geometricallyEq'`: `(f ∘ g)^* a = g^* (f^* a)` geometrically, for
  holomorphic maps between manifolds of *different* dimensions (TN's
  `pullback_comp_geometricallyEq` treats equal dimensions; the proof is the same chain rule).
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.Okounkov.TranscendentalVolId

open Set Filter MeasureTheory Matrix
open scoped Topology Manifold ContDiff

/-! ### Block-triangular matrices and slices -/

/-- If the first column of `G` is `e_0`, the lower right block has the determinant of `G`. -/
theorem det_submatrix_succ_of_col_zero {k : ℕ} (G : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ)
    (h0 : G 0 0 = 1) (hs : ∀ i : Fin k, G i.succ 0 = 0) :
    (G.submatrix Fin.succ Fin.succ).det = G.det := by
  rw [Matrix.det_succ_column_zero G, Fin.sum_univ_succ]
  simp [h0, hs, Fin.succAbove_zero]

/-- The first column of a matrix preserving the first coordinate of row vectors is `e_0`. -/
theorem col_zero_of_vecMul_zero {k : ℕ} {G : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ}
    (h : ∀ x : Fin (k + 1) → ℝ, (x ᵥ* G) 0 = x 0) (i : Fin (k + 1)) :
    G i 0 = if i = 0 then 1 else 0 := by
  have hi := h (Pi.single i 1)
  have hl : (Pi.single i (1 : ℝ) ᵥ* G) 0 = G i 0 := by
    simp [Matrix.vecMul, dotProduct, Pi.single_apply]
  rw [hl] at hi
  rw [hi]
  by_cases h0 : i = 0
  · subst h0; simp
  · simp [h0, Ne.symm h0]

/-- The tail of `(c + (0, y)) G` is affine in `y` with linear part the lower right block. -/
theorem tail_vecMul_add_cons {k : ℕ} (G : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ)
    (c : Fin (k + 1) → ℝ) (y : Fin k → ℝ) :
    (fun j : Fin k => ((c + Fin.cons 0 y) ᵥ* G) j.succ) =
      y ᵥ* G.submatrix Fin.succ Fin.succ + fun j => (c ᵥ* G) j.succ := by
  funext j
  simp only [Matrix.add_vecMul, Pi.add_apply]
  rw [add_comm]
  congr 1
  simp [Matrix.vecMul, dotProduct, Fin.sum_univ_succ, Matrix.submatrix_apply]

/-- **Volume preservation on slices**: if `det G = 1` and `(x G)_0 = x_0` for all `x`, then
`y ↦ tail((c + (0, y)) G)` preserves Lebesgue measure. -/
theorem volume_image_tail_vecMul {k : ℕ} (G : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ)
    (hdet : G.det = 1) (h0 : ∀ x : Fin (k + 1) → ℝ, (x ᵥ* G) 0 = x 0) (c : Fin (k + 1) → ℝ)
    (S : Set (Fin k → ℝ)) :
    volume ((fun y : Fin k → ℝ => fun j : Fin k => ((c + Fin.cons 0 y) ᵥ* G) j.succ) '' S) =
      volume S := by
  set M' := G.submatrix Fin.succ Fin.succ with hM'
  have hcol := col_zero_of_vecMul_zero h0
  have hdet' : M'.det = 1 := by
    rw [hM', det_submatrix_succ_of_col_zero G (by simpa using hcol 0)
      (fun i => by simpa [Fin.succ_ne_zero] using hcol i.succ), hdet]
  set c' : Fin k → ℝ := fun j => (c ᵥ* G) j.succ
  have hfun : (fun y : Fin k → ℝ => fun j : Fin k => ((c + Fin.cons 0 y) ᵥ* G) j.succ) =
      (fun y => y + c') ∘ ⇑(Matrix.toLin' M'ᵀ) := by
    funext y
    rw [Function.comp_apply, Matrix.toLin'_apply, Matrix.mulVec_transpose]
    exact tail_vecMul_add_cons G c y
  rw [hfun, image_comp, image_add_right, measure_preimage_add_right,
    MeasureTheory.Measure.addHaar_image_linearMap, LinearMap.det_toLin', Matrix.det_transpose,
    hdet', abs_one, ENNReal.ofReal_one, one_mul]

/-! ### Functoriality of the pullback for maps between different dimensions -/

section Pullback

open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.FirstPass.HolomorphicMaps

variable {p nX nY nZ : ℕ}
  {X : Type*} [TopologicalSpace X] [ChartedSpace (ComplexModel nX) X] [IsComplexManifold nX X]
  {Y : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel nY) Y] [IsComplexManifold nY Y]
  {Z : Type*} [TopologicalSpace Z] [ChartedSpace (ComplexModel nZ) Z] [IsComplexManifold nZ Z]

/-- **`(f ∘ g)^* a = g^* (f^* a)` geometrically**, for holomorphic `g : Z → Y`, `f : Y → X`
between manifolds of possibly different dimensions. -/
theorem pullback_comp_geometricallyEq' {f : Y → X} {g : Z → Y}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel nY) 𝓘(ℂ, ComplexModel nX) ∞ f)
    (hg : ContMDiff 𝓘(ℂ, ComplexModel nZ) 𝓘(ℂ, ComplexModel nY) ∞ g)
    (a : SmoothRealForm nX X p) :
    (SmoothRealForm.pullback (hf.comp hg) a).GeometricallyEq
      (SmoothRealForm.pullback hg (SmoothRealForm.pullback hf a)) := by
  intro e z hz
  set x : Z := e.val.symm z with hx
  set d₂ := complexChartAt (n := nY) (g x) with hd₂
  set d₁ := complexChartAt (n := nX) (f (g x)) with hd₁
  have hgx : g x ∈ d₂.val.source := mem_complexChartAt_source _
  have hfgx : f (g x) ∈ d₁.val.source := mem_complexChartAt_source _
  set w : ComplexModel nY := coordinateMap g e d₂ z with hw
  have hwx : d₂.val.symm w = g x := by
    rw [hw]
    exact d₂.val.left_inv hgx
  have hzdom : z ∈ coordinateDomain g e d₂ := ⟨hz, by
    simpa only [mem_preimage, ← hx] using hgx⟩
  have hwdom : w ∈ coordinateDomain f d₂ d₁ :=
    ⟨d₂.val.map_source hgx, by simpa only [mem_preimage, hwx] using hfgx⟩
  have heq : coordinateMap (f ∘ g) e d₁ =ᶠ[𝓝 z]
      (coordinateMap f d₂ d₁) ∘ (coordinateMap g e d₂) := by
    filter_upwards [(coordinateDomain_isOpen hg e d₂).mem_nhds hzdom] with y hy
    show d₁.val (f (g (e.val.symm y))) =
      d₁.val (f (d₂.val.symm (d₂.val (g (e.val.symm y)))))
    rw [d₂.val.left_inv hy.2]
  have hchain : fderiv ℝ (coordinateMap (f ∘ g) e d₁) z =
      (fderiv ℝ (coordinateMap f d₂ d₁) w).comp
        (fderiv ℝ (coordinateMap g e d₂) z) := by
    rw [heq.fderiv_eq]
    exact fderiv_comp z
      ((coordinateMap_contDiffAt_real hf d₂ d₁ hwdom).differentiableAt (by simp))
      ((coordinateMap_contDiffAt_real hg e d₂ hzdom).differentiableAt (by simp))
  have hpoint : coordinateMap f d₂ d₁ w = coordinateMap (f ∘ g) e d₁ z := by
    show d₁.val (f (d₂.val.symm w)) = d₁.val (f (g (e.val.symm z)))
    rw [hwx]
  ext v
  show (a.coeff d₁ (coordinateMap (f ∘ g) e d₁ z))
      (fun i => fderiv ℝ (coordinateMap (f ∘ g) e d₁) z (v i)) = _
  rw [hchain]
  show _ = ((SmoothRealForm.pullback hf a).coeff d₂ w)
      (fun i => fderiv ℝ (coordinateMap g e d₂) z (v i))
  have hinner : (SmoothRealForm.pullback hf a).coeff d₂ w =
      (a.coeff d₁ (coordinateMap f d₂ d₁ w)).compContinuousLinearMap
        (fderiv ℝ (coordinateMap f d₂ d₁) w) := by
    show SmoothRealForm.chartPullbackCoeff a f d₂
      (complexChartAt (n := nX) (f (d₂.val.symm w))) w = _
    rw [hwx, ← hd₁]
    rfl
  rw [hinner, hpoint]
  rfl

end Pullback

end SGPT.Okounkov.TranscendentalVolId
