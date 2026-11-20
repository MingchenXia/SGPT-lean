import SGPT.Unibranch.KS3BlowupPositivity
import SGPT.Unibranch.KS3BlowupMonomial

/-!
# The Blanchard weight in monomial coordinates

Lane KS3 (Kähler preservation under blowups, `def:unibranch:L212`).  On the blowup of
`O × ℂ^r` (`O ⊆ ℂ^N` open) along the zero plane, in monomial coordinates `w ∈ ℂ^{N+r}` with
distinguished index `j ≥ N` (`KS3BlowupMonomial.exists_monomialCoords`), the Blanchard weight
`U = c₀ ‖G‖² + Σ_x c_x ‖B_x G‖²` of `X` (with `G = t ŵ` on the strict transform of the graph of
the generators `G`) factors as `|t|² · monomialWeight`, where

`monomialWeight w = c₀(Q w) ‖ŵ‖² + Σ_x c_x(Q w) Σ_i |Σ_l B_{x,i,l}(Q w) ŵ_l|²`,

`ŵ_l = hatCoord j w (N + l)` and `Q w = P₀ + (w_0, …, w_{N-1})` (`baseMap`) is the base point.
This file proves the smoothness (`contDiffOn_monomialWeight`), the positivity
(`monomialWeight_pos`), the factorization (`sum_eq_normSq_mul_monomialWeight`) and the
Fubini–Study positivity of `ddᶜ log monomialWeight` in fibre directions
(`smoothDDC_log_monomialWeight_pos`).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace SGPT.Unibranch.KS3MonomialWeight

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
  BlowupWeightLevi ProductComplexManifold

variable {N r : ℕ}

/-- The base point `Q w = P₀ + (w_0, …, w_{N-1})` of a point with monomial coordinates `w`. -/
def baseMap (P₀ : ComplexModel N) (w : ComplexModel (N + r)) : ComplexModel N :=
  P₀ + ((prodModelEquiv N r).symm w).1

theorem symm_fst_apply (w : ComplexModel (N + r)) (i : Fin N) :
    ((prodModelEquiv N r).symm w).1 i = w (Fin.castAdd r i) := by
  have h := KS3BlowupMonomial.prodModelEquiv_castAdd ((prodModelEquiv N r).symm w).1
    ((prodModelEquiv N r).symm w).2 i
  rw [Prod.mk.eta, ContinuousLinearEquiv.apply_symm_apply] at h
  exact h.symm

theorem baseMap_apply (P₀ : ComplexModel N) (w : ComplexModel (N + r)) (i : Fin N) :
    baseMap P₀ w i = P₀ i + w (Fin.castAdd r i) := by
  rw [baseMap, PiLp.add_apply, symm_fst_apply]

theorem contDiff_baseMap (P₀ : ComplexModel N) :
    ContDiff ℂ ∞ (baseMap (r := r) P₀) :=
  contDiff_const.add ((ContinuousLinearMap.fst ℂ (ComplexModel N) (ComplexModel r)).contDiff.comp
    (prodModelEquiv N r).symm.contDiff)

theorem baseMap_line (P₀ : ComplexModel N) (w v : ComplexModel (N + r))
    (hv : ∀ i : Fin N, v (Fin.castAdd r i) = 0) (t : ℂ) :
    baseMap P₀ (w + t • v) = baseMap P₀ w := by
  ext i
  rw [baseMap_apply, baseMap_apply, PiLp.add_apply, PiLp.smul_apply, hv i, smul_zero, add_zero]

theorem contDiff_hatCoord {n : ℕ} (j l : Fin n) :
    ContDiff ℂ ∞ (fun w : ComplexModel n => hatCoord j w l) := by
  by_cases hl : l = j
  · simp only [hatCoord, hl, if_true]
    exact contDiff_const
  · simp only [hatCoord, hl, if_false]
    exact (EuclideanSpace.proj l : ComplexModel n →L[ℂ] ℂ).contDiff

theorem hatCoord_self {n : ℕ} (j : Fin n) (w : ComplexModel n) : hatCoord j w j = 1 := by
  simp [hatCoord]

theorem contDiffOn_normSq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {s : Set E}
    {f : E → ℂ} (hf : ContDiffOn ℝ ∞ f s) :
    ContDiffOn ℝ ∞ (fun x => Complex.normSq (f x)) s := by
  simp only [Complex.normSq_apply]
  exact ((Complex.reCLM.contDiff.comp_contDiffOn hf).mul
      (Complex.reCLM.contDiff.comp_contDiffOn hf)).add
    ((Complex.imCLM.contDiff.comp_contDiffOn hf).mul (Complex.imCLM.contDiff.comp_contDiffOn hf))

variable {ι : Type} [Fintype ι] {rr : ι → ℕ}

/-- **The Blanchard weight in monomial coordinates.** -/
def monomialWeight (j : Fin (N + r)) (Q : ComplexModel (N + r) → ComplexModel N)
    (c₀ : ComplexModel N → ℝ) (c : ι → ComplexModel N → ℝ)
    (Bm : (x : ι) → Fin (rr x) → Fin r → ComplexModel N → ℂ) (w : ComplexModel (N + r)) : ℝ :=
  c₀ (Q w) * ∑ l, Complex.normSq (hatCoord j w (Fin.natAdd N l)) +
    ∑ x, c x (Q w) * ∑ i, Complex.normSq (∑ l, Bm x i l (Q w) * hatCoord j w (Fin.natAdd N l))

variable (j : Fin (N + r)) {Q : ComplexModel (N + r) → ComplexModel N}
  {c₀ : ComplexModel N → ℝ} {c : ι → ComplexModel N → ℝ}
  {Bm : (x : ι) → Fin (rr x) → Fin r → ComplexModel N → ℂ}

theorem contDiffOn_monomialWeight (hQ : ContDiff ℂ ∞ Q) {V₀ : Set (ComplexModel N)}
    (hV₀ : IsOpen V₀) (hc₀ : ContDiffOn ℝ ∞ c₀ V₀) (hc : ∀ x, ContDiffOn ℝ ∞ (c x) V₀)
    (hB : ∀ x i l, DifferentiableOn ℂ (Bm x i l) V₀) :
    ContDiffOn ℝ ∞ (monomialWeight j Q c₀ c Bm) (Q ⁻¹' V₀) := by
  have hQr : ContDiff ℝ ∞ Q := hQ.restrict_scalars ℝ
  have hmaps : MapsTo Q (Q ⁻¹' V₀) V₀ := fun _ hw => hw
  have hhat : ∀ l : Fin r, ContDiffOn ℝ ∞
      (fun w : ComplexModel (N + r) => hatCoord j w (Fin.natAdd N l)) (Q ⁻¹' V₀) := fun l =>
    ((contDiff_hatCoord j (Fin.natAdd N l)).restrict_scalars ℝ).contDiffOn
  have hBQ : ∀ x i l, ContDiffOn ℝ ∞ (fun w => Bm x i l (Q w)) (Q ⁻¹' V₀) := fun x i l =>
    ((contDiffOn_of_differentiableOn_complex (hB x i l) hV₀).restrict_scalars ℝ).comp
      hQr.contDiffOn hmaps
  refine ((hc₀.comp hQr.contDiffOn hmaps).mul
    (ContDiffOn.sum fun l _ => contDiffOn_normSq (hhat l))).add
    (ContDiffOn.sum fun x _ => ((hc x).comp hQr.contDiffOn hmaps).mul
      (ContDiffOn.sum fun i _ => contDiffOn_normSq
        (ContDiffOn.sum fun l _ => (hBQ x i l).mul (hhat l))))

theorem monomialWeight_pos (hj : N ≤ j.1) {w : ComplexModel (N + r)} (hc₀ : 0 < c₀ (Q w))
    (hc : ∀ x, 0 ≤ c x (Q w)) : 0 < monomialWeight j Q c₀ c Bm w := by
  have hj' : Fin.natAdd N ⟨j.1 - N, by omega⟩ = j := Fin.ext (by simp; omega)
  have h1 : 1 ≤ ∑ l, Complex.normSq (hatCoord j w (Fin.natAdd N l)) := by
    have := Finset.single_le_sum (f := fun l => Complex.normSq (hatCoord j w (Fin.natAdd N l)))
      (fun l _ => Complex.normSq_nonneg _) (Finset.mem_univ ⟨j.1 - N, by omega⟩)
    simp only [hj', hatCoord_self, map_one] at this
    exact this
  have h2 : 0 ≤ ∑ x, c x (Q w) *
      ∑ i, Complex.normSq (∑ l, Bm x i l (Q w) * hatCoord j w (Fin.natAdd N l)) :=
    Finset.sum_nonneg fun x _ => mul_nonneg (hc x)
      (Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _)
  unfold monomialWeight
  nlinarith

/-- **Factorization of the weight.** -/
theorem sum_eq_normSq_mul_monomialWeight (w : ComplexModel (N + r)) (t : ℂ) (G : Fin r → ℂ)
    (hG : ∀ l, G l = t * hatCoord j w (Fin.natAdd N l)) :
    c₀ (Q w) * ∑ l, Complex.normSq (G l) +
      ∑ x, c x (Q w) * ∑ i, Complex.normSq (∑ l, Bm x i l (Q w) * G l) =
      Complex.normSq t * monomialWeight j Q c₀ c Bm w := by
  have h1 : ∑ l, Complex.normSq (G l) =
      Complex.normSq t * ∑ l, Complex.normSq (hatCoord j w (Fin.natAdd N l)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => by rw [hG l, Complex.normSq_mul]
  have h2 : ∀ x i, Complex.normSq (∑ l, Bm x i l (Q w) * G l) =
      Complex.normSq t * Complex.normSq (∑ l, Bm x i l (Q w) * hatCoord j w (Fin.natAdd N l)) := by
    intro x i
    have : ∑ l, Bm x i l (Q w) * G l =
        t * ∑ l, Bm x i l (Q w) * hatCoord j w (Fin.natAdd N l) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun l _ => by rw [hG l]; ring
    rw [this, Complex.normSq_mul]
  simp only [h2]
  rw [h1, monomialWeight, mul_add]
  congr 1
  · ring
  · simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun i _ => by ring

/-- **Fubini–Study positivity of `ddᶜ log monomialWeight` in fibre directions.** -/
theorem smoothDDC_log_monomialWeight_pos (hj : N ≤ j.1) (P₀ : ComplexModel N)
    {V₀ : Set (ComplexModel N)} (hV₀ : IsOpen V₀) (hc₀s : ContDiffOn ℝ ∞ c₀ V₀)
    (hcs : ∀ x, ContDiffOn ℝ ∞ (c x) V₀) (hB : ∀ x i l, DifferentiableOn ℂ (Bm x i l) V₀)
    {w₀ : ComplexModel (N + r)} (hw₀ : baseMap P₀ w₀ ∈ V₀) (hc₀ : 0 < c₀ (baseMap P₀ w₀))
    (hc : ∀ x, 0 ≤ c x (baseMap P₀ w₀)) {v : ComplexModel (N + r)} (hv : v ≠ 0)
    (hv0 : ∀ i : Fin (N + r), ¬ (N ≤ i.1 ∧ i ≠ j) → v i = 0) :
    0 < smoothDDC (fun w => Real.log (monomialWeight j (baseMap P₀) c₀ c Bm w)) w₀
      ![v, Complex.I • v] := by
  have hcast : ∀ i : Fin N, v (Fin.castAdd r i) = 0 := fun i =>
    hv0 _ (fun h => by simp at h; omega)
  have hline : ∀ t : ℂ, baseMap P₀ (w₀ + t • v) = baseMap P₀ w₀ :=
    baseMap_line P₀ w₀ v hcast
  have hpos := monomialWeight_pos (Bm := Bm) j hj hc₀ hc
  have hsm := contDiffOn_monomialWeight j (contDiff_baseMap (r := r) P₀) hV₀ hc₀s hcs hB
  have hC : ContDiffAt ℝ ∞ (monomialWeight j (baseMap P₀) c₀ c Bm) w₀ :=
    hsm.contDiffAt (((contDiff_baseMap (r := r) P₀).continuous.isOpen_preimage _ hV₀).mem_nhds hw₀)
  have hC2 : ContDiffAt ℝ 2
      (fun w => Real.log (monomialWeight j (baseMap P₀) c₀ c Bm w)) w₀ :=
    (hC.log hpos.ne').of_le (by simpa using ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hvj : v j = 0 := hv0 j (fun h => h.2 rfl)
  have hvl : ∃ l : Fin r, v (Fin.natAdd N l) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hv
    ext i
    by_cases hi : N ≤ i.1 ∧ i ≠ j
    · have hi' : Fin.natAdd N ⟨i.1 - N, by omega⟩ = i := Fin.ext (by simp; omega)
      rw [← hi']
      exact hcon _
    · exact hv0 i hi
  exact KS3BlowupPositivity.fibre_pos (Fin.natAdd N) ⟨⟨j.1 - N, by omega⟩, Fin.ext (by simp; omega)⟩
    (fun w => c₀ (baseMap P₀ w)) (fun x w => c x (baseMap P₀ w))
    (fun x i l w => Bm x i l (baseMap P₀ w)) hC2 hc₀ hc
    (fun t => by simp only [hline]) (fun x t => by simp only [hline])
    (fun x i l t => by simp only [hline]) hvj hvl

end SGPT.Unibranch.KS3MonomialWeight
