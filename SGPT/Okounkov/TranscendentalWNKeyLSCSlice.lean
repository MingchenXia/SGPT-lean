import SGPT.Okounkov.TranscendentalWNKeyLSCExcChart

/-!
# Fibre coordinates near `ℰ \ X'` (package WN-KEY, lane WN-LSC)

Blueprint `claude-tok-wn-key`, node `tok-wn-key:fibre-limit-exceptional`, and `claude-tok-wn-lsc`,
node `tok-wn-lsc:slice-coords`; source WN21 §5.

At `q ∈ ℰ \ X'` the function `τ ∘ π_{ℙ¹} ∘ μ` is a coordinate of the monomial chart: there are
holomorphic coordinates `(t, y) ↦ Λ(t, y)` of `ℂ^{m+2}` with `τ(μ(ℓ_j(Λ(t, y)))) - τ(0) = t` and a
linear left inverse `y = ν(w)` (`SliceCoords`):

* chart `j = m + 1`: `Λ(t, y) = (y, t)`, `ν(w', w_{m+1}) = w'`;
* chart `j = m` (where `w_{m+1}(q) ≠ 0`, `ExcChart.W_idxT_ne_zero`): `Λ(t, y)` has
  `w_m = t / y_m`, `w_{m+1} = y_m` (so `τ = w_m w_{m+1} = t`), `ν` forgets `w_m`.

The slice `t = 0` is `ℰ`, the slices `t ≠ 0` are the fibres `X_τ`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

universe u

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

namespace SGPT.Okounkov.TranscendentalWN.LSC

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.BlowupMonomialCharts
open SGPT.Foundations.Analysis.Pending.ProductComplexManifold
open scoped SGPT.Foundations.Analysis.Pending.ProductComplexManifold
open SGPT.Okounkov.TranscendentalMain
open SGPT.Okounkov.TranscendentalWN

variable {m : ℕ} {F : OriginalFlagGeometry.{u} (m + 1)}

variable {𝒳 : Type u} [TopologicalSpace 𝒳] [ChartedSpace (ComplexModel (m + 1 + 1)) 𝒳]
  [IsComplexManifold (m + 1 + 1) 𝒳] {μ : 𝒳 → F.carrier × ProjectiveLine}

/-- **`tok-wn-lsc:slice-coords`**: fibre coordinates `(t, y)` on a monomial chart. -/
structure SliceCoords {q : 𝒳} (C : ExcChart F μ q) where
  Λ : ComplexModel 1 × ComplexModel (m + 1) → ComplexModel (m + 1 + 1)
  ν : ComplexModel (m + 1 + 1) →L[ℂ] ComplexModel (m + 1)
  G : Set (ComplexModel 1 × ComplexModel (m + 1))
  hG : IsOpen G
  hΛ : ∀ p ∈ G, ContDiffAt ℂ ∞ Λ p
  hνΛ : ∀ p ∈ G, ν (Λ p) = p.2
  hτΛ : ∀ p ∈ G, ((splitL m).symm (monomial m C.j (Λ p))).2 = p.1
  hΛE : ∀ y, ((0 : ComplexModel 1), y) ∈ G → Λ (0, y) C.j = 0
  O' : Set 𝒳
  hO' : IsOpen O'
  hO'O : O' ⊆ C.O
  hqO' : q ∈ O'
  hΛν : ∀ z ∈ O', ∀ t, ((splitL m).symm (monomial m C.j (C.W z))).2 = t →
    (t, ν (C.W z)) ∈ G ∧ Λ (t, ν (C.W z)) = C.W z

namespace SliceCoords

/-- The left inverse `w ↦ w'` in the chart `j = m + 1`. -/
def nuT (m : ℕ) : ComplexModel (m + 1 + 1) →L[ℂ] ComplexModel (m + 1) :=
  (ContinuousLinearMap.fst ℂ (ComplexModel (m + 1)) (ComplexModel 1)).comp
    ((splitL m).symm : ComplexModel (m + 1 + 1) →L[ℂ] _)

/-- The left inverse in the chart `j = m` (forget `w_m`, keep `w_{m+1}` as the last coordinate). -/
def nuZ (m : ℕ) : ComplexModel (m + 1 + 1) →L[ℂ] ComplexModel (m + 1) :=
  (nuT m).comp (swapNormal m : ComplexModel (m + 1 + 1) →L[ℂ] ComplexModel (m + 1 + 1))

theorem nuT_apply (w : ComplexModel (m + 1 + 1)) : nuT m w = ((splitL m).symm w).1 := rfl

theorem nuZ_apply (w : ComplexModel (m + 1 + 1)) :
    nuZ m w = ((splitL m).symm (swapNormal m w)).1 := rfl

theorem splitL_eq_iff (y : ComplexModel (m + 1)) (s : ComplexModel 1) (w : ComplexModel (m + 1 + 1)) :
    splitL m (y, s) = w ↔ y = ((splitL m).symm w).1 ∧ s 0 = w (idxT m) := by
  constructor
  · rintro rfl
    simp
  · rintro ⟨rfl, hs⟩
    apply (splitL m).symm.injective
    rw [ContinuousLinearEquiv.symm_apply_apply]
    refine Prod.ext rfl ?_
    ext i
    fin_cases i
    simp [hs]

/-- The coordinates of the chart `j = m + 1`. -/
def ofIdxT {q : 𝒳} (C : ExcChart F μ q) (hj : C.j = idxT m) : SliceCoords C where
  Λ p := splitL m (p.2, p.1)
  ν := nuT m
  G := univ
  hG := isOpen_univ
  hΛ p _ := by
    have h : ContDiff ℂ ∞ (fun p : ComplexModel 1 × ComplexModel (m + 1) => splitL m (p.2, p.1)) :=
      (splitL m).contDiff.comp (contDiff_snd.prodMk contDiff_fst)
    exact h.contDiffAt
  hνΛ p _ := by simp [nuT_apply]
  hτΛ p _ := by
    rw [hj, monomial_idxT_split]
    simp
  hΛE y _ := by rw [hj]; simp
  O' := C.O
  hO' := C.hO
  hO'O := subset_rfl
  hqO' := C.hqO
  hΛν z _ t ht := by
    refine ⟨mem_univ _, ?_⟩
    rw [splitL_eq_iff]
    refine ⟨rfl, ?_⟩
    have h := congrArg (fun v : ComplexModel 1 => v 0) ht
    simp only [splitL_symm_snd, monomial_apply, hj] at h
    simpa using h.symm

/-- The coordinates of the chart `j = m`, near a point with `w_{m+1} ≠ 0`. -/
def ofIdxZ {q : 𝒳} (C : ExcChart F μ q) (hj : C.j = idxZ m) (hq : C.W q (idxT m) ≠ 0) :
    SliceCoords C where
  Λ p := swapNormal m (splitL m (p.2, (p.2 (Fin.last m))⁻¹ • p.1))
  ν := nuZ m
  G := {p | p.2 (Fin.last m) ≠ 0}
  hG := isOpen_ne_fun ((PiLp.continuous_apply 2 _ (Fin.last m)).comp continuous_snd)
    continuous_const
  hΛ p hp := by
    have h1 : ContDiffAt ℂ ∞ (fun p : ComplexModel 1 × ComplexModel (m + 1) =>
        (p.2 (Fin.last m))⁻¹) p :=
      (((EuclideanSpace.proj (Fin.last m) : ComplexModel (m + 1) →L[ℂ] ℂ).contDiff.comp
        contDiff_snd).contDiffAt).inv hp
    have h2 : ContDiffAt ℂ ∞ (fun p : ComplexModel 1 × ComplexModel (m + 1) =>
        (p.2, (p.2 (Fin.last m))⁻¹ • p.1)) p :=
      contDiffAt_snd.prodMk (h1.smul contDiffAt_fst)
    exact ((swapNormal m : _ →L[ℂ] ComplexModel (m + 1 + 1)).contDiff.comp
      (splitL m : _ →L[ℂ] ComplexModel (m + 1 + 1)).contDiff).contDiffAt.comp p h2
  hνΛ p _ := by simp [nuZ_apply]
  hτΛ p hp := by
    rw [hj, monomial_idxZ_swapNormal, monomial_idxT_split, splitL_symm_snd_eq]
    ext i
    fin_cases i
    simp only [swapNormal_apply, Equiv.swap_apply_right]
    simp only [Fin.isValue, splitL_castSucc, scaleLast, if_true, PiLp.smul_apply, smul_eq_mul]
    exact mul_inv_cancel_left₀ hp _
  hΛE y _ := by
    rw [hj]
    simp
  O' := C.O ∩ {z | C.W z (idxT m) ≠ 0}
  hO' := by
    refine isOpen_iff_mem_nhds.mpr fun z hz => inter_mem (C.hO.mem_nhds hz.1) ?_
    exact (((PiLp.continuous_apply 2 _ (idxT m)).continuousAt).comp
      (C.hW z hz.1).continuousAt).preimage_mem_nhds (isOpen_ne.mem_nhds hz.2)
  hO'O := inter_subset_left
  hqO' := ⟨C.hqO, hq⟩
  hΛν z hz t ht := by
    have hzT : C.W z (idxT m) ≠ 0 := hz.2
    have hν : nuZ m (C.W z) (Fin.last m) = C.W z (idxT m) := by
      rw [nuZ_apply, splitL_symm_fst]
      simp [Equiv.swap_apply_left]
    refine ⟨by simpa [hν] using hzT, ?_⟩
    have h := congrArg (fun v : ComplexModel 1 => v 0) ht
    simp only [splitL_symm_snd, monomial_apply, hj] at h
    rw [if_pos ⟨by simp, idxZ_ne_idxT.symm⟩] at h
    apply (swapNormal m).symm.injective
    rw [ContinuousLinearEquiv.symm_apply_apply, swapNormal_symm_apply, splitL_eq_iff]
    refine ⟨by rw [← nuZ_apply], ?_⟩
    simp only [hν, PiLp.smul_apply, smul_eq_mul, swapNormal_apply, Equiv.swap_apply_right]
    rw [← h]
    field_simp

/-- **`tok-wn-lsc:slice-coords`**: fibre coordinates exist at every `q ∈ ℰ \ X'`. -/
theorem nonempty {q : 𝒳} (C : ExcChart F μ q) (hqE : q ∈ exceptionalSet F μ)
    (hqX : q ∉ strictCentralFibre F μ) : Nonempty (SliceCoords C) := by
  rcases C.hj with hj | hj
  · exact ⟨ofIdxZ C hj (C.W_idxT_ne_zero hj hqE hqX)⟩
  · exact ⟨ofIdxT C hj⟩

end SliceCoords

end SGPT.Okounkov.TranscendentalWN.LSC
