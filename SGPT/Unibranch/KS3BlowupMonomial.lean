import SGPT.Foundations.Analysis.Pending.BlowupLocalSurjectivity
import SGPT.Foundations.Analysis.Pending.BlowupFibreDirection
import SGPT.Foundations.Analysis.Pending.BlowupWeightLevi
import SGPT.Foundations.Analysis.Pending.HironakaProductZeroPlaneBlowup

/-!
# Monomial coordinates on the blowup of a zero plane

Lane KS3 (Kähler preservation under blowups, `def:unibranch:L212`).  Let `π : Z → M × ℂ^r` be
the blowup of `M × ℂ^r` along the zero plane `M × {0}` (`M` a complex manifold of dimension
`N`).  Near every point `ζ ∈ Z` there are holomorphic *monomial coordinates* `W : Z → ℂ^{N+r}`
and an index `j ≥ N` such that, with `t = W_j` and `ŵ_l = hatCoord j W (N + l)` (`ŵ_{j-N} = 1`),

* `(π z).2 = t · ŵ` (`snd_eq`), and
* the chart coordinates of `(π z).1` are those of `(π ζ).1` plus the first `N` monomial
  coordinates (`fst_eq`),

and `W` is an immersion at `ζ` in chart coordinates (`fderiv_ne_zero`), with vanishing
coordinates `l < N` and `j` on the kernel of `dπ` (`fderiv_apply_eq_zero`).  This is
`BlowupLocalSurjectivity.exists_monomialLocalInverse` for the flat chart of the zero plane.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

namespace SGPT.Unibranch.KS3BlowupMonomial

open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.FirstPass.BlowupSequences
  SGPT.Foundations.Analysis.Pending ProductComplexManifold BlowupFlatCoordinates BlowupMonomialCharts
  BlowupWeightLevi

open scoped ProductComplexManifold

variable {N r : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (ComplexModel N) M]
  [IsComplexManifold N M]

/-- The flat chart of the zero plane at `(p, 0)`: the product chart, recentred. -/
def flatChart (p : M) :
    LocalHolomorphicEquivAt (n := N + r)
      (chartAt (ComplexModel (N + r)) ((p, 0) : M × ComplexModel r) (p, 0)) :=
  let c := complexChartAt (n := N + r) ((p, 0) : M × ComplexModel r)
  { source := c.val.target
    target := (fun q : ComplexModel (N + r) => q + c.val (p, 0)) ⁻¹' c.val.target
    isOpen_source := c.val.open_target
    isOpen_target := c.val.open_target.preimage (continuous_id.add continuous_const)
    center_mem_source := c.val.map_source (mem_complexChartAt_source _)
    toFun := fun q => q - c.val (p, 0)
    invFun := fun q => q + c.val (p, 0)
    toFun_holomorphic := (differentiable_id.sub_const _).differentiableOn
    invFun_holomorphic := (differentiable_id.add_const _).differentiableOn
    mapsTo_toFun := fun q hq => by
      change (q - c.val (p, 0)) + c.val (p, 0) ∈ c.val.target
      simpa only [sub_add_cancel] using hq
    mapsTo_invFun := fun _ hq => hq
    left_inv := fun q _ => sub_add_cancel q _
    right_inv := fun q _ => add_sub_cancel_right q _ }

omit [IsComplexManifold N M] in
theorem chart_prod_apply (p : M) (q : M × ComplexModel r) :
    chartAt (ComplexModel (N + r)) ((p, 0) : M × ComplexModel r) q =
      prodModelEquiv N r (chartAt (ComplexModel N) p q.1, q.2) := by
  change prodModelEquiv N r (chartAt (ComplexModel N) p q.1,
    (chartAt (ComplexModel r) (0 : ComplexModel r)) q.2) = _
  rw [chartAt_self_eq]
  rfl

omit [IsComplexManifold N M] in
theorem flatChart_apply (p : M) (q : M × ComplexModel r) :
    (flatChart (r := r) p).toFun (chartAt (ComplexModel (N + r)) ((p, 0) : M × ComplexModel r) q) =
      prodModelEquiv N r (chartAt (ComplexModel N) p q.1 - chartAt (ComplexModel N) p p, q.2) := by
  change chartAt (ComplexModel (N + r)) ((p, 0) : M × ComplexModel r) q -
    chartAt (ComplexModel (N + r)) ((p, 0) : M × ComplexModel r) (p, 0) = _
  rw [chart_prod_apply, chart_prod_apply, ← map_sub]
  simp only [Prod.mk_sub_mk, sub_zero]

omit [IsComplexManifold N M] in
theorem flatChart_flat (p : M) {q : M × ComplexModel r}
    (_hq : q ∈ (chartAt (ComplexModel (N + r)) ((p, 0) : M × ComplexModel r)).source)
    (_hq' : chartAt (ComplexModel (N + r)) ((p, 0) : M × ComplexModel r) q ∈
      (flatChart (r := r) p).source) :
    (q ∈ {q : M × ComplexModel r | q.2 = 0} ↔
      (flatChart (r := r) p).toFun (chartAt (ComplexModel (N + r)) ((p, 0) : M × ComplexModel r) q)
        ∈ complexCoordinatePlane (N + r) N) := by
  rw [flatChart_apply, prodModelEquiv_mem_complexCoordinatePlane_iff]
  rfl

theorem prodModelEquiv_natAdd (x : ComplexModel N) (z : ComplexModel r) (l : Fin r) :
    prodModelEquiv N r (x, z) (Fin.natAdd N l) = z l := by
  simp [prodModelEquiv]

theorem prodModelEquiv_castAdd (x : ComplexModel N) (z : ComplexModel r) (i : Fin N) :
    prodModelEquiv N r (x, z) (Fin.castAdd r i) = x i := by
  simp [prodModelEquiv]

variable {Z : Type} [TopologicalSpace Z] [ChartedSpace (ComplexModel (N + r)) Z]
  [IsComplexManifold (N + r) Z] {π : Z → M × ComplexModel r}

/-- **Monomial coordinates near a point of the blowup of a zero plane.** -/
theorem exists_monomialCoords (hπ : IsBlowupAlong (N + r) {q : M × ComplexModel r | q.2 = 0} π)
    (ζ : Z) :
    ∃ (j : Fin (N + r)) (_hj : N ≤ j.1) (O : Set Z) (W : Z → ComplexModel (N + r)),
      IsOpen O ∧ ζ ∈ O ∧
      (∀ z ∈ O, ContMDiffAt 𝓘(ℂ, ComplexModel (N + r)) 𝓘(ℂ, ComplexModel (N + r)) ∞ W z) ∧
      (∀ z ∈ O, (π z).1 ∈ (chartAt (ComplexModel N) (π ζ).1).source) ∧
      (∀ z ∈ O, ∀ l : Fin r, (π z).2 l = W z j * hatCoord j (W z) (Fin.natAdd N l)) ∧
      (∀ z ∈ O, ∀ i : Fin N, chartAt (ComplexModel N) (π ζ).1 (π z).1 i -
        chartAt (ComplexModel N) (π ζ).1 (π ζ).1 i = W z (Fin.castAdd r i)) ∧
      (∀ v : ComplexModel (N + r), v ≠ 0 →
        fderiv ℝ (fun u => W ((chartAt (ComplexModel (N + r)) ζ).symm u))
          (chartAt (ComplexModel (N + r)) ζ ζ) v ≠ 0) ∧
      (∀ v : ComplexModel (N + r),
        mfderiv 𝓘(ℂ, ComplexModel (N + r)) 𝓘(ℂ, ComplexModel (N + r)) π ζ v = 0 →
        ∀ i : Fin (N + r), ¬ (N ≤ i.1 ∧ i ≠ j) →
          fderiv ℝ (fun u => W ((chartAt (ComplexModel (N + r)) ζ).symm u))
            (chartAt (ComplexModel (N + r)) ζ ζ) v i = 0) := by
  set p := (π ζ).1
  set Φ := flatChart (N := N) (M := M) (r := r) p
  have hΦsrc : Φ.source ⊆ (chartAt (ComplexModel (N + r)) ((p, 0) : M × ComplexModel r)).target :=
    Subset.rfl
  have hflat : ∀ {y : M × ComplexModel r},
      y ∈ (chartAt (ComplexModel (N + r)) ((p, 0) : M × ComplexModel r)).source →
      chartAt (ComplexModel (N + r)) ((p, 0) : M × ComplexModel r) y ∈ Φ.source →
        (y ∈ {q : M × ComplexModel r | q.2 = 0} ↔
          Φ.toFun (chartAt (ComplexModel (N + r)) ((p, 0) : M × ComplexModel r) y) ∈
            complexCoordinatePlane (N + r) N) := fun hy hy' => flatChart_flat (N := N) (r := r) p hy hy'
  have hsrc : π ζ ∈ (chartAt (ComplexModel (N + r)) ((p, 0) : M × ComplexModel r)).source := by
    rw [chartAt_prod, prodChart_source]
    exact ⟨mem_chart_source _ p, by simp⟩
  have hz : π ζ ∈ flatDomain Φ :=
    ⟨hsrc, (chartAt (ComplexModel (N + r)) ((p, 0) : M × ComplexModel r)).map_source hsrc⟩
  obtain ⟨j, hj, O, hO, hζO, W, hWs, hWeq, hℓ, -⟩ :=
    BlowupLocalSurjectivity.exists_monomialLocalInverse hπ hΦsrc hflat hz
  have hsrcO : ∀ z ∈ O, (π z).1 ∈ (chartAt (ComplexModel N) p).source := by
    intro z hz'
    have h1 := (hWeq z hz').1.1
    rw [chartAt_prod, prodChart_source] at h1
    exact h1.1
  have hmono : ∀ z ∈ O, monomial N j (W z) =
      prodModelEquiv N r (chartAt (ComplexModel N) p (π z).1 - chartAt (ComplexModel N) p p,
        (π z).2) := by
    intro z hz'
    rw [(hWeq z hz').2, flatChart_apply]
  refine ⟨j, hj, O, W, hO, hζO, hWs, hsrcO, ?_, ?_, ?_, ?_⟩
  · intro z hz' l
    have h := congrArg (fun w : ComplexModel (N + r) => w (Fin.natAdd N l)) (hmono z hz')
    simp only [prodModelEquiv_natAdd, monomial_apply] at h
    rw [← h]
    by_cases hl : Fin.natAdd N l = j
    · simp [hatCoord, hl]
    · have hNl : N ≤ (Fin.natAdd N l).1 := by simp
      simp [hatCoord, hl, hNl, mul_comm]
  · intro z hz' i
    have h := congrArg (fun w : ComplexModel (N + r) => w (Fin.castAdd r i)) (hmono z hz')
    simp only [prodModelEquiv_castAdd, monomial_apply] at h
    have hi : ¬ (N ≤ (Fin.castAdd r i).1 ∧ Fin.castAdd r i ≠ j) := by
      simp only [Fin.val_castAdd, not_and]
      intro h'
      exact absurd h' (by omega)
    rw [if_neg hi] at h
    rw [h]
    simp only [PiLp.sub_apply]
  · intro v hv
    have hWmem : ∀ z' ∈ O, W z' ∈ monomialDomain Φ N j := fun z' hz' => by
      show monomial N j (W z') ∈ Φ.target
      rw [(hWeq z' hz').2]
      exact Φ.mapsTo_toFun (hWeq z' hz').1.2
    obtain ⟨ℓ, ⟨hℓs, hℓπ⟩, -⟩ := BlowupLocalSurjectivity.existsUnique_monomialLift hπ hΦsrc hflat hj
    exact BlowupFibreDirection.fderiv_monomialInverse_ne_zero hO hWs hWmem hℓs (hℓ ℓ hℓs hℓπ)
      hζO hv
  · intro v hv i hi
    exact BlowupFibreDirection.fderiv_monomialInverse_apply_eq_zero hπ hO hWs hWeq hζO hv i hi

end SGPT.Unibranch.KS3BlowupMonomial
