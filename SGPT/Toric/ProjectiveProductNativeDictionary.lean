import SGPT.Toric.ProjectiveProductNativeReverse

set_option autoImplicit false
noncomputable section
namespace SGPT.Toric
open Set Filter MeasureTheory SGPT.PSH SGPT.Convex
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.BoundedGlobalProduct
open scoped Topology RealInnerProductSpace

/-- Actual native PSH comparison on the original torus extends across the
produced coordinate-null boundary, without changing extended values. -/
theorem projectiveProduct_le_of_le_torus {n : ℕ}
    {u v : projectiveProductSpace n → EReal}
    (hu : IsThetaPshPotential (projectiveProductFSBackground n).form.val u)
    (hv : IsThetaPshPotential (projectiveProductFSBackground n).form.val v)
    (h : ∀ p ∈ projectiveProductTorus n, u p ≤ v p) : u ≤ v := by
  intro p
  obtain ⟨ε, hε⟩ := projectiveProductNativeChart_exhaustive (complexChartAt (n := n) p)
  let e := projectiveProductNativeChart n ε
  have hs : p ∈ e.val.source := by
    have h := mem_complexChartAt_source (n := n) p
    rw [hε] at h
    exact h
  have hpu := BoundedGlobalProduct.ThetaPlurisubharmonic.corrected_plurisubharmonicOn
    hu.1 e (projectiveProductFSPotential_localPotential n ε)
  have hpv := BoundedGlobalProduct.ThetaPlurisubharmonic.corrected_plurisubharmonicOn
    hv.1 e (projectiveProductFSPotential_localPotential n ε)
  have ht : ∀ᵐ z ∂(volume : Measure (ComplexModel n)), e.val.symm z ∈ projectiveProductTorus n := by
    apply ae_iff.mpr
    simpa only [mem_compl_iff] using projectiveProductBoundary_chart_volume_eq_zero n ε
  have hae : ∀ᵐ z ∂(volume : Measure (ComplexModel n)).restrict univ,
      chartFunction u e z + (projectiveProductFSPotential n z : EReal) ≤
        chartFunction v e z + (projectiveProductFSPotential n z : EReal) := by
    rw [Measure.restrict_univ]
    filter_upwards [ht] with z hz
    exact add_le_add (h _ hz) le_rfl
  have he := hpu.le_of_ae_le isOpen_univ hpv.upperSemicontinuousOn volume hae
    (e.val p) (mem_univ _)
  change u (e.val.symm (e.val p)) + (projectiveProductFSPotential n (e.val p) : EReal) ≤
    v (e.val.symm (e.val p)) + (projectiveProductFSPotential n (e.val p) : EReal) at he
  rw [e.val.left_inv hs] at he
  exact (EReal.addLECancellable_coe _).add_le_add_iff_right.mp he

/-- Genuine native potentials with the same original torus values are pointwise equal. -/
theorem projectiveProduct_eq_of_eqOn_torus {n : ℕ}
    {u v : projectiveProductSpace n → EReal}
    (hu : IsThetaPshPotential (projectiveProductFSBackground n).form.val u)
    (hv : IsThetaPshPotential (projectiveProductFSBackground n).form.val v)
    (h : EqOn u v (projectiveProductTorus n)) : u = v :=
  le_antisymm (projectiveProduct_le_of_le_torus hu hv (fun _ hp => (h hp).le))
    (projectiveProduct_le_of_le_torus hv hu (fun _ hp => (h hp).ge))

/-- Exact positive radial values identify the original corrected descent of
the manufactured extension before any real readback. -/
theorem projectiveProductToricCorrectedDescent_extension {n : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : ConvexOn ℝ univ f) :
    projectiveProductToricCorrectedDescent (projectiveProductToricExtension f) =
      fun x => (f x : EReal) := by
  funext x
  let e := projectiveProductNativeChart n (fun _ => false)
  have hz : expCoordinates x ∈ e.val.target := by rw [projectiveProductNativeChart_target]; exact mem_univ _
  have hp : e.val.symm (expCoordinates x) ∈ projectiveProductTorus n :=
    (projectiveProductTorus_chart_symm n (fun _ => false) _).mpr (expCoordinates_mem_complexTorus x)
  have hρ := projectiveProductReferenceProfile_tropicalization (expCoordinates_mem_complexTorus x)
  rw [tropicalization_expCoordinates] at hρ
  change projectiveProductToricExtension f (e.val.symm (expCoordinates x)) +
    (projectiveProductReferenceProfile n x : EReal) = _
  rw [projectiveProductToricExtension_eq_off hf hp]
  change ((f (tropicalization (e.val (e.val.symm (expCoordinates x)))) -
    projectiveProductFSPotential n (e.val (e.val.symm (expCoordinates x))) : ℝ) : EReal) + _ = _
  rw [e.val.right_inv hz, tropicalization_expCoordinates, ← hρ, ← EReal.coe_add]
  congr 1
  ring

/-- Real readback occurs only after the exact finite corrected-value producer. -/
theorem projectiveProductToricEuclideanProfile_extension {n : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : ConvexOn ℝ univ f) :
    projectiveProductToricEuclideanProfile (projectiveProductToricExtension f) = f := by
  funext x
  simp only [projectiveProductToricEuclideanProfile,
    congrFun (projectiveProductToricCorrectedDescent_extension hf) x, EReal.toReal_coe]

/-- Genuine original invariant native PSH recovers the literal reverse torus
branch of its produced finite real profile, without discarding poles. -/
theorem projectiveProductToricOffPotential_eq_of_profile {n : ℕ}
    {u : projectiveProductSpace n → EReal}
    (hu : IsThetaPshPotential (projectiveProductFSBackground n).form.val u)
    (hi : ProjectiveProductCircleInvariant u) :
    EqOn u (projectiveProductToricOffPotential (projectiveProductToricEuclideanProfile u))
      (projectiveProductTorus n) := by
  intro p hp
  have hs := hp
  rw [← projectiveProductTorus_chart_source n] at hs
  let e := projectiveProductNativeChart n (fun _ => false)
  have hc := projectiveProductToricEuclideanProfile_corrected hu hi hs.2
  change u (e.val.symm (e.val p)) + (projectiveProductFSPotential n (e.val p) : EReal) =
    (projectiveProductToricEuclideanProfile u (tropicalization (e.val p)) : EReal) at hc
  rw [e.val.left_inv hs.1] at hc
  have hh : projectiveProductToricOffPotential (projectiveProductToricEuclideanProfile u) p +
      (projectiveProductFSPotential n (e.val p) : EReal) =
        (projectiveProductToricEuclideanProfile u (tropicalization (e.val p)) : EReal) := by
    change (((projectiveProductToricEuclideanProfile u (tropicalization (e.val p)) -
      projectiveProductFSPotential n (e.val p) : ℝ) : EReal) + _) = _
    rw [← EReal.coe_add]
    congr 1
    ring
  have he := hc.trans hh.symm
  exact le_antisymm ((EReal.addLECancellable_coe _).add_le_add_iff_right.mp he.le)
    ((EReal.addLECancellable_coe _).add_le_add_iff_right.mp he.ge)

/-- The actual original native invariant potentials and real cube-growth
functions have genuine inverse maps, on the original native product. -/
def projectiveProductToricEquivRealGrowth (n : ℕ) :
    {u : projectiveProductSpace n → EReal //
      IsThetaPshPotential (projectiveProductFSBackground n).form.val u ∧
        ProjectiveProductCircleInvariant u} ≃
    {f : EuclideanSpace ℝ (Fin n) → ℝ //
      f ∈ RealGrowthClass (innerₗ (EuclideanSpace ℝ (Fin n))) (euclideanUnitCube n)} where
  toFun u := ⟨projectiveProductToricEuclideanProfile u.val,
    projectiveProductToricEuclideanProfile_convex u.property.1 u.property.2,
    (projectiveProductToricProfile_mem_growthClass u.property.1 u.property.2).2⟩
  invFun f := ⟨projectiveProductToricExtension f.val,
    (projectiveProductToricExtension_spec f.property).1,
    (projectiveProductToricExtension_spec f.property).2.1⟩
  left_inv u := by
    apply Subtype.ext
    apply projectiveProduct_eq_of_eqOn_torus
      (isThetaPshPotential_projectiveProductToricExtension
        ⟨projectiveProductToricEuclideanProfile_convex u.property.1 u.property.2,
          (projectiveProductToricProfile_mem_growthClass u.property.1 u.property.2).2⟩) u.property.1
    intro p hp
    exact (projectiveProductToricExtension_eq_off
      (projectiveProductToricEuclideanProfile_convex u.property.1 u.property.2) hp).trans
        ((projectiveProductToricOffPotential_eq_of_profile u.property.1 u.property.2) hp).symm
  right_inv f := Subtype.ext (projectiveProductToricEuclideanProfile_extension f.property.1)

private theorem profile_coe {n : ℕ} {u : projectiveProductSpace n → EReal}
    (hu : IsThetaPshPotential (projectiveProductFSBackground n).form.val u)
    (hi : ProjectiveProductCircleInvariant u) (x : EuclideanSpace ℝ (Fin n)) :
    (projectiveProductToricEuclideanProfile u x : EReal) =
      projectiveProductToricCorrectedDescent u x := by
  have hf := finite_of_pshOn_tropicalPullback (pshOn_projectiveProductToricCorrectedDescent hu hi) x
  exact EReal.coe_toReal hf.1 hf.2

/-- The same finite original constant compares native invariant potentials
exactly when it compares their actual finite real convex profiles. -/
theorem projectiveProductToricProfile_le_add_iff {n : ℕ}
    {u v : projectiveProductSpace n → EReal}
    (hu : IsThetaPshPotential (projectiveProductFSBackground n).form.val u)
    (hv : IsThetaPshPotential (projectiveProductFSBackground n).form.val v)
    (hiu : ProjectiveProductCircleInvariant u) (hiv : ProjectiveProductCircleInvariant v) (C : ℝ) :
    (∀ p, u p ≤ v p + (C : EReal)) ↔
      ∀ x, projectiveProductToricEuclideanProfile u x ≤ projectiveProductToricEuclideanProfile v x + C := by
  constructor
  · intro h x
    let p := (projectiveProductNativeChart n (fun _ => false)).val.symm (expCoordinates x)
    have hc := add_le_add (h p) (le_refl (projectiveProductReferenceProfile n x : EReal))
    rw [add_right_comm (v p) (C : EReal)] at hc
    change projectiveProductToricCorrectedDescent u x ≤
      projectiveProductToricCorrectedDescent v x + (C : EReal) at hc
    rw [← profile_coe hu hiu x, ← profile_coe hv hiv x, ← EReal.coe_add] at hc
    exact EReal.coe_le_coe_iff.mp hc
  · intro h
    apply projectiveProduct_le_of_le_torus hu (hv.add_const C)
    intro p hp
    have hc := h (tropicalization ((projectiveProductNativeChart n (fun _ => false)).val p))
    have huOff := projectiveProductToricOffPotential_eq_of_profile hu hiu hp
    have hvOff := projectiveProductToricOffPotential_eq_of_profile hv hiv hp
    rw [huOff, hvOff]
    change (((projectiveProductToricEuclideanProfile u _ - projectiveProductFSPotential n _ : ℝ) : EReal)) ≤
      (((projectiveProductToricEuclideanProfile v _ - projectiveProductFSPotential n _ : ℝ) : EReal)) + (C : EReal)
    rw [← EReal.coe_add]
    apply EReal.coe_le_coe_iff.mpr
    linarith

/-- Exact original pointwise order is the actual finite convex-profile order. -/
theorem projectiveProductToricProfile_le_iff {n : ℕ}
    {u v : projectiveProductSpace n → EReal}
    (hu : IsThetaPshPotential (projectiveProductFSBackground n).form.val u)
    (hv : IsThetaPshPotential (projectiveProductFSBackground n).form.val v)
    (hiu : ProjectiveProductCircleInvariant u) (hiv : ProjectiveProductCircleInvariant v) :
    u ≤ v ↔ projectiveProductToricEuclideanProfile u ≤ projectiveProductToricEuclideanProfile v := by
  change (∀ p, u p ≤ v p) ↔ ∀ x,
    projectiveProductToricEuclideanProfile u x ≤ projectiveProductToricEuclideanProfile v x
  simpa only [EReal.coe_zero, add_zero] using projectiveProductToricProfile_le_add_iff hu hv hiu hiv 0

/-- The literal source singularity comparison preserves the same finite
constant under the actual native-to-convex dictionary. -/
theorem projectiveProductToricProfile_singularityLE_iff {n : ℕ}
    {u v : projectiveProductSpace n → EReal}
    (hu : IsThetaPshPotential (projectiveProductFSBackground n).form.val u)
    (hv : IsThetaPshPotential (projectiveProductFSBackground n).form.val v)
    (hiu : ProjectiveProductCircleInvariant u) (hiv : ProjectiveProductCircleInvariant v) :
    SingularityLE u v ↔
      SingularityLE (fun x => (projectiveProductToricEuclideanProfile u x : EReal))
        (fun x => (projectiveProductToricEuclideanProfile v x : EReal)) := by
  rw [singularityLE_iff_exists_real, singularityLE_iff_exists_real]
  apply exists_congr
  intro C
  simpa only [← EReal.coe_add, EReal.coe_le_coe_iff] using
    projectiveProductToricProfile_le_add_iff hu hv hiu hiv C

end SGPT.Toric
