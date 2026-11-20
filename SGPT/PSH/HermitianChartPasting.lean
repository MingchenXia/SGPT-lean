import SGPT.PSH.HermitianPasting

/-!
# Compact coordinate-domain Hermitian pasting

Compact containment in an actual chart produces the manifold-domain closure
condition. The boundary inequality is supplied in coordinates and transported
internally; no global positivity or boundary certificate is assumed.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.Hermitian

open Set Filter TopologicalSpace
open scoped Topology ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending.ERealBoundaryMaxPastingTopology

variable {m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]

/-- The actual manifold preimage of a coordinate domain, restricted to the
source of the chosen holomorphic chart. -/
def chartDomain (e : ComplexChart (m + 1) M) (D : Set (ComplexModel (m + 1))) : Set M :=
  e.val.source ∩ e.val ⁻¹' D

/-- Compact containment in the chart target prevents the closure of the
manifold patch from acquiring points outside the chart source. -/
theorem closure_chartDomain_subset_source
    (e : ComplexChart (m + 1) M) {D : Set (ComplexModel (m + 1))}
    (hDc : IsCompact (closure D)) (hDt : closure D ⊆ e.val.target) :
    closure (chartDomain e D) ⊆ e.val.source := by
  have hK : IsCompact (e.val.symm '' closure D) :=
    hDc.image_of_continuousOn (e.val.continuousOn_symm.mono hDt)
  have hsub : chartDomain e D ⊆ e.val.symm '' closure D := by
    intro x hx
    exact ⟨e.val x, subset_closure hx.2, e.val.left_inv hx.1⟩
  intro x hx
  obtain ⟨z, hz, rfl⟩ := closure_minimal hsub hK.isClosed hx
  exact e.val.map_target (hDt hz)

/-- Genuine coordinate boundary upper limits pull back to the compactly
contained manifold patch, retaining arbitrary negative-infinite values. -/
theorem boundaryDominatedOn_chartDomain
    (e : ComplexChart (m + 1) M) {D : Set (ComplexModel (m + 1))}
    (hD : IsOpen D) (hDc : IsCompact (closure D)) (hDt : closure D ⊆ e.val.target)
    {v : ComplexModel (m + 1) → EReal} {u : M → EReal}
    (hb : ∀ z ∈ frontier D, limsup v (𝓝[D] z) ≤ chartFunction u e z) :
    BoundaryDominatedOn univ (chartDomain e D) (fun x => v (e.val x)) u := by
  intro x hx c hc
  have hxs : x ∈ e.val.source :=
    closure_chartDomain_subset_source e hDc hDt (frontier_subset_closure hx.2)
  have hxc : ContinuousAt e.val x := e.val.continuousAt hxs
  have hxcl : e.val x ∈ closure D :=
    (closure_mono (image_subset_iff.mpr (fun _ hy => hy.2)))
      (mem_closure_image hxc (frontier_subset_closure hx.2))
  have hU : IsOpen (chartDomain e D) := e.val.isOpen_inter_preimage hD
  have hxnot : e.val x ∉ D := by
    intro hxD
    exact hx.2.2 (by rw [hU.interior_eq]; exact ⟨hxs, hxD⟩)
  have hxfr : e.val x ∈ frontier D := by
    rw [hD.frontier_eq]
    exact ⟨hxcl, hxnot⟩
  have huc : chartFunction u e (e.val x) < c := by
    simpa only [chartFunction, e.val.left_inv hxs] using hc
  have hnear : ∀ᶠ z in 𝓝 (e.val x), z ∈ D → v z < c :=
    eventually_nhdsWithin_iff.mp
      (eventually_lt_of_limsup_lt ((hb (e.val x) hxfr).trans_lt huc))
  apply eventually_nhdsWithin_iff.mpr
  filter_upwards [hxc.tendsto.eventually hnear] with y hy hyU
  exact hy hyU.2

/-- The exact chart replacement used in the frozen-background argument:
the maximum inside a relatively compact coordinate domain, and the original
global potential outside it, belongs to the original Hermitian class. -/
theorem isHermitianPSH_chart_gluedMax_of_boundary_limsup
    (omega : Background (m + 1) M) (e : ComplexChart (m + 1) M)
    {D : Set (ComplexModel (m + 1))} (hD : IsOpen D)
    (hDc : IsCompact (closure D)) (hDt : closure D ⊆ e.val.target)
    {v : ComplexModel (m + 1) → EReal} {q : ComplexModel (m + 1) → ℝ}
    (hq : ContDiffOn ℝ ∞ q D)
    (hp : PlurisubharmonicOn (fun y => v y + (q y : EReal)) D)
    (hdom : ∀ y ∈ D, ∀ a : ComplexModel (m + 1),
      smoothDDC q y ![a, Complex.I • a] ≤ omega.form.coeff e y ![a, Complex.I • a])
    {u : M → EReal} (hu : IsHermitianPSH omega u)
    (hb : ∀ z ∈ frontier D, limsup v (𝓝[D] z) ≤ chartFunction u e z) :
    IsHermitianPSH omega (gluedMax (chartDomain e D) (fun x => v (e.val x)) u) := by
  have hU : IsOpen (chartDomain e D) := e.val.isOpen_inter_preimage hD
  have hdomD : e.val.target ∩ e.val.symm ⁻¹' chartDomain e D ⊆ D := by
    intro y hy
    have h := hy.2.2
    change e.val (e.val.symm y) ∈ D at h
    simpa only [e.val.right_inv hy.1] using h
  have hlocal := hasDominatedLocalPSHCorrections_of_chart omega.form e
    (v := fun x => v (e.val x)) hU
    (fun _ hx => hx.1) (hq.mono hdomD) ?_ (fun y hy a => hdom y (hdomD hy) a)
  · exact isFormPSH_gluedMax_of_boundary omega.form omega.isTypeOneOne hU hlocal hu
      (boundaryDominatedOn_chartDomain e hD hDc hDt hb)
  · intro y hy
    apply (hp y (hdomD hy)).congr
    filter_upwards [e.val.open_target.mem_nhds hy.1] with t ht
    change v t + (q t : EReal) = v (e.val (e.val.symm t)) + (q t : EReal)
    rw [e.val.right_inv ht]

end SGPT.PSH.Hermitian
