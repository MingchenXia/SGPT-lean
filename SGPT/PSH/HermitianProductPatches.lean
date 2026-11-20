import SGPT.PSH.HermitianGlobalProducts
import SGPT.PSH.HermitianLocalCorrection

/-!
# Genuine nonclosed-background product patches

The correction is chosen from the background before all potentials. Bounded
Hermitian PSH potentials become ordinary locally bounded PSH functions on
these patches. The candidate product is the literal signed background
expansion; positivity and overlap invariance are separate analytic claims.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.HermitianGlobalProducts

open Set Filter Metric TopologicalSpace
open scoped Topology ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.Pending
open StronglyPositiveForms LocalProductCurrents LocalBedfordTaylorProducts LocalBedfordTaylorCollar
open Hermitian

variable {m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]

/-- Smooth correction data for a background, independent of any potential.
Its Hessian majorizes the actual background; it is not a local potential. -/
structure BackgroundPatch (omega : Background (m + 1) M) where
  geometry : CoordinatePatch (m + 1) M
  correction : ComplexModel (m + 1) → ℝ
  smooth : ContDiffOn ℝ ∞ correction geometry.domain
  dominates : ∀ z ∈ geometry.domain, ∀ v : ComplexModel (m + 1),
    omega.form.coeff geometry.chart z ![v, Complex.I • v] ≤
      smoothDDC correction z ![v, Complex.I • v]

namespace BackgroundPatch

variable {omega : Background (m + 1) M}

/-- The genuine real representative of the locally corrected function. -/
def correctedReal (P : BackgroundPatch omega) (u : M → EReal)
    (z : ComplexModel (m + 1)) : ℝ :=
  (chartFunction u P.geometry.chart z).toReal + P.correction z

/-- The smooth residual is the actual background minus the correction's
Hessian. It need not be closed or semipositive. -/
def residual (P : BackgroundPatch omega) (z : ComplexModel (m + 1)) : RealForm (m + 1) 2 :=
  omega.form.coeff P.geometry.chart z - smoothDDC P.correction z

theorem residual_smooth (P : BackgroundPatch omega) :
    ContDiffOn ℝ ∞ P.residual P.geometry.domain :=
  ((omega.form.smooth P.geometry.chart).mono P.geometry.domain_le_target).sub
    (contDiffOn_ddcForm P.smooth)

/-- Bounded actual Hermitian PSH potentials have ordinary locally bounded
PSH corrected representatives, with poles excluded by their real bounds. -/
theorem correctedReal_isLocallyBoundedPshOn (P : BackgroundPatch omega)
    {u : M → EReal} (hu : IsHermitianPSH omega u)
    (hb : ∃ a b : ℝ, ∀ x, (a : EReal) ≤ u x ∧ u x ≤ (b : EReal)) :
    IsLocallyBoundedPshOn P.geometry.domain (P.correctedReal u) := by
  obtain ⟨a, b, hab⟩ := hb
  have huf (x : M) : u x ≠ ⊤ ∧ u x ≠ ⊥ :=
    ⟨ne_of_lt ((hab x).2.trans_lt (EReal.coe_lt_top b)),
      ne_of_gt ((EReal.bot_lt_coe a).trans_le (hab x).1)⟩
  have hreal (z : ComplexModel (m + 1)) :
      ((P.correctedReal u z : ℝ) : EReal) =
        chartFunction u P.geometry.chart z + (P.correction z : EReal) := by
    rw [correctedReal, EReal.coe_add, chartFunction,
      EReal.coe_toReal (huf _).1 (huf _).2]
  refine ⟨?_, ?_⟩
  · have hp := chart_add_smooth_plurisubharmonicOn omega.isTypeOneOne hu
      P.geometry.chart P.geometry.domain_le_target P.smooth P.dominates
    intro z hz
    apply (hp z hz).congr
    exact Eventually.of_forall fun y => (hreal y).symm
  · intro z hz
    obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (P.geometry.domain.isOpen.mem_nhds hz)
    have hclosed : closedBall z (r / 2) ⊆ (P.geometry.domain : Set (ComplexModel (m + 1))) :=
      (closedBall_subset_ball (by linarith)).trans hball
    obtain ⟨C, hC⟩ := (isCompact_closedBall z (r / 2)).exists_bound_of_continuousOn
      (P.smooth.continuousOn.mono hclosed)
    refine ⟨⟨ball z (r / 2), isOpen_ball⟩, mem_ball_self (by linarith),
      ball_subset_closedBall.trans hclosed, max |a| |b| + C, ?_⟩
    intro w hw
    have hwC : |P.correction w| ≤ C := by
      simpa only [Real.norm_eq_abs] using hC w (ball_subset_closedBall hw)
    let s : ℝ := (chartFunction u P.geometry.chart w).toReal
    have hs : (s : EReal) = chartFunction u P.geometry.chart w :=
      EReal.coe_toReal (huf _).1 (huf _).2
    have hsa : a ≤ s := EReal.coe_le_coe_iff.mp (hs ▸ (hab _).1)
    have hsb : s ≤ b := EReal.coe_le_coe_iff.mp (hs ▸ (hab _).2)
    have habs : |s| ≤ max |a| |b| := by
      refine abs_le.mpr ⟨?_, hsb.trans ((le_abs_self b).trans (le_max_right _ _))⟩
      exact (neg_le_neg (le_max_left |a| |b|)).trans ((neg_abs_le a).trans hsa)
    calc
      |P.correctedReal u w| = |s + P.correction w| := rfl
      _ ≤ |s| + |P.correction w| := abs_add_le _ _
      _ ≤ max |a| |b| + C := add_le_add habs hwC

/-- The actual mixed expansion in every product degree. In particular,
`p = m` supplies the bidimension-one currents needed by integration by parts. -/
def mixedCurrent (P : BackgroundPatch omega) (p : ℕ) (hp : p ≤ m + 1)
    (u : Fin p → M → EReal) :
    LocalProductCurrent (m + 1) P.geometry.domain (m + 1 - p) :=
  HermitianProducts.backgroundExpansion p (m + 1 - p) (fun i => P.correctedReal (u i))
    P.residual_smooth (oneCurrentOf (U := P.geometry.domain) (Nat.sub_add_cancel hp))

/-- The candidate top-degree product is the actual background expansion.
No positivity, mass or overlap condition enters this definition. -/
def current (P : BackgroundPatch omega) (u : Fin (m + 1) → M → EReal) :
    LocalProductCurrent (m + 1) P.geometry.domain 0 :=
  HermitianProducts.backgroundExpansion (m + 1) 0 (fun i => P.correctedReal (u i))
    P.residual_smooth (oneCurrentOf (U := P.geometry.domain) (Nat.zero_add (m + 1)))

end BackgroundPatch

/-- Quadratic domination produces genuine background patches around every
point, before any tuple of potentials is supplied. -/
theorem exists_backgroundPatch_containing (omega : Background (m + 1) M) (x : M) :
    ∃ P : BackgroundPatch omega, x ∈ P.geometry.source := by
  let e := complexChartAt (n := m + 1) x
  have hx : x ∈ e.val.source := mem_complexChartAt_source x
  obtain ⟨A, r, _hA, hr, htarget, hdom⟩ :=
    HermitianQuadratic.exists_chart_quadratic_domination omega.form e (e.val.map_source hx)
  let Ω : Opens (ComplexModel (m + 1)) := ⟨ball (e.val x) r, isOpen_ball⟩
  refine ⟨{
    geometry := ⟨e, Ω, ball_subset_closedBall.trans htarget⟩
    correction := ballPot A (e.val x) 0
    smooth := (contDiff_ballPot A (e.val x) 0).contDiffOn
    dominates := fun z hz v => hdom z (ball_subset_closedBall hz) v }, ?_⟩
  exact ⟨hx, mem_ball_self hr⟩

/-- A finite ordered cover by actual majorizing-correction patches. -/
structure BackgroundFiniteCover (omega : Background (m + 1) M) where
  count : ℕ
  patch : Fin count → BackgroundPatch omega
  covers : ∀ x : M, ∃ i, x ∈ (patch i).geometry.source

/-- Compactness produces a finite cover independent of all potentials.
The empty manifold is allowed and may have a cover with zero patches. -/
theorem nonempty_backgroundFiniteCover [CompactSpace M] (omega : Background (m + 1) M) :
    Nonempty (BackgroundFiniteCover omega) := by
  classical
  have hcover : (univ : Set M) ⊆ ⋃ P : BackgroundPatch omega, (P.geometry.source : Set M) := by
    intro x _
    obtain ⟨P, hx⟩ := exists_backgroundPatch_containing omega x
    exact mem_iUnion.mpr ⟨P, hx⟩
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
    (fun P : BackgroundPatch omega => (P.geometry.source : Set M))
    (fun P => P.geometry.source.isOpen) hcover
  refine ⟨{
    count := s.card
    patch := fun i => (s.equivFin.symm i).val
    covers := ?_ }⟩
  intro x
  obtain ⟨P, hPx⟩ := mem_iUnion.mp (hs (mem_univ x))
  obtain ⟨hP, hx⟩ := mem_iUnion.mp hPx
  refine ⟨s.equivFin ⟨P, hP⟩, ?_⟩
  change x ∈ (((s.equivFin.symm (s.equivFin ⟨P, hP⟩)).val).geometry.source : Set M)
  rw [Equiv.symm_apply_apply]
  exact hx

end SGPT.PSH.HermitianGlobalProducts
