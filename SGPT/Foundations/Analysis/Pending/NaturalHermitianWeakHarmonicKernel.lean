import SGPT.Foundations.Analysis.Pending.NaturalHermitianWeakLaplacian
import Mathlib.Analysis.InnerProductSpace.Projection.Basic

set_option autoImplicit false

/-! # The actual weak harmonic subspace of the original form Hilbert space
Five complete mathematical proofs precede SOURCE. The actual resolvent
internally constructs the closed harmonic kernel, native orthogonal projection
and original smooth geometric readbacks. No finite-dimensionality,
unshifted Green, Rellich or regularity certificate occurs.
-/

noncomputable section

open Set Filter
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.NaturalHermitianWeakHarmonicKernel

open FirstPass FirstPass.PositiveClasses NaturalHermitianFormL2
  NaturalHermitianGraphEnergy NaturalHermitianWeakResolvent
  NaturalHermitianWeakLaplacian NaturalHermitianCodifferential
  NaturalHermitianHodgeLaplacian

variable {n q : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M]

local instance (w : KahlerBackground n M) (q : ℕ) : NormedAddCommGroup (GraphEnergy w q) :=
  Submodule.normedAddCommGroup (graphEnergySubmodule w q)

local instance (w : KahlerBackground n M) (q : ℕ) : InnerProductSpace ℝ (GraphEnergy w q) :=
  Submodule.innerProductSpace (graphEnergySubmodule w q)

local instance (w : KahlerBackground n M) (q : ℕ) : CompleteSpace (GraphEnergy w q) :=
  graphEnergy_complete w q

/-- The literal fixed-point kernel of the actual shifted weak resolvent. -/
def harmonicKernel (w : KahlerBackground n M) (q : ℕ) :
    Submodule ℝ (HilbertFormL2 w.form.val w.isKahler.1 q) :=
  (shiftedWeakResolvent w q - ContinuousLinearMap.id ℝ _).ker

theorem mem_harmonicKernel_iff (w : KahlerBackground n M)
    (f : HilbertFormL2 w.form.val w.isKahler.1 q) :
    f ∈ harmonicKernel w q ↔ shiftedWeakResolvent w q f = f := by
  change shiftedWeakResolvent w q f - f = 0 ↔ _
  exact sub_eq_zero

theorem harmonicKernel_isClosed (w : KahlerBackground n M) (q : ℕ) :
    IsClosed (harmonicKernel w q : Set (HilbertFormL2 w.form.val w.isKahler.1 q)) :=
  (shiftedWeakResolvent w q - ContinuousLinearMap.id ℝ _).isClosed_ker

theorem harmonicKernel_complete (w : KahlerBackground n M) (q : ℕ) :
    CompleteSpace (harmonicKernel w q) :=
  ContinuousLinearMap.completeSpace_ker
    (shiftedWeakResolvent w q - ContinuousLinearMap.id ℝ _)

theorem mem_harmonicKernel_iff_zero_graph (w : KahlerBackground n M)
    (f : HilbertFormL2 w.form.val w.isKahler.1 q) :
    f ∈ harmonicKernel w q ↔ (f, 0) ∈ weakGraph w q := by
  rw [mem_harmonicKernel_iff, mem_weakGraph_iff, add_zero]
  exact eq_comm

theorem mem_harmonicKernel_iff_domain_zero (w : KahlerBackground n M)
    (f : HilbertFormL2 w.form.val w.isKahler.1 q) :
    f ∈ harmonicKernel w q ↔ ∃ a : weakDomain w q,
      a.val = f ∧ weakLaplacian w q a = 0 :=
  (mem_harmonicKernel_iff_zero_graph w f).trans (mem_weakGraph_iff_domain w f 0)

/-- Actual harmonicity is precisely simultaneous vanishing of the two weak coordinates. -/
theorem mem_harmonicKernel_iff_zero_coordinates (w : KahlerBackground n M)
    (f : HilbertFormL2 w.form.val w.isKahler.1 q) :
    f ∈ harmonicKernel w q ↔ ∃ u : GraphEnergy w q,
      energyInclusion w q u = f ∧ energyDerivative w q u = 0 ∧
        energyCoderivative w q u = 0 := by
  constructor
  · intro hf
    obtain ⟨u, hi, hu⟩ := (mem_weakGraph_iff_weak_equation w f 0).mp
      ((mem_harmonicKernel_iff_zero_graph w f).mp hf)
    have hs : ‖energyDerivative w q u‖ ^ 2 + ‖energyCoderivative w q u‖ ^ 2 = 0 :=
      (congrArg₂ (fun a b : ℝ => a + b)
        (real_inner_self_eq_norm_sq (energyDerivative w q u))
        (real_inner_self_eq_norm_sq (energyCoderivative w q u))).symm.trans
        ((hu u).trans (inner_zero_left (energyInclusion w q u)))
    have hd : ‖energyDerivative w q u‖ = 0 := by
      nlinarith [sq_nonneg ‖energyCoderivative w q u‖]
    have hc : ‖energyCoderivative w q u‖ = 0 := by
      nlinarith [sq_nonneg ‖energyDerivative w q u‖]
    exact ⟨u, hi, norm_eq_zero.mp hd, norm_eq_zero.mp hc⟩
  · rintro ⟨u, hi, hd, hc⟩
    apply (mem_harmonicKernel_iff_zero_graph w f).mpr
    apply (mem_weakGraph_iff_weak_equation w f 0).mpr
    refine ⟨u, hi, ?_⟩
    intro v
    calc
      inner ℝ (energyDerivative w q u) (energyDerivative w q v) +
          inner ℝ (energyCoderivative w q u) (energyCoderivative w q v) = 0 + 0 :=
        congrArg₂ (fun a b : ℝ => a + b)
          ((congrArg (fun a => inner ℝ a (energyDerivative w q v)) hd).trans
            (inner_zero_left _))
          ((congrArg (fun a => inner ℝ a (energyCoderivative w q v)) hc).trans
            (inner_zero_left _))
      _ = 0 := zero_add 0
      _ = inner ℝ 0 (energyInclusion w q v) := (inner_zero_left _).symm

theorem energyInclusion_mem_harmonicKernel_iff (w : KahlerBackground n M)
    (u : GraphEnergy w q) :
    energyInclusion w q u ∈ harmonicKernel w q ↔
      energyDerivative w q u = 0 ∧ energyCoderivative w q u = 0 := by
  constructor
  · intro h
    obtain ⟨v, hi, hd, hc⟩ := (mem_harmonicKernel_iff_zero_coordinates w _).mp h
    have hv : v = u := energyInclusion_injective w q hi
    exact hv ▸ ⟨hd, hc⟩
  · rintro ⟨hd, hc⟩
    exact (mem_harmonicKernel_iff_zero_coordinates w _).mpr ⟨u, rfl, hd, hc⟩

theorem domain_mem_harmonicKernel_iff (w : KahlerBackground n M) (a : weakDomain w q) :
    a.val ∈ harmonicKernel w q ↔ weakLaplacian w q a = 0 := by
  constructor
  · intro h
    obtain ⟨b, hb, hz⟩ := (mem_harmonicKernel_iff_domain_zero w a.val).mp h
    have heq : b = a := Subtype.ext hb
    exact (congrArg (weakLaplacian w q) heq).symm.trans hz
  · intro hz
    exact (mem_harmonicKernel_iff_domain_zero w a.val).mpr ⟨a, rfl, hz⟩

local instance (w : KahlerBackground n M) (q : ℕ) : CompleteSpace (harmonicKernel w q) :=
  harmonicKernel_complete w q

/-- The genuine native projection, constructed using the internally complete actual kernel. -/
def harmonicProjection (w : KahlerBackground n M) (q : ℕ) :
    HilbertFormL2 w.form.val w.isKahler.1 q →L[ℝ]
      HilbertFormL2 w.form.val w.isKahler.1 q :=
  (harmonicKernel w q).starProjection

theorem harmonicProjection_mem (w : KahlerBackground n M)
    (f : HilbertFormL2 w.form.val w.isKahler.1 q) :
    harmonicProjection w q f ∈ harmonicKernel w q :=
  (harmonicKernel w q).starProjection_apply_mem f

theorem sub_harmonicProjection_mem_orthogonal (w : KahlerBackground n M)
    (f : HilbertFormL2 w.form.val w.isKahler.1 q) :
    f - harmonicProjection w q f ∈ (harmonicKernel w q)ᗮ :=
  Submodule.sub_starProjection_mem_orthogonal (K := harmonicKernel w q) f

theorem harmonicProjection_eq_self_iff (w : KahlerBackground n M)
    (f : HilbertFormL2 w.form.val w.isKahler.1 q) :
    harmonicProjection w q f = f ↔ f ∈ harmonicKernel w q :=
  Submodule.starProjection_eq_self_iff

theorem harmonicProjection_eq_zero_iff (w : KahlerBackground n M)
    (f : HilbertFormL2 w.form.val w.isKahler.1 q) :
    harmonicProjection w q f = 0 ↔ f ∈ (harmonicKernel w q)ᗮ :=
  Submodule.starProjection_apply_eq_zero_iff (harmonicKernel w q)

theorem harmonicProjection_comp_self (w : KahlerBackground n M) (q : ℕ) :
    (harmonicProjection w q).comp (harmonicProjection w q) = harmonicProjection w q := by
  ext f
  exact (harmonicProjection_eq_self_iff w _).mpr (harmonicProjection_mem w f)

theorem harmonicProjection_range (w : KahlerBackground n M) (q : ℕ) :
    (harmonicProjection w q).range = harmonicKernel w q :=
  Submodule.range_starProjection (harmonicKernel w q)

theorem harmonicProjection_ker (w : KahlerBackground n M) (q : ℕ) :
    (harmonicProjection w q).ker = (harmonicKernel w q)ᗮ :=
  Submodule.ker_starProjection (harmonicKernel w q)

theorem harmonicProjection_norm_le (w : KahlerBackground n M) (q : ℕ) :
    ‖harmonicProjection w q‖ ≤ 1 :=
  (harmonicKernel w q).starProjection_norm_le

theorem harmonicProjection_apply_norm_le (w : KahlerBackground n M)
    (f : HilbertFormL2 w.form.val w.isKahler.1 q) :
    ‖harmonicProjection w q f‖ ≤ ‖f‖ :=
  (harmonicKernel w q).norm_starProjection_apply_le f

theorem harmonicProjection_inner_symm (w : KahlerBackground n M)
    (f g : HilbertFormL2 w.form.val w.isKahler.1 q) :
    inner ℝ (harmonicProjection w q f) g = inner ℝ f (harmonicProjection w q g) :=
  Submodule.inner_starProjection_left_eq_right (harmonicKernel w q) f g

theorem resolvent_harmonicProjection (w : KahlerBackground n M)
    (f : HilbertFormL2 w.form.val w.isKahler.1 q) :
    shiftedWeakResolvent w q (harmonicProjection w q f) = harmonicProjection w q f :=
  (mem_harmonicKernel_iff w _).mp (harmonicProjection_mem w f)

theorem resolvent_mem_harmonic_orthogonal (w : KahlerBackground n M)
    (f : HilbertFormL2 w.form.val w.isKahler.1 q)
    (hf : f ∈ (harmonicKernel w q)ᗮ) :
    shiftedWeakResolvent w q f ∈ (harmonicKernel w q)ᗮ := by
  intro h hh
  have hr := (mem_harmonicKernel_iff w h).mp hh
  exact (shiftedWeakResolvent_inner_symm w h f).symm.trans
    ((congrArg (fun a => inner ℝ a f) hr).trans (hf h hh))

theorem harmonicProjection_resolvent (w : KahlerBackground n M)
    (f : HilbertFormL2 w.form.val w.isKahler.1 q) :
    harmonicProjection w q (shiftedWeakResolvent w q f) = harmonicProjection w q f := by
  have hp := harmonicProjection_mem w f
  have hr := resolvent_mem_harmonic_orthogonal w
    (f - harmonicProjection w q f) (sub_harmonicProjection_mem_orthogonal w f)
  have heq : shiftedWeakResolvent w q (f - harmonicProjection w q f) =
      shiftedWeakResolvent w q f - harmonicProjection w q f :=
    (map_sub (shiftedWeakResolvent w q) f (harmonicProjection w q f)).trans
      (congrArg (fun a => shiftedWeakResolvent w q f - a) (resolvent_harmonicProjection w f))
  exact Submodule.eq_starProjection_of_mem_orthogonal hp (heq ▸ hr)

theorem resolvent_comp_harmonicProjection (w : KahlerBackground n M) (q : ℕ) :
    (shiftedWeakResolvent w q).comp (harmonicProjection w q) = harmonicProjection w q := by
  ext f
  exact resolvent_harmonicProjection w f

theorem harmonicProjection_comp_resolvent (w : KahlerBackground n M) (q : ℕ) :
    (harmonicProjection w q).comp (shiftedWeakResolvent w q) = harmonicProjection w q := by
  ext f
  exact harmonicProjection_resolvent w f

/-- Genuine orthogonality of every actual unshifted weak Laplacian value. -/
theorem weakLaplacian_mem_harmonic_orthogonal (w : KahlerBackground n M)
    (a : weakDomain w q) :
    weakLaplacian w q a ∈ (harmonicKernel w q)ᗮ := by
  intro h hh
  obtain ⟨b, hb, hz⟩ := (mem_harmonicKernel_iff_domain_zero w h).mp hh
  calc
    inner ℝ h (weakLaplacian w q a) = inner ℝ b.val (weakLaplacian w q a) :=
      congrArg (fun t => inner ℝ t (weakLaplacian w q a)) hb.symm
    _ = inner ℝ (weakLaplacian w q b) a.val := (weakLaplacian_inner_symm w b a).symm
    _ = 0 := (congrArg (fun t => inner ℝ t a.val) hz).trans (inner_zero_left _)

theorem harmonicProjection_weakLaplacian (w : KahlerBackground n M)
    (a : weakDomain w q) :
    harmonicProjection w q (weakLaplacian w q a) = 0 :=
  (harmonicProjection_eq_zero_iff w _).mpr (weakLaplacian_mem_harmonic_orthogonal w a)

theorem unshifted_solution_forcing_orthogonal (w : KahlerBackground n M)
    (f : HilbertFormL2 w.form.val w.isKahler.1 q)
    (a : weakDomain w q) (ha : weakLaplacian w q a = f) :
    harmonicProjection w q f = 0 :=
  (congrArg (harmonicProjection w q) ha).symm.trans (harmonicProjection_weakLaplacian w a)

private theorem original_image_eq_zero_iff (w : KahlerBackground n M)
    {p : ℕ} (α : SmoothRealForm n M p) :
    toHilbertFormL2 w.form.val w.isKahler.1 α = 0 ↔ α.GeometricallyEq 0 := by
  have hz : toHilbertFormL2 w.form.val w.isKahler.1 (0 : SmoothRealForm n M p) = 0 :=
    (toHilbertFormL2Linear w.form.val w.isKahler.1 p).map_zero
  exact (Iff.of_eq (congrArg (fun z => toHilbertFormL2 w.form.val w.isKahler.1 α = z)
    hz.symm)).trans (toHilbertFormL2_eq_iff w.form.val w.isKahler.1 α 0)

/-- Exact original smooth geometric Laplacian zero readback, including all degrees. -/
theorem original_smooth_mem_harmonicKernel_iff_laplacian (w : KahlerBackground n M)
    (α : SmoothRealForm n M q) :
    toHilbertFormL2 w.form.val w.isKahler.1 α ∈ harmonicKernel w q ↔
      (hodgeLaplacianForm w.form.val w.isKahler.1 q α).GeometricallyEq 0 := by
  let a : weakDomain w q := ⟨toHilbertFormL2 w.form.val w.isKahler.1 α,
    original_smooth_mem_weakDomain w α⟩
  have hA : weakLaplacian w q a = toHilbertFormL2 w.form.val w.isKahler.1
      (hodgeLaplacianForm w.form.val w.isKahler.1 q α) := weakLaplacian_original_smooth w α
  exact (domain_mem_harmonicKernel_iff w a).trans
    ((Iff.of_eq (congrArg (fun t => t = 0) hA)).trans (original_image_eq_zero_iff w _))

/-- The two actual weak coordinates read back the original geometric d and delta zeros. -/
theorem original_smooth_mem_harmonicKernel_iff_coordinates (w : KahlerBackground n M)
    (α : SmoothRealForm n M q) :
    toHilbertFormL2 w.form.val w.isKahler.1 α ∈ harmonicKernel w q ↔
      α.exteriorDerivative.GeometricallyEq 0 ∧
        (coderivativeForm w.form.val w.isKahler.1 q α).GeometricallyEq 0 := by
  have h := energyInclusion_mem_harmonicKernel_iff w (smoothEnergyLinear w q α)
  have hd := original_image_eq_zero_iff w α.exteriorDerivative
  have hc := original_image_eq_zero_iff w (coderivativeForm w.form.val w.isKahler.1 q α)
  exact h.trans (and_congr hd hc)

theorem original_smooth_laplacian_zero_iff_coordinates (w : KahlerBackground n M)
    (α : SmoothRealForm n M q) :
    (hodgeLaplacianForm w.form.val w.isKahler.1 q α).GeometricallyEq 0 ↔
      α.exteriorDerivative.GeometricallyEq 0 ∧
        (coderivativeForm w.form.val w.isKahler.1 q α).GeometricallyEq 0 :=
  (original_smooth_mem_harmonicKernel_iff_laplacian w α).symm.trans
    (original_smooth_mem_harmonicKernel_iff_coordinates w α)

end SGPT.Foundations.Analysis.Pending.NaturalHermitianWeakHarmonicKernel
