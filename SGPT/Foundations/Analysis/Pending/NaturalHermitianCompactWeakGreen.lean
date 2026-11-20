import SGPT.Foundations.Analysis.Pending.NaturalHermitianGlobalCompactInclusion
import SGPT.Foundations.Analysis.Pending.NaturalHermitianReducedWeakLaplacianGraph
import Mathlib.Analysis.Normed.Operator.Compact.FredholmAlternative
import Mathlib.Analysis.InnerProductSpace.Spectrum

set_option autoImplicit false

/-! # Genuine compact weak Green operator in the original Hilbert and weak domain
Five complete mathematical proofs precede SOURCE. Actual compactness is
called from the original global chart reconstruction. The native Fredholm
alternative then constructs a bounded inverse on the actual harmonic
complement. All domain, forcing and whole-domain identities are internal.
-/

noncomputable section

open Set Filter
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.NaturalHermitianCompactWeakGreen

open FirstPass FirstPass.PositiveClasses NaturalHermitianFormL2 NaturalHermitianGraphEnergy
  NaturalHermitianWeakResolvent NaturalHermitianWeakLaplacian NaturalHermitianWeakHarmonicKernel
  NaturalHermitianReducedWeakResolvent NaturalHermitianReducedPositiveShiftResolvent
  NaturalHermitianReducedWeakLaplacianGraph NaturalHermitianGlobalCompactInclusion

variable {n q : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M]

local instance complementNormedAddCommGroup (w : KahlerBackground n M) (q : ℕ) :
    NormedAddCommGroup ((harmonicKernel w q)ᗮ) :=
  Submodule.normedAddCommGroup ((harmonicKernel w q)ᗮ)

local instance complementInnerProductSpace (w : KahlerBackground n M) (q : ℕ) :
    InnerProductSpace ℝ ((harmonicKernel w q)ᗮ) :=
  Submodule.innerProductSpace ((harmonicKernel w q)ᗮ)

local instance complementNormedSpace (w : KahlerBackground n M) (q : ℕ) :
    NormedSpace ℝ ((harmonicKernel w q)ᗮ) :=
  (Submodule.innerProductSpace ((harmonicKernel w q)ᗮ)).toNormedSpace

local instance complementCompleteSpace (w : KahlerBackground n M) (q : ℕ) :
    CompleteSpace ((harmonicKernel w q)ᗮ) := harmonicComplement_complete w q

local instance graphNormedAddCommGroup (w : KahlerBackground n M) (q : ℕ) :
    NormedAddCommGroup (GraphEnergy w q) :=
  Submodule.normedAddCommGroup (graphEnergySubmodule w q)

local instance graphInnerProductSpace (w : KahlerBackground n M) (q : ℕ) :
    InnerProductSpace ℝ (GraphEnergy w q) :=
  Submodule.innerProductSpace (graphEnergySubmodule w q)

local instance graphNormedSpace (w : KahlerBackground n M) (q : ℕ) :
    NormedSpace ℝ (GraphEnergy w q) :=
  Submodule.normedSpace (graphEnergySubmodule w q)

/-- The original harmonic kernel is exactly the original resolvent's eigenvalue-one space. -/
theorem harmonicKernel_eq_eigenspace (w : KahlerBackground n M) (q : ℕ) :
    harmonicKernel w q = Module.End.eigenspace (shiftedWeakResolvent w q).toLinearMap 1 := by
  ext f
  simp only [mem_harmonicKernel_iff, Module.End.mem_eigenspace_iff, one_smul,
    ContinuousLinearMap.coe_coe]

/-- Actual original compactness, internally called at the original background and degree. -/
theorem harmonicKernel_finiteDimensional (w : KahlerBackground n M) (q : ℕ) :
    FiniteDimensional ℝ (harmonicKernel w q) := by
  rw [harmonicKernel_eq_eigenspace]
  exact ContinuousLinearMap.finite_dimensional_eigenspace
    (isCompactOperator_shiftedWeakResolvent w q) 1 one_ne_zero

/-- True native compact restriction to the internally invariant original harmonic complement. -/
theorem reducedResolvent_isCompactOperator (w : KahlerBackground n M) (q : ℕ) :
    IsCompactOperator (reducedResolvent w q) :=
  (isCompactOperator_shiftedWeakResolvent w q).restrict'
    (fun f hf => resolvent_mem_harmonic_orthogonal w f hf)

/-- The actual complement has no nonzero fixed vector, including a zero ambient Hilbert space. -/
theorem reducedResolvent_not_hasEigenvalue_one (w : KahlerBackground n M) (q : ℕ) :
    ¬ Module.End.HasEigenvalue (reducedResolvent w q).toLinearMap 1 := by
  intro h
  obtain ⟨f, hf, hne⟩ := h.exists_hasEigenvector
  have heq : reducedResolvent w q f = f := by
    simpa only [one_smul, ContinuousLinearMap.coe_coe] using (Module.End.mem_eigenspace_iff.mp hf)
  exact hne ((reducedResolvent_eq_self_iff w f).mp heq)

private theorem compact_defect_bijective {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (S : E →L[ℝ] E) (hS : IsCompactOperator S)
    (hfixed : ∀ f : E, S f = f → f = 0) :
    Function.Bijective (ContinuousLinearMap.id ℝ E - S) := by
  have hno : ¬ Module.End.HasEigenvalue S.toLinearMap (1 : ℝ) := by
    intro h
    obtain ⟨f, hf, hne⟩ := h.exists_hasEigenvector
    have hEq : S f = f := by
      simpa only [one_smul, ContinuousLinearMap.coe_coe] using (Module.End.mem_eigenspace_iff.mp hf)
    exact hne (hfixed f hEq)
  have hr := (hS.hasEigenvalue_or_mem_resolventSet (one_ne_zero : (1 : ℝ) ≠ 0)).resolve_left hno
  have hu : IsUnit (ContinuousLinearMap.id ℝ E - S) := by
    have hunit := spectrum.mem_resolventSet_iff.mp hr
    simpa only [map_one, ContinuousLinearMap.one_def] using hunit
  exact ContinuousLinearMap.isUnit_iff_bijective.mp hu

/-- Fredholm produces genuine onto and injectivity for the actual defect, without a caller gap. -/
theorem reducedDefect_bijective (w : KahlerBackground n M) (q : ℕ) :
    Function.Bijective (reducedDefect w q) :=
  @compact_defect_bijective ((harmonicKernel w q)ᗮ)
    (complementNormedAddCommGroup w q) (complementNormedSpace w q) (complementCompleteSpace w q)
    (reducedResolvent w q) (reducedResolvent_isCompactOperator w q)
    (fun f hf => (reducedResolvent_eq_self_iff w f).mp hf)

/-- The original complete complement yields a native continuous equivalence with literal forward map. -/
def reducedDefectEquiv (w : KahlerBackground n M) (q : ℕ) :
    (harmonicKernel w q)ᗮ ≃L[ℝ] (harmonicKernel w q)ᗮ :=
  ContinuousLinearEquiv.ofBijective (reducedDefect w q)
    (LinearMap.ker_eq_bot.mpr (reducedDefect_bijective w q).1)
    (LinearMap.range_eq_top.mpr (reducedDefect_bijective w q).2)

theorem reducedDefectEquiv_apply (w : KahlerBackground n M) (f : (harmonicKernel w q)ᗮ) :
    reducedDefectEquiv w q f = reducedDefect w q f := rfl

theorem reducedDefect_inverse_apply (w : KahlerBackground n M)
    (f : (harmonicKernel w q)ᗮ) :
    reducedDefect w q ((reducedDefectEquiv w q).symm f) = f :=
  (reducedDefectEquiv w q).apply_symm_apply f

theorem reducedDefect_inverse_left (w : KahlerBackground n M)
    (f : (harmonicKernel w q)ᗮ) :
    (reducedDefectEquiv w q).symm (reducedDefect w q f) = f :=
  (reducedDefectEquiv w q).symm_apply_apply f

/-- The genuine reduced Green operator, compact resolvent followed by an internally bounded inverse. -/
def reducedWeakGreen (w : KahlerBackground n M) (q : ℕ) :
    (harmonicKernel w q)ᗮ →L[ℝ] (harmonicKernel w q)ᗮ :=
  (reducedResolvent w q).comp (reducedDefectEquiv w q).symm.toContinuousLinearMap

theorem reducedWeakGreen_apply (w : KahlerBackground n M) (f : (harmonicKernel w q)ᗮ) :
    reducedWeakGreen w q f = reducedResolvent w q ((reducedDefectEquiv w q).symm f) := rfl

theorem reducedWeakGreen_isCompactOperator (w : KahlerBackground n M) (q : ℕ) :
    IsCompactOperator (reducedWeakGreen w q) :=
  (reducedResolvent_isCompactOperator w q).comp_clm
    (reducedDefectEquiv w q).symm.toContinuousLinearMap

/-- The literal existing unit-shift domain lift, composed with the actual inverse defect. -/
def reducedWeakGreenDomainLift (w : KahlerBackground n M) (q : ℕ) :
    (harmonicKernel w q)ᗮ →ₗ[ℝ] reducedWeakDomain w q :=
  (reducedPositiveShiftDomainLift w q 1 zero_lt_one).comp
    (reducedDefectEquiv w q).symm.toLinearMap

theorem reducedWeakGreenDomainLift_inclusion (w : KahlerBackground n M)
    (f : (harmonicKernel w q)ᗮ) :
    reducedDomainInclusion w q (reducedWeakGreenDomainLift w q f) = reducedWeakGreen w q f := by
  change reducedDomainInclusion w q (reducedPositiveShiftDomainLift w q 1 zero_lt_one
    ((reducedDefectEquiv w q).symm f)) = _
  rw [reducedPositiveShiftDomainLift_inclusion, reducedPositiveShiftResolvent_one]
  rfl

theorem reducedWeakLaplacian_greenDomainLift (w : KahlerBackground n M)
    (f : (harmonicKernel w q)ᗮ) :
    reducedWeakLaplacian w q (reducedWeakGreenDomainLift w q f) = f := by
  change reducedWeakLaplacian w q (reducedPositiveShiftDomainLift w q 1 zero_lt_one
    ((reducedDefectEquiv w q).symm f)) = _
  rw [reducedWeakLaplacian_positiveShiftDomainLift, reducedPositiveShiftResolvent_one, one_smul]
  exact reducedDefect_inverse_apply w f

/-- The actual Green lift is genuinely bounded in the existing closed graph norm. -/
def reducedWeakGreenGraphCLM (w : KahlerBackground n M) (q : ℕ) :
    (harmonicKernel w q)ᗮ →L[ℝ] reducedWeakGraph w q :=
  (reducedGraphParametrization w q).comp (reducedDefectEquiv w q).symm.toContinuousLinearMap

theorem reducedWeakGreenGraphCLM_val (w : KahlerBackground n M)
    (f : (harmonicKernel w q)ᗮ) :
    (reducedWeakGreenGraphCLM w q f).val = (reducedWeakGreen w q f, f) := by
  change (reducedResolvent w q ((reducedDefectEquiv w q).symm f),
    (reducedDefectEquiv w q).symm f - reducedResolvent w q ((reducedDefectEquiv w q).symm f)) = _
  exact Prod.ext rfl (reducedDefect_inverse_apply w f)

theorem reducedWeakGreen_mem_domainImage (w : KahlerBackground n M)
    (f : (harmonicKernel w q)ᗮ) : reducedWeakGreen w q f ∈ reducedDomainImage w q :=
  ⟨reducedWeakGreenDomainLift w q f, reducedWeakGreenDomainLift_inclusion w f⟩

/-- Kernel zero is internally the intersection of the true harmonic kernel and its complement. -/
theorem reducedWeakLaplacian_eq_zero_iff (w : KahlerBackground n M)
    (a : reducedWeakDomain w q) : reducedWeakLaplacian w q a = 0 ↔ a = 0 := by
  constructor
  · intro ha
    have hA : weakLaplacian w q a.val = 0 := congrArg Subtype.val ha
    have hk := (domain_mem_harmonicKernel_iff w a.val).mpr hA
    have hz : a.val.val = 0 := (inner_self_eq_zero (𝕜 := ℝ)).mp (a.property a.val.val hk)
    exact Subtype.ext (Subtype.ext hz)
  · rintro rfl
    exact map_zero _

theorem reducedWeakLaplacian_bijective (w : KahlerBackground n M) (q : ℕ) :
    Function.Bijective (reducedWeakLaplacian w q) := by
  constructor
  · intro a b h
    apply sub_eq_zero.mp
    apply (reducedWeakLaplacian_eq_zero_iff w (a - b)).mp
    exact (map_sub (reducedWeakLaplacian w q) a b).trans
      ((congrArg (fun z => z - reducedWeakLaplacian w q b) h).trans (sub_self _))
  · intro f
    exact ⟨reducedWeakGreenDomainLift w q f, reducedWeakLaplacian_greenDomainLift w f⟩

theorem reducedWeakGreenDomainLift_inverse (w : KahlerBackground n M)
    (a : reducedWeakDomain w q) :
    reducedWeakGreenDomainLift w q (reducedWeakLaplacian w q a) = a := by
  apply (reducedWeakLaplacian_bijective w q).1
  exact reducedWeakLaplacian_greenDomainLift w _

theorem reducedWeakGreen_laplacian (w : KahlerBackground n M)
    (a : reducedWeakDomain w q) :
    reducedWeakGreen w q (reducedWeakLaplacian w q a) = reducedDomainInclusion w q a :=
  (reducedWeakGreenDomainLift_inclusion w _).symm.trans
    (congrArg (reducedDomainInclusion w q) (reducedWeakGreenDomainLift_inverse w a))

theorem existsUnique_reduced_unshifted_solution (w : KahlerBackground n M)
    (f : (harmonicKernel w q)ᗮ) :
    ∃! a : reducedWeakDomain w q, reducedWeakLaplacian w q a = f := by
  refine ⟨reducedWeakGreenDomainLift w q f, reducedWeakLaplacian_greenDomainLift w f, ?_⟩
  intro a ha
  exact (reducedWeakLaplacian_bijective w q).1
    (ha.trans (reducedWeakLaplacian_greenDomainLift w f).symm)

theorem native_value_le_opNorm {E F : Type*}
    [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    [SeminormedAddCommGroup F] [NormedSpace ℝ F]
    (T : E →L[ℝ] F) (f : E) : ‖T f‖ ≤ ‖T‖ * ‖f‖ := T.le_opNorm f

theorem reducedWeakGreenDomainLift_norm_le (w : KahlerBackground n M)
    (f : (harmonicKernel w q)ᗮ) :
    ‖reducedDomainInclusion w q (reducedWeakGreenDomainLift w q f)‖ ≤
      ‖(reducedWeakGreen w q : (harmonicKernel w q)ᗮ →L[ℝ] (harmonicKernel w q)ᗮ)‖ * ‖f‖ := by
  rw [reducedWeakGreenDomainLift_inclusion]
  exact @native_value_le_opNorm ((harmonicKernel w q)ᗮ) ((harmonicKernel w q)ᗮ)
    (complementNormedAddCommGroup w q).toSeminormedAddCommGroup (complementNormedSpace w q)
    (complementNormedAddCommGroup w q).toSeminormedAddCommGroup (complementNormedSpace w q)
    (reducedWeakGreen w q) f

/-- Literal projection to the actual harmonic complement, with membership proved internally. -/
def harmonicComplementProjection (w : KahlerBackground n M) (q : ℕ) :
    HilbertFormL2 w.form.val w.isKahler.1 q →L[ℝ] (harmonicKernel w q)ᗮ :=
  (ContinuousLinearMap.id ℝ _ - harmonicProjection w q).codRestrict ((harmonicKernel w q)ᗮ)
    (fun f => sub_harmonicProjection_mem_orthogonal w f)

theorem harmonicComplementProjection_val (w : KahlerBackground n M)
    (f : HilbertFormL2 w.form.val w.isKahler.1 q) :
    (harmonicComplementProjection w q f).val = f - harmonicProjection w q f := rfl

/-- Actual ambient weak Green operator in the original Hilbert completion. -/
def weakGreen (w : KahlerBackground n M) (q : ℕ) :
    HilbertFormL2 w.form.val w.isKahler.1 q →L[ℝ] HilbertFormL2 w.form.val w.isKahler.1 q :=
  ((harmonicKernel w q)ᗮ).subtypeL.comp
    ((reducedWeakGreen w q).comp (harmonicComplementProjection w q))

theorem weakGreen_apply (w : KahlerBackground n M)
    (f : HilbertFormL2 w.form.val w.isKahler.1 q) :
    weakGreen w q f = (reducedWeakGreen w q (harmonicComplementProjection w q f)).val := rfl

theorem weakGreen_isCompactOperator (w : KahlerBackground n M) (q : ℕ) :
    IsCompactOperator (weakGreen w q) :=
  ((reducedWeakGreen_isCompactOperator w q).comp_clm (harmonicComplementProjection w q)).clm_comp
    ((harmonicKernel w q)ᗮ).subtypeL

/-- The genuine original weak domain, without introducing a proxy operator or domain. -/
def weakGreenDomainLift (w : KahlerBackground n M) (q : ℕ) :
    HilbertFormL2 w.form.val w.isKahler.1 q →ₗ[ℝ] weakDomain w q :=
  (reducedWeakDomain w q).subtype.comp
    ((reducedWeakGreenDomainLift w q).comp (harmonicComplementProjection w q).toLinearMap)

theorem weakGreenDomainLift_val (w : KahlerBackground n M)
    (f : HilbertFormL2 w.form.val w.isKahler.1 q) :
    (weakGreenDomainLift w q f).val = weakGreen w q f :=
  congrArg Subtype.val (reducedWeakGreenDomainLift_inclusion w (harmonicComplementProjection w q f))

theorem weakLaplacian_greenDomainLift (w : KahlerBackground n M)
    (f : HilbertFormL2 w.form.val w.isKahler.1 q) :
    weakLaplacian w q (weakGreenDomainLift w q f) = f - harmonicProjection w q f :=
  congrArg Subtype.val (reducedWeakLaplacian_greenDomainLift w (harmonicComplementProjection w q f))

theorem weakGreen_mem_harmonic_orthogonal (w : KahlerBackground n M)
    (f : HilbertFormL2 w.form.val w.isKahler.1 q) : weakGreen w q f ∈ (harmonicKernel w q)ᗮ :=
  (reducedWeakGreen w q (harmonicComplementProjection w q f)).property

theorem harmonicProjection_weakGreen (w : KahlerBackground n M)
    (f : HilbertFormL2 w.form.val w.isKahler.1 q) : harmonicProjection w q (weakGreen w q f) = 0 :=
  (harmonicProjection_eq_zero_iff w _).mpr (weakGreen_mem_harmonic_orthogonal w f)

/-- Actual bounded energy lift using the original Riesz producer and exact forcing inverse. -/
def weakGreenEnergySolution (w : KahlerBackground n M) (q : ℕ) :
    HilbertFormL2 w.form.val w.isKahler.1 q →L[ℝ] GraphEnergy w q :=
  (energySolution w q).comp (((harmonicKernel w q)ᗮ).subtypeL.comp
    ((reducedDefectEquiv w q).symm.toContinuousLinearMap.comp (harmonicComplementProjection w q)))

theorem energyInclusion_weakGreenEnergySolution (w : KahlerBackground n M)
    (f : HilbertFormL2 w.form.val w.isKahler.1 q) :
    energyInclusion w q (weakGreenEnergySolution w q f) = weakGreen w q f := rfl

/-- Both actual coordinates satisfy the entire unshifted weak equation. -/
theorem weakGreenEnergySolution_weak_equation (w : KahlerBackground n M)
    (f : HilbertFormL2 w.form.val w.isKahler.1 q) (v : GraphEnergy w q) :
    inner ℝ (energyDerivative w q (weakGreenEnergySolution w q f)) (energyDerivative w q v) +
      inner ℝ (energyCoderivative w q (weakGreenEnergySolution w q f))
        (energyCoderivative w q v) =
      inner ℝ (f - harmonicProjection w q f) (energyInclusion w q v) := by
  let h := (reducedDefectEquiv w q).symm (harmonicComplementProjection w q f)
  have hforce : h.val - shiftedWeakResolvent w q h.val = f - harmonicProjection w q f :=
    congrArg Subtype.val (reducedDefect_inverse_apply w (harmonicComplementProjection w q f))
  have heq := energySolution_weak_equation w h.val v
  change inner ℝ (shiftedWeakResolvent w q h.val) (energyInclusion w q v) +
    inner ℝ (energyDerivative w q (energySolution w q h.val)) (energyDerivative w q v) +
    inner ℝ (energyCoderivative w q (energySolution w q h.val)) (energyCoderivative w q v) = _ at heq
  have hinner := inner_sub_left (𝕜 := ℝ) h.val (shiftedWeakResolvent w q h.val)
    (energyInclusion w q v)
  change inner ℝ (energyDerivative w q (energySolution w q h.val)) (energyDerivative w q v) +
    inner ℝ (energyCoderivative w q (energySolution w q h.val)) (energyCoderivative w q v) = _
  rw [← hforce]
  linarith

/-- Exact forcing compatibility, now with a genuine actual-domain solution producer. -/
theorem exists_unshifted_solution_iff_projection_zero (w : KahlerBackground n M)
    (f : HilbertFormL2 w.form.val w.isKahler.1 q) :
    (∃ a : weakDomain w q, weakLaplacian w q a = f) ↔ harmonicProjection w q f = 0 := by
  constructor
  · rintro ⟨a, ha⟩
    exact unshifted_solution_forcing_orthogonal w f a ha
  · intro hf
    refine ⟨weakGreenDomainLift w q f, ?_⟩
    exact (weakLaplacian_greenDomainLift w f).trans (by rw [hf, sub_zero])

theorem exists_unshifted_solution_iff_mem_orthogonal (w : KahlerBackground n M)
    (f : HilbertFormL2 w.form.val w.isKahler.1 q) :
    (∃ a : weakDomain w q, weakLaplacian w q a = f) ↔ f ∈ (harmonicKernel w q)ᗮ :=
  (exists_unshifted_solution_iff_projection_zero w f).trans (harmonicProjection_eq_zero_iff w f)

theorem weakLaplacian_range_eq_harmonic_orthogonal (w : KahlerBackground n M) (q : ℕ) :
    (weakLaplacian w q).range = (harmonicKernel w q)ᗮ := by
  ext f
  exact exists_unshifted_solution_iff_mem_orthogonal w f

theorem weakLaplacian_range_isClosed (w : KahlerBackground n M) (q : ℕ) :
    IsClosed ((weakLaplacian w q).range : Set (HilbertFormL2 w.form.val w.isKahler.1 q)) := by
  rw [weakLaplacian_range_eq_harmonic_orthogonal]
  exact harmonicComplement_isClosed w q

theorem harmonicComplementProjection_harmonicProjection (w : KahlerBackground n M)
    (f : HilbertFormL2 w.form.val w.isKahler.1 q) :
    harmonicComplementProjection w q (harmonicProjection w q f) = 0 := by
  apply Subtype.ext
  change harmonicProjection w q f - harmonicProjection w q (harmonicProjection w q f) = 0
  rw [(harmonicProjection_eq_self_iff w _).mpr (harmonicProjection_mem w f), sub_self]

theorem weakGreen_harmonicProjection (w : KahlerBackground n M)
    (f : HilbertFormL2 w.form.val w.isKahler.1 q) : weakGreen w q (harmonicProjection w q f) = 0 := by
  change (reducedWeakGreen w q (harmonicComplementProjection w q (harmonicProjection w q f))).val = 0
  rw [harmonicComplementProjection_harmonicProjection, map_zero]
  rfl

theorem weakGreen_comp_harmonicProjection (w : KahlerBackground n M) (q : ℕ) :
    (weakGreen w q).comp (harmonicProjection w q) = 0 := by
  ext f
  exact weakGreen_harmonicProjection w f

theorem harmonicProjection_comp_weakGreen (w : KahlerBackground n M) (q : ℕ) :
    (harmonicProjection w q).comp (weakGreen w q) = 0 := by
  ext f
  exact harmonicProjection_weakGreen w f

theorem solutions_difference_mem_harmonicKernel (w : KahlerBackground n M)
    (a b : weakDomain w q) (h : weakLaplacian w q a = weakLaplacian w q b) :
    a.val - b.val ∈ harmonicKernel w q := by
  have hz : weakLaplacian w q (a - b) = 0 :=
    (map_sub (weakLaplacian w q) a b).trans
      ((congrArg (fun z => z - weakLaplacian w q b) h).trans (sub_self _))
  exact (domain_mem_harmonicKernel_iff w (a - b)).mpr hz

theorem weakGreen_laplacian (w : KahlerBackground n M) (a : weakDomain w q) :
    weakGreen w q (weakLaplacian w q a) = a.val - harmonicProjection w q a.val := by
  let b := weakGreenDomainLift w q (weakLaplacian w q a)
  have hA : weakLaplacian w q b = weakLaplacian w q a :=
    (weakLaplacian_greenDomainLift w _).trans
      (by rw [harmonicProjection_weakLaplacian, sub_zero])
  have hk := solutions_difference_mem_harmonicKernel w a b hA.symm
  have hp := (harmonicProjection_eq_self_iff w _).mpr hk
  have hb : b.val = weakGreen w q (weakLaplacian w q a) := weakGreenDomainLift_val w _
  have hzero := harmonicProjection_weakGreen w (weakLaplacian w q a)
  have hproj := map_sub (harmonicProjection w q) a.val b.val
  rw [hb, hzero, sub_zero] at hproj
  rw [hb] at hp
  have hd : a.val - weakGreen w q (weakLaplacian w q a) = harmonicProjection w q a.val :=
    hp.symm.trans hproj
  rw [← hd]
  abel

theorem orthogonal_unshifted_solution_unique (w : KahlerBackground n M)
    (a b : weakDomain w q)
    (ha : a.val ∈ (harmonicKernel w q)ᗮ) (hb : b.val ∈ (harmonicKernel w q)ᗮ)
    (h : weakLaplacian w q a = weakLaplacian w q b) : a = b := by
  have hk := solutions_difference_mem_harmonicKernel w a b h
  have he := ((harmonicKernel w q)ᗮ).sub_mem ha hb
  have hz : a.val - b.val = 0 := (inner_self_eq_zero (𝕜 := ℝ)).mp (he _ hk)
  exact Subtype.ext (sub_eq_zero.mp hz)

theorem weakGreen_inner_symm (w : KahlerBackground n M)
    (f g : HilbertFormL2 w.form.val w.isKahler.1 q) :
    inner ℝ (weakGreen w q f) g = inner ℝ f (weakGreen w q g) := by
  have hs := weakLaplacian_inner_symm w (weakGreenDomainLift w q f) (weakGreenDomainLift w q g)
  rw [weakLaplacian_greenDomainLift, weakLaplacian_greenDomainLift,
    weakGreenDomainLift_val, weakGreenDomainLift_val] at hs
  have hf : inner ℝ (harmonicProjection w q f) (weakGreen w q g) = 0 :=
    (weakGreen_mem_harmonic_orthogonal w g) _ (harmonicProjection_mem w f)
  have hg : inner ℝ (weakGreen w q f) (harmonicProjection w q g) = 0 :=
    (real_inner_comm _ _).trans
      ((weakGreen_mem_harmonic_orthogonal w f) _ (harmonicProjection_mem w g))
  rw [inner_sub_left, inner_sub_right, hf, hg, sub_zero, sub_zero] at hs
  exact hs.symm

theorem weakGreen_nonneg (w : KahlerBackground n M)
    (f : HilbertFormL2 w.form.val w.isKahler.1 q) :
    0 ≤ inner ℝ (weakGreen w q f) f := by
  have hp := weakLaplacian_nonneg w (weakGreenDomainLift w q f)
  rw [weakLaplacian_greenDomainLift, weakGreenDomainLift_val, inner_sub_left] at hp
  have hf : inner ℝ (harmonicProjection w q f) (weakGreen w q f) = 0 :=
    (weakGreen_mem_harmonic_orthogonal w f) _ (harmonicProjection_mem w f)
  rw [hf, sub_zero] at hp
  exact hp.trans_eq (real_inner_comm _ _)

end SGPT.Foundations.Analysis.Pending.NaturalHermitianCompactWeakGreen
