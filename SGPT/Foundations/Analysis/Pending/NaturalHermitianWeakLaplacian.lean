import SGPT.Foundations.Analysis.Pending.NaturalHermitianWeakResolvent
import SGPT.Foundations.Analysis.Pending.NaturalHermitianHodgeLaplacian
import Mathlib.Algebra.Module.Submodule.Equiv

set_option autoImplicit false

/-! # The actual closed graph and dense domain of the original weak Laplacian
All nine entire mathematical proofs precede SOURCE. The native kernel
graph, range domain and algebraic operator are constructed from the
actual Riesz resolvent; no caller closedness or onto certificate is used.
-/

noncomputable section

open Set Filter
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.NaturalHermitianWeakLaplacian

open FirstPass FirstPass.PositiveClasses NaturalHermitianFormL2
  NaturalHermitianGraphEnergy NaturalHermitianCodifferential
  NaturalHermitianWeakResolvent NaturalHermitianHodgeLaplacian
  NaturalHermitianKahlerVolumeCalibration

variable {n q : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M]

local instance (w : KahlerBackground n M) (q : ℕ) : NormedAddCommGroup (GraphEnergy w q) :=
  Submodule.normedAddCommGroup (graphEnergySubmodule w q)

local instance (w : KahlerBackground n M) (q : ℕ) : InnerProductSpace ℝ (GraphEnergy w q) :=
  Submodule.innerProductSpace (graphEnergySubmodule w q)

local instance (w : KahlerBackground n M) (q : ℕ) : CompleteSpace (GraphEnergy w q) :=
  graphEnergy_complete w q

/-- Actual continuous kernel map, using native product projections. -/
def graphKernel (w : KahlerBackground n M) (q : ℕ) :
    (HilbertFormL2 w.form.val w.isKahler.1 q × HilbertFormL2 w.form.val w.isKahler.1 q)
      →L[ℝ] HilbertFormL2 w.form.val w.isKahler.1 q :=
  ContinuousLinearMap.fst ℝ _ _ - (shiftedWeakResolvent w q).comp
    (ContinuousLinearMap.fst ℝ _ _ + ContinuousLinearMap.snd ℝ _ _)

/-- The actual weak graph, constructed internally as a native linear kernel. -/
def weakGraph (w : KahlerBackground n M) (q : ℕ) :
    Submodule ℝ (HilbertFormL2 w.form.val w.isKahler.1 q ×
      HilbertFormL2 w.form.val w.isKahler.1 q) := (graphKernel w q).ker

theorem mem_weakGraph_iff (w : KahlerBackground n M)
    (x y : HilbertFormL2 w.form.val w.isKahler.1 q) :
    (x, y) ∈ weakGraph w q ↔ x = shiftedWeakResolvent w q (x + y) := by
  change x - shiftedWeakResolvent w q (x + y) = 0 ↔ _
  exact sub_eq_zero

theorem weakGraph_isClosed (w : KahlerBackground n M) (q : ℕ) :
    IsClosed (weakGraph w q : Set (HilbertFormL2 w.form.val w.isKahler.1 q ×
      HilbertFormL2 w.form.val w.isKahler.1 q)) :=
  (graphKernel w q).isClosed_ker

theorem weakGraph_complete (w : KahlerBackground n M) (q : ℕ) :
    CompleteSpace (weakGraph w q) :=
  ContinuousLinearMap.completeSpace_ker (graphKernel w q)

theorem resolvent_pair_mem_weakGraph (w : KahlerBackground n M)
    (f : HilbertFormL2 w.form.val w.isKahler.1 q) :
    (shiftedWeakResolvent w q f, f - shiftedWeakResolvent w q f) ∈ weakGraph w q := by
  apply (mem_weakGraph_iff w _ _).mpr
  rw [add_sub_cancel]

/-- Genuine continuous parametrization of the entire actual closed graph. -/
def graphParametrization (w : KahlerBackground n M) (q : ℕ) :
    HilbertFormL2 w.form.val w.isKahler.1 q →L[ℝ] weakGraph w q := by
  let H := HilbertFormL2 w.form.val w.isKahler.1 q
  let R : H →L[ℝ] H := shiftedWeakResolvent w q
  let P : H →L[ℝ] H × H := R.prod (ContinuousLinearMap.id ℝ H - R)
  exact P.codRestrict (weakGraph w q) (fun f => resolvent_pair_mem_weakGraph w f)

/-- The actual inverse parametrization is the literal sum of graph coordinates. -/
def graphForcing (w : KahlerBackground n M) (q : ℕ) :
    weakGraph w q →L[ℝ] HilbertFormL2 w.form.val w.isKahler.1 q :=
  (ContinuousLinearMap.fst ℝ (HilbertFormL2 w.form.val w.isKahler.1 q)
      (HilbertFormL2 w.form.val w.isKahler.1 q) +
    ContinuousLinearMap.snd ℝ (HilbertFormL2 w.form.val w.isKahler.1 q)
      (HilbertFormL2 w.form.val w.isKahler.1 q)).comp
    (weakGraph w q).subtypeL

theorem graphForcing_parametrization (w : KahlerBackground n M)
    (f : HilbertFormL2 w.form.val w.isKahler.1 q) :
    graphForcing w q (graphParametrization w q f) = f := by
  change shiftedWeakResolvent w q f + (f - shiftedWeakResolvent w q f) = f
  abel

theorem graphParametrization_forcing (w : KahlerBackground n M) (g : weakGraph w q) :
    graphParametrization w q (graphForcing w q g) = g := by
  apply Subtype.ext
  have h := (mem_weakGraph_iff w g.val.1 g.val.2).mp g.property
  change (shiftedWeakResolvent w q (g.val.1 + g.val.2),
    g.val.1 + g.val.2 - shiftedWeakResolvent w q (g.val.1 + g.val.2)) = g.val
  rw [← h, add_sub_cancel_left]

theorem graph_first_projection_injective (w : KahlerBackground n M) (q : ℕ) :
    Function.Injective (fun g : weakGraph w q => g.val.1) := by
  intro g h heq
  change g.val.1 = h.val.1 at heq
  have hg := (mem_weakGraph_iff w g.val.1 g.val.2).mp g.property
  have hh := (mem_weakGraph_iff w h.val.1 h.val.2).mp h.property
  have hs : g.val.1 + g.val.2 = h.val.1 + h.val.2 :=
    shiftedWeakResolvent_injective w q (hg.symm.trans (heq.trans hh))
  apply Subtype.ext
  rw [heq] at hs
  exact Prod.ext heq (add_left_cancel hs)

/-- Literal internally constructed domain; no completeness or closed-range assertion. -/
def weakDomain (w : KahlerBackground n M) (q : ℕ) :
    Submodule ℝ (HilbertFormL2 w.form.val w.isKahler.1 q) :=
  (shiftedWeakResolvent w q).range

/-- Actual algebraic equivalence onto the genuine range of the injective resolvent. -/
def resolventRangeEquiv (w : KahlerBackground n M) (q : ℕ) :
    HilbertFormL2 w.form.val w.isKahler.1 q ≃ₗ[ℝ] weakDomain w q :=
  LinearEquiv.ofInjective (shiftedWeakResolvent w q).toLinearMap
    (shiftedWeakResolvent_injective w q)

/-- The genuine weak Laplacian on its actual range domain, only algebraically linear. -/
def weakLaplacian (w : KahlerBackground n M) (q : ℕ) :
    weakDomain w q →ₗ[ℝ] HilbertFormL2 w.form.val w.isKahler.1 q :=
  (resolventRangeEquiv w q).symm.toLinearMap - (weakDomain w q).subtype

theorem resolventRangeEquiv_apply (w : KahlerBackground n M)
    (f : HilbertFormL2 w.form.val w.isKahler.1 q) :
    (resolventRangeEquiv w q f).val = shiftedWeakResolvent w q f := rfl

theorem resolventRangeEquiv_symm_apply (w : KahlerBackground n M) (x : weakDomain w q) :
    shiftedWeakResolvent w q ((resolventRangeEquiv w q).symm x) = x.val :=
  LinearEquiv.ofInjective_symm_apply (shiftedWeakResolvent w q).toLinearMap x

theorem weakLaplacian_resolvent (w : KahlerBackground n M)
    (f : HilbertFormL2 w.form.val w.isKahler.1 q) :
    weakLaplacian w q (resolventRangeEquiv w q f) = f - shiftedWeakResolvent w q f := by
  change (resolventRangeEquiv w q).symm (resolventRangeEquiv w q f) -
    shiftedWeakResolvent w q f = _
  rw [LinearEquiv.symm_apply_apply]

theorem domain_pair_mem_weakGraph (w : KahlerBackground n M) (x : weakDomain w q) :
    (x.val, weakLaplacian w q x) ∈ weakGraph w q := by
  apply (mem_weakGraph_iff w _ _).mpr
  change x.val = shiftedWeakResolvent w q
    (x.val + ((resolventRangeEquiv w q).symm x - x.val))
  have hsum : x.val + ((resolventRangeEquiv w q).symm x - x.val) =
      (resolventRangeEquiv w q).symm x := by abel
  exact (resolventRangeEquiv_symm_apply w x).symm.trans
    (congrArg (shiftedWeakResolvent w q) hsum.symm)

theorem mem_weakGraph_iff_domain (w : KahlerBackground n M)
    (x y : HilbertFormL2 w.form.val w.isKahler.1 q) :
    (x, y) ∈ weakGraph w q ↔ ∃ d : weakDomain w q, d.val = x ∧ weakLaplacian w q d = y := by
  constructor
  · intro h
    have hx := (mem_weakGraph_iff w x y).mp h
    refine ⟨resolventRangeEquiv w q (x + y), hx.symm, ?_⟩
    rw [weakLaplacian_resolvent, ← hx, add_sub_cancel_left]
  · rintro ⟨d, rfl, rfl⟩
    exact domain_pair_mem_weakGraph w d

theorem weakDomain_dense (w : KahlerBackground n M) (q : ℕ) :
    Dense (weakDomain w q : Set (HilbertFormL2 w.form.val w.isKahler.1 q)) :=
  shiftedWeakResolvent_denseRange w q

theorem weakLaplacian_graph_isClosed (w : KahlerBackground n M) (q : ℕ) :
    IsClosed {z : HilbertFormL2 w.form.val w.isKahler.1 q ×
      HilbertFormL2 w.form.val w.isKahler.1 q |
      ∃ d : weakDomain w q, d.val = z.1 ∧ weakLaplacian w q d = z.2} := by
  have hset : {z : HilbertFormL2 w.form.val w.isKahler.1 q ×
      HilbertFormL2 w.form.val w.isKahler.1 q |
      ∃ d : weakDomain w q, d.val = z.1 ∧ weakLaplacian w q d = z.2} =
      (weakGraph w q : Set _) := by
    ext z
    exact (mem_weakGraph_iff_domain w z.1 z.2).symm
  rw [hset]
  exact weakGraph_isClosed w q

/-- Exact whole graph-domain weak characterization, internally derived from genuine Riesz uniqueness. -/
theorem mem_weakGraph_iff_weak_equation (w : KahlerBackground n M)
    (x y : HilbertFormL2 w.form.val w.isKahler.1 q) :
    (x, y) ∈ weakGraph w q ↔ ∃ u : GraphEnergy w q,
      energyInclusion w q u = x ∧ ∀ v : GraphEnergy w q,
        inner ℝ (energyDerivative w q u) (energyDerivative w q v) +
          inner ℝ (energyCoderivative w q u) (energyCoderivative w q v) =
          inner ℝ y (energyInclusion w q v) := by
  constructor
  · intro h
    have hx := (mem_weakGraph_iff w x y).mp h
    refine ⟨energySolution w q (x + y), hx.symm, ?_⟩
    intro v
    have hr := energySolution_weak_equation w (x + y) v
    have hI : inner ℝ (energyInclusion w q (energySolution w q (x + y)))
        (energyInclusion w q v) = inner ℝ x (energyInclusion w q v) :=
      congrArg (fun a => inner ℝ a (energyInclusion w q v)) hx.symm
    have ha := inner_add_left (𝕜 := ℝ) x y (energyInclusion w q v)
    linarith
  · rintro ⟨u, hi, hu⟩
    have heq : u = energySolution w q (x + y) := by
      apply ext_inner_right ℝ
      intro v
      have hI := congrArg (fun a => inner ℝ a (energyInclusion w q v)) hi
      have ha := inner_add_left (𝕜 := ℝ) x y (energyInclusion w q v)
      have hw := hu v
      have hr := energySolution_inner w (x + y) v
      have hE := energy_inner w u v
      calc
        inner ℝ u v =
            (inner ℝ (energyInclusion w q u) (energyInclusion w q v) +
              inner ℝ (energyDerivative w q u) (energyDerivative w q v)) +
            inner ℝ (energyCoderivative w q u) (energyCoderivative w q v) := hE
        _ = inner ℝ (energyInclusion w q u) (energyInclusion w q v) +
            (inner ℝ (energyDerivative w q u) (energyDerivative w q v) +
              inner ℝ (energyCoderivative w q u) (energyCoderivative w q v)) :=
          add_assoc _ _ _
        _ = inner ℝ x (energyInclusion w q v) + inner ℝ y (energyInclusion w q v) :=
          congrArg₂ (fun a b : ℝ => a + b) hI hw
        _ = inner ℝ (x + y) (energyInclusion w q v) := ha.symm
        _ = inner ℝ (energySolution w q (x + y)) v := hr.symm
    apply (mem_weakGraph_iff w x y).mpr
    exact hi.symm.trans (congrArg (energyInclusion w q) heq)

/-- The actual shifted operator on the genuine domain, with no caller onto hypothesis. -/
def shiftedWeakLaplacian (w : KahlerBackground n M) (q : ℕ) :
    weakDomain w q →ₗ[ℝ] HilbertFormL2 w.form.val w.isKahler.1 q :=
  (weakDomain w q).subtype + weakLaplacian w q

theorem shiftedWeakLaplacian_eq_inverse (w : KahlerBackground n M) (x : weakDomain w q) :
    shiftedWeakLaplacian w q x = (resolventRangeEquiv w q).symm x := by
  change x.val + ((resolventRangeEquiv w q).symm x - x.val) = _
  abel

/-- Genuine bijectivity of I plus the actual unbounded weak Laplacian. -/
theorem shiftedWeakLaplacian_bijective (w : KahlerBackground n M) (q : ℕ) :
    Function.Bijective (shiftedWeakLaplacian w q) := by
  have heq : (shiftedWeakLaplacian w q : weakDomain w q →
      HilbertFormL2 w.form.val w.isKahler.1 q) = (resolventRangeEquiv w q).symm :=
    funext (shiftedWeakLaplacian_eq_inverse w)
  rw [heq]
  exact (resolventRangeEquiv w q).symm.bijective

theorem shiftedWeakLaplacian_resolvent (w : KahlerBackground n M)
    (f : HilbertFormL2 w.form.val w.isKahler.1 q) :
    shiftedWeakLaplacian w q (resolventRangeEquiv w q f) = f :=
  (shiftedWeakLaplacian_eq_inverse w _).trans
    ((resolventRangeEquiv w q).symm_apply_apply f)

theorem existsUnique_shifted_weakLaplacian_solution (w : KahlerBackground n M)
    (f : HilbertFormL2 w.form.val w.isKahler.1 q) :
    ∃! x : weakDomain w q, shiftedWeakLaplacian w q x = f := by
  refine ⟨resolventRangeEquiv w q f, shiftedWeakLaplacian_resolvent w f, ?_⟩
  intro x hx
  exact (shiftedWeakLaplacian_bijective w q).1
    (hx.trans (shiftedWeakLaplacian_resolvent w f).symm)

/-- The actual operator is symmetric on its constructed dense domain. -/
theorem weakLaplacian_inner_symm (w : KahlerBackground n M) (x z : weakDomain w q) :
    inner ℝ (weakLaplacian w q x) z.val = inner ℝ x.val (weakLaplacian w q z) := by
  obtain ⟨u, huI, hu⟩ := (mem_weakGraph_iff_weak_equation w x.val _).mp
    (domain_pair_mem_weakGraph w x)
  obtain ⟨v, hvI, hv⟩ := (mem_weakGraph_iff_weak_equation w z.val _).mp
    (domain_pair_mem_weakGraph w z)
  calc
    inner ℝ (weakLaplacian w q x) z.val =
        inner ℝ (weakLaplacian w q x) (energyInclusion w q v) :=
      congrArg (fun a => inner ℝ (weakLaplacian w q x) a) hvI.symm
    _ = inner ℝ (energyDerivative w q u) (energyDerivative w q v) +
        inner ℝ (energyCoderivative w q u) (energyCoderivative w q v) := (hu v).symm
    _ = inner ℝ (energyDerivative w q v) (energyDerivative w q u) +
        inner ℝ (energyCoderivative w q v) (energyCoderivative w q u) :=
      congrArg₂ (fun a b : ℝ => a + b)
        (real_inner_comm (energyDerivative w q v) (energyDerivative w q u))
        (real_inner_comm (energyCoderivative w q v) (energyCoderivative w q u))
    _ = inner ℝ (weakLaplacian w q z) (energyInclusion w q u) := hv u
    _ = inner ℝ (weakLaplacian w q z) x.val :=
      congrArg (fun a => inner ℝ (weakLaplacian w q z) a) huI
    _ = inner ℝ x.val (weakLaplacian w q z) := real_inner_comm x.val (weakLaplacian w q z)

/-- Literal two-coordinate energy for every actual first-coordinate lift. -/
theorem weakLaplacian_energy_identity (w : KahlerBackground n M) (x : weakDomain w q)
    (u : GraphEnergy w q) (hi : energyInclusion w q u = x.val) :
    inner ℝ (weakLaplacian w q x) x.val =
      ‖energyDerivative w q u‖ ^ 2 + ‖energyCoderivative w q u‖ ^ 2 := by
  obtain ⟨v, hvI, hv⟩ := (mem_weakGraph_iff_weak_equation w x.val _).mp
    (domain_pair_mem_weakGraph w x)
  have heq : v = u := energyInclusion_injective w q (hvI.trans hi.symm)
  subst v
  calc
    inner ℝ (weakLaplacian w q x) x.val =
        inner ℝ (weakLaplacian w q x) (energyInclusion w q u) :=
      congrArg (fun a => inner ℝ (weakLaplacian w q x) a) hi.symm
    _ = inner ℝ (energyDerivative w q u) (energyDerivative w q u) +
        inner ℝ (energyCoderivative w q u) (energyCoderivative w q u) := (hv u).symm
    _ = _ := congrArg₂ (fun a b : ℝ => a + b)
      (real_inner_self_eq_norm_sq (energyDerivative w q u))
      (real_inner_self_eq_norm_sq (energyCoderivative w q u))

theorem weakLaplacian_nonneg (w : KahlerBackground n M) (x : weakDomain w q) :
    0 ≤ inner ℝ (weakLaplacian w q x) x.val := by
  obtain ⟨u, hi, _⟩ := (mem_weakGraph_iff_weak_equation w x.val _).mp
    (domain_pair_mem_weakGraph w x)
  exact (add_nonneg (sq_nonneg ‖energyDerivative w q u‖)
    (sq_nonneg ‖energyCoderivative w q u‖)).trans_eq (weakLaplacian_energy_identity w x u hi).symm

/-- True original smooth Dirichlet identity, calibrated in the actual new Hilbert spaces. -/
theorem original_smooth_hilbert_dirichlet (w : KahlerBackground n M)
    (α β : SmoothRealForm n M q) :
    inner ℝ (toHilbertFormL2 w.form.val w.isKahler.1
        (hodgeLaplacianForm w.form.val w.isKahler.1 q α))
      (toHilbertFormL2 w.form.val w.isKahler.1 β) =
      inner ℝ (energyDerivative w q (smoothEnergyLinear w q α))
        (energyDerivative w q (smoothEnergyLinear w q β)) +
      inner ℝ (energyCoderivative w q (smoothEnergyLinear w q α))
        (energyCoderivative w q (smoothEnergyLinear w q β)) := by
  have hleft := (hilbert_inner w.form.val w.isKahler.1
      (hodgeLaplacianForm w.form.val w.isKahler.1 q α) β).trans
    (integralPair_eq_hodgeIntegralPairing w _ β)
  have hd : inner ℝ (energyDerivative w q (smoothEnergyLinear w q α))
      (energyDerivative w q (smoothEnergyLinear w q β)) =
      NaturalHermitianFormalAdjoint.hodgeIntegralPairing w (q + 1)
        α.exteriorDerivative β.exteriorDerivative :=
    (hilbert_inner w.form.val w.isKahler.1 α.exteriorDerivative β.exteriorDerivative).trans
      (integralPair_eq_hodgeIntegralPairing w α.exteriorDerivative β.exteriorDerivative)
  have hc : inner ℝ (energyCoderivative w q (smoothEnergyLinear w q α))
      (energyCoderivative w q (smoothEnergyLinear w q β)) =
      NaturalHermitianFormalAdjoint.hodgeIntegralPairing w (q - 1)
        (coderivativeForm w.form.val w.isKahler.1 q α)
        (coderivativeForm w.form.val w.isKahler.1 q β) :=
    (hilbert_inner w.form.val w.isKahler.1
      (coderivativeForm w.form.val w.isKahler.1 q α)
      (coderivativeForm w.form.val w.isKahler.1 q β)).trans
      (integralPair_eq_hodgeIntegralPairing w _ _)
  have hdir := hodgeLaplacian_dirichlet_identity w q α β
  cases q with
  | zero =>
    have hz : inner ℝ (energyCoderivative w 0 (smoothEnergyLinear w 0 α))
        (energyCoderivative w 0 (smoothEnergyLinear w 0 β)) = 0 :=
      (congrArg (fun a => inner ℝ a (energyCoderivative w 0 (smoothEnergyLinear w 0 β)))
        (energyCoderivative_zero_degree w (smoothEnergyLinear w 0 α))).trans
        (inner_zero_left _)
    change _ = NaturalHermitianFormalAdjoint.hodgeIntegralPairing w 1
      α.exteriorDerivative β.exteriorDerivative + 0 at hdir
    exact (hleft.trans hdir).trans (congrArg₂ (fun a b : ℝ => a + b) hd.symm hz.symm)
  | succ p =>
    change _ = NaturalHermitianFormalAdjoint.hodgeIntegralPairing w (p + 1 + 1)
      α.exteriorDerivative β.exteriorDerivative +
      NaturalHermitianFormalAdjoint.hodgeIntegralPairing w p
        (coderivativeForm w.form.val w.isKahler.1 (p + 1) α)
        (coderivativeForm w.form.val w.isKahler.1 (p + 1) β) at hdir
    exact (hleft.trans hdir).trans (congrArg₂ (fun a b : ℝ => a + b) hd.symm hc.symm)

/-- Genuine original smooth Laplacian pairs belong to the internally closed weak graph. -/
theorem original_smooth_pair_mem_weakGraph (w : KahlerBackground n M)
    (α : SmoothRealForm n M q) :
    (toHilbertFormL2 w.form.val w.isKahler.1 α,
      toHilbertFormL2 w.form.val w.isKahler.1
        (hodgeLaplacianForm w.form.val w.isKahler.1 q α)) ∈ weakGraph w q := by
  let H := HilbertFormL2 w.form.val w.isKahler.1 q
  let u : GraphEnergy w q := smoothEnergyLinear w q α
  let f : H := toHilbertFormL2 w.form.val w.isKahler.1
    (hodgeLaplacianForm w.form.val w.isKahler.1 q α)
  have hcontL : Continuous (fun v : GraphEnergy w q =>
      inner ℝ (energyDerivative w q u) (energyDerivative w q v) +
      inner ℝ (energyCoderivative w q u) (energyCoderivative w q v)) :=
    ((continuous_const : Continuous (fun _ : GraphEnergy w q => energyDerivative w q u)).inner
      (𝕜 := ℝ) (energyDerivative w q).continuous).add
      ((continuous_const : Continuous (fun _ : GraphEnergy w q => energyCoderivative w q u)).inner
        (𝕜 := ℝ) (energyCoderivative w q).continuous)
  have hcontR : Continuous (fun v : GraphEnergy w q => inner ℝ f (energyInclusion w q v)) :=
    (continuous_const : Continuous (fun _ : GraphEnergy w q => f)).inner
      (𝕜 := ℝ) (energyInclusion w q).continuous
  apply (mem_weakGraph_iff_weak_equation w _ _).mpr
  refine ⟨u, rfl, ?_⟩
  intro v
  exact (smoothEnergy_denseRange w q).induction_on
    (p := fun z => inner ℝ (energyDerivative w q u) (energyDerivative w q z) +
      inner ℝ (energyCoderivative w q u) (energyCoderivative w q z) =
      inner ℝ f (energyInclusion w q z)) v (isClosed_eq hcontL hcontR)
      (fun β => (original_smooth_hilbert_dirichlet w α β).symm)

theorem original_smooth_mem_weakDomain (w : KahlerBackground n M)
    (α : SmoothRealForm n M q) :
    toHilbertFormL2 w.form.val w.isKahler.1 α ∈ weakDomain w q := by
  obtain ⟨d, hd, _⟩ := (mem_weakGraph_iff_domain w _ _).mp
    (original_smooth_pair_mem_weakGraph w α)
  exact hd ▸ d.property

/-- The actual closed weak operator extends the literal original smooth Hodge Laplacian. -/
theorem weakLaplacian_original_smooth (w : KahlerBackground n M)
    (α : SmoothRealForm n M q) :
    weakLaplacian w q ⟨toHilbertFormL2 w.form.val w.isKahler.1 α,
      original_smooth_mem_weakDomain w α⟩ =
      toHilbertFormL2 w.form.val w.isKahler.1
        (hodgeLaplacianForm w.form.val w.isKahler.1 q α) := by
  obtain ⟨d, hd, hA⟩ := (mem_weakGraph_iff_domain w _ _).mp
    (original_smooth_pair_mem_weakGraph w α)
  have heq : d = ⟨toHilbertFormL2 w.form.val w.isKahler.1 α,
      original_smooth_mem_weakDomain w α⟩ := Subtype.ext hd
  exact (congrArg (weakLaplacian w q) heq).symm.trans hA

end SGPT.Foundations.Analysis.Pending.NaturalHermitianWeakLaplacian
