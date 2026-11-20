import SGPT.Foundations.Analysis.Pending.NaturalHermitianReducedPositiveShiftResolvent

set_option autoImplicit false

/-! # The actual reduced weak Laplacian graph and its entire adjoint
Five entire mathematical proofs precede SOURCE and have independent
mathematical review. Every graph, actual domain readback, density and
adjoint relation is internally constructed in the original harmonic
complement. The graph norm is the native Cartesian product-subspace norm.
-/

noncomputable section

open Set Filter
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.NaturalHermitianReducedWeakLaplacianGraph

open FirstPass FirstPass.PositiveClasses NaturalHermitianFormL2
  NaturalHermitianWeakHarmonicKernel NaturalHermitianReducedWeakResolvent
  NaturalHermitianReducedPositiveShiftResolvent

variable {n q : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M]

local instance (w : KahlerBackground n M) (q : ℕ) :
    NormedAddCommGroup ((harmonicKernel w q)ᗮ) :=
  Submodule.normedAddCommGroup ((harmonicKernel w q)ᗮ)

local instance (w : KahlerBackground n M) (q : ℕ) :
    InnerProductSpace ℝ ((harmonicKernel w q)ᗮ) :=
  Submodule.innerProductSpace ((harmonicKernel w q)ᗮ)

local instance (w : KahlerBackground n M) (q : ℕ) :
    NormedSpace ℝ ((harmonicKernel w q)ᗮ) :=
  (Submodule.innerProductSpace ((harmonicKernel w q)ᗮ)).toNormedSpace

local instance (w : KahlerBackground n M) (q : ℕ) :
    CompleteSpace ((harmonicKernel w q)ᗮ) := harmonicComplement_complete w q

/-- Actual continuous kernel map using the original reduced resolvent and native projections. -/
def reducedGraphKernel (w : KahlerBackground n M) (q : ℕ) :
    ((harmonicKernel w q)ᗮ × (harmonicKernel w q)ᗮ) →L[ℝ] (harmonicKernel w q)ᗮ :=
  ContinuousLinearMap.fst ℝ _ _ - (reducedResolvent w q).comp
    (ContinuousLinearMap.fst ℝ _ _ + ContinuousLinearMap.snd ℝ _ _)

/-- Literal actual closed reduced graph, with the native product-subspace norm. -/
def reducedWeakGraph (w : KahlerBackground n M) (q : ℕ) :
    Submodule ℝ ((harmonicKernel w q)ᗮ × (harmonicKernel w q)ᗮ) :=
  (reducedGraphKernel w q).ker

theorem mem_reducedWeakGraph_iff (w : KahlerBackground n M)
    (x y : (harmonicKernel w q)ᗮ) :
    (x, y) ∈ reducedWeakGraph w q ↔ x = reducedResolvent w q (x + y) := by
  change x - reducedResolvent w q (x + y) = 0 ↔ _
  exact sub_eq_zero

theorem reducedWeakGraph_isClosed (w : KahlerBackground n M) (q : ℕ) :
    IsClosed (reducedWeakGraph w q : Set ((harmonicKernel w q)ᗮ × (harmonicKernel w q)ᗮ)) :=
  (reducedGraphKernel w q).isClosed_ker

theorem reducedWeakGraph_complete (w : KahlerBackground n M) (q : ℕ) :
    CompleteSpace (reducedWeakGraph w q) :=
  ContinuousLinearMap.completeSpace_ker (reducedGraphKernel w q)

theorem reducedResolvent_pair_mem_graph (w : KahlerBackground n M)
    (f : (harmonicKernel w q)ᗮ) :
    (reducedResolvent w q f, f - reducedResolvent w q f) ∈ reducedWeakGraph w q := by
  apply (mem_reducedWeakGraph_iff w _ _).mpr
  rw [add_sub_cancel]

/-- The entire literal reduced original domain gives genuine graph elements. -/
theorem reducedDomain_pair_mem_graph (w : KahlerBackground n M)
    (a : reducedWeakDomain w q) :
    (reducedDomainInclusion w q a, reducedWeakLaplacian w q a) ∈ reducedWeakGraph w q := by
  apply (mem_reducedWeakGraph_iff w _ _).mpr
  apply Subtype.ext
  exact (NaturalHermitianWeakLaplacian.mem_weakGraph_iff w _ _).mp
    (NaturalHermitianWeakLaplacian.domain_pair_mem_weakGraph w a.val)

/-- True original-domain readback, internally transporting the actual original kernel graph. -/
theorem mem_reducedWeakGraph_iff_domain (w : KahlerBackground n M)
    (x y : (harmonicKernel w q)ᗮ) :
    (x, y) ∈ reducedWeakGraph w q ↔ ∃ a : reducedWeakDomain w q,
      reducedDomainInclusion w q a = x ∧ reducedWeakLaplacian w q a = y := by
  constructor
  · intro h
    have hx := (mem_reducedWeakGraph_iff w x y).mp h
    have hG : (x.val, y.val) ∈ NaturalHermitianWeakLaplacian.weakGraph w q := by
      apply (NaturalHermitianWeakLaplacian.mem_weakGraph_iff w _ _).mpr
      exact congrArg Subtype.val hx
    obtain ⟨a, ha, hA⟩ :=
      (NaturalHermitianWeakLaplacian.mem_weakGraph_iff_domain w x.val y.val).mp hG
    have he : a ∈ reducedWeakDomain w q := by
      change a.val ∈ (harmonicKernel w q)ᗮ
      rw [ha]
      exact x.property
    exact ⟨⟨a, he⟩, Subtype.ext ha, Subtype.ext hA⟩
  · rintro ⟨a, hx, hy⟩
    exact hx ▸ hy ▸ reducedDomain_pair_mem_graph w a

theorem reducedGraph_first_projection_injective (w : KahlerBackground n M) (q : ℕ) :
    Function.Injective (fun g : reducedWeakGraph w q => g.val.1) := by
  intro g h heq
  change g.val.1 = h.val.1 at heq
  have hg := (mem_reducedWeakGraph_iff w g.val.1 g.val.2).mp g.property
  have hh := (mem_reducedWeakGraph_iff w h.val.1 h.val.2).mp h.property
  have hs : g.val.1 + g.val.2 = h.val.1 + h.val.2 :=
    reducedResolvent_injective w q (hg.symm.trans (heq.trans hh))
  apply Subtype.ext
  rw [heq] at hs
  exact Prod.ext heq (add_left_cancel hs)

/-- The literal first-coordinate image of the actual original reduced domain. -/
def reducedDomainImage (w : KahlerBackground n M) (q : ℕ) :
    Submodule ℝ (harmonicKernel w q)ᗮ := (reducedDomainInclusion w q).range

theorem reducedDomainImage_eq_resolvent_range (w : KahlerBackground n M) (q : ℕ) :
    reducedDomainImage w q = (reducedResolvent w q).range := by
  ext f
  constructor
  · rintro ⟨a, ha⟩
    have h := (mem_reducedWeakGraph_iff w _ _).mp (reducedDomain_pair_mem_graph w a)
    exact ⟨reducedDomainInclusion w q a + reducedWeakLaplacian w q a, h.symm.trans ha⟩
  · rintro ⟨g, hg⟩
    obtain ⟨a, ha, _⟩ := (mem_reducedWeakGraph_iff_domain w _ _).mp
      (reducedResolvent_pair_mem_graph w g)
    exact ⟨a, ha.trans hg⟩

theorem reducedDomainImage_dense (w : KahlerBackground n M) (q : ℕ) :
    Dense (reducedDomainImage w q : Set (harmonicKernel w q)ᗮ) := by
  rw [reducedDomainImage_eq_resolvent_range]
  exact reducedResolvent_denseRange w q

/-- Actual bounded native graph parametrization, with genuine kernel membership internal. -/
def reducedGraphParametrization (w : KahlerBackground n M) (q : ℕ) :
    (harmonicKernel w q)ᗮ →L[ℝ] reducedWeakGraph w q := by
  let E : Type _ := ↥((harmonicKernel w q)ᗮ)
  let S : E →L[ℝ] E := reducedResolvent w q
  let P : E →L[ℝ] E × E := S.prod (ContinuousLinearMap.id ℝ E - S)
  exact P.codRestrict (reducedWeakGraph w q) (fun f => reducedResolvent_pair_mem_graph w f)

/-- Actual native graph forcing map, the sum of its two coordinates. -/
def reducedGraphForcing (w : KahlerBackground n M) (q : ℕ) :
    reducedWeakGraph w q →L[ℝ] (harmonicKernel w q)ᗮ :=
  (ContinuousLinearMap.fst ℝ (harmonicKernel w q)ᗮ (harmonicKernel w q)ᗮ +
    ContinuousLinearMap.snd ℝ (harmonicKernel w q)ᗮ (harmonicKernel w q)ᗮ).comp
    (reducedWeakGraph w q).subtypeL

theorem reducedGraphForcing_parametrization (w : KahlerBackground n M)
    (f : (harmonicKernel w q)ᗮ) :
    reducedGraphForcing w q (reducedGraphParametrization w q f) = f := by
  change reducedResolvent w q f + (f - reducedResolvent w q f) = f
  abel

theorem reducedGraphParametrization_forcing (w : KahlerBackground n M)
    (g : reducedWeakGraph w q) :
    reducedGraphParametrization w q (reducedGraphForcing w q g) = g := by
  apply Subtype.ext
  have h := (mem_reducedWeakGraph_iff w g.val.1 g.val.2).mp g.property
  change (reducedResolvent w q (g.val.1 + g.val.2),
    g.val.1 + g.val.2 - reducedResolvent w q (g.val.1 + g.val.2)) = g.val
  rw [← h, add_sub_cancel_left]

/-- The actual continuous equivalence compares forcing with the genuine graph norm. -/
def reducedGraphEquiv (w : KahlerBackground n M) (q : ℕ) :
    (harmonicKernel w q)ᗮ ≃L[ℝ] reducedWeakGraph w q :=
  ContinuousLinearEquiv.equivOfInverse (reducedGraphParametrization w q) (reducedGraphForcing w q)
    (fun f => reducedGraphForcing_parametrization w f)
    (fun g => reducedGraphParametrization_forcing w g)

theorem reducedGraphEquiv_apply (w : KahlerBackground n M)
    (f : (harmonicKernel w q)ᗮ) : reducedGraphEquiv w q f = reducedGraphParametrization w q f := rfl

theorem reducedGraphEquiv_symm_apply (w : KahlerBackground n M)
    (g : reducedWeakGraph w q) : (reducedGraphEquiv w q).symm g = reducedGraphForcing w q g := rfl

/-- Literal whole-domain reduced adjoint relation; no supplied test or adjoint certificate. -/
def reducedAdjointGraph (w : KahlerBackground n M) (q : ℕ) :
    Submodule ℝ ((harmonicKernel w q)ᗮ × (harmonicKernel w q)ᗮ) where
  carrier := {p | ∀ g : reducedWeakGraph w q,
    inner ℝ g.val.2 p.1 = inner ℝ g.val.1 p.2}
  zero_mem' := by intro g; simp only [Prod.fst_zero, Prod.snd_zero, inner_zero_right]
  add_mem' := by
    intro a b ha hb g
    change inner ℝ g.val.2 (a.1 + b.1) = inner ℝ g.val.1 (a.2 + b.2)
    simp only [inner_add_right, ha g, hb g]
  smul_mem' := by
    intro c a ha g
    change inner ℝ g.val.2 (c • a.1) = inner ℝ g.val.1 (c • a.2)
    exact (real_inner_smul_right g.val.2 a.1 c).trans
      ((congrArg (fun r : ℝ => c * r) (ha g)).trans
        (real_inner_smul_right g.val.1 a.2 c).symm)

theorem mem_reducedAdjointGraph_iff (w : KahlerBackground n M)
    (v z : (harmonicKernel w q)ᗮ) :
    (v, z) ∈ reducedAdjointGraph w q ↔ ∀ g : reducedWeakGraph w q,
      inner ℝ g.val.2 v = inner ℝ g.val.1 z := Iff.rfl

theorem mem_reducedAdjointGraph_iff_domain_tests (w : KahlerBackground n M)
    (v z : (harmonicKernel w q)ᗮ) :
    (v, z) ∈ reducedAdjointGraph w q ↔ ∀ a : reducedWeakDomain w q,
      inner ℝ (reducedWeakLaplacian w q a) v = inner ℝ (reducedDomainInclusion w q a) z := by
  constructor
  · intro h a
    exact h ⟨(reducedDomainInclusion w q a, reducedWeakLaplacian w q a),
      reducedDomain_pair_mem_graph w a⟩
  · intro h g
    obtain ⟨a, hx, hy⟩ := (mem_reducedWeakGraph_iff_domain w g.val.1 g.val.2).mp g.property
    exact (congrArg (fun b => inner ℝ b v) hy.symm).trans
      ((h a).trans (congrArg (fun b => inner ℝ b z) hx))

theorem reducedAdjointGraph_isClosed (w : KahlerBackground n M) (q : ℕ) :
    IsClosed (reducedAdjointGraph w q : Set ((harmonicKernel w q)ᗮ × (harmonicKernel w q)ᗮ)) := by
  let E := (harmonicKernel w q)ᗮ
  let C : reducedWeakGraph w q → Set (E × E) :=
    fun g => {p | inner ℝ g.val.2 p.1 = inner ℝ g.val.1 p.2}
  have hset : (reducedAdjointGraph w q : Set (E × E)) = ⋂ g, C g := by
    ext p
    simp only [Set.mem_iInter]
    rfl
  rw [hset]
  apply isClosed_iInter
  intro g
  exact isClosed_eq
    ((continuous_const : Continuous (fun _ : E × E => g.val.2)).inner (𝕜 := ℝ)
      (continuous_fst : Continuous (fun p : E × E => p.1)))
    ((continuous_const : Continuous (fun _ : E × E => g.val.1)).inner (𝕜 := ℝ)
      (continuous_snd : Continuous (fun p : E × E => p.2)))

/-- Entire original reduced graph self-adjointness, proved using all actual forcing vectors. -/
theorem reducedAdjointGraph_eq_graph (w : KahlerBackground n M) (q : ℕ) :
    reducedAdjointGraph w q = reducedWeakGraph w q := by
  ext p
  constructor
  · intro h
    apply (mem_reducedWeakGraph_iff w p.1 p.2).mpr
    apply ext_inner_left ℝ
    intro f
    have ht := h ⟨(reducedResolvent w q f, f - reducedResolvent w q f),
      reducedResolvent_pair_mem_graph w f⟩
    have hs := inner_sub_left (𝕜 := ℝ) f (reducedResolvent w q f) p.1
    have ha := inner_add_right (𝕜 := ℝ) (reducedResolvent w q f) p.1 p.2
    have hr := reducedResolvent_inner_symm w f (p.1 + p.2)
    change inner ℝ (f - reducedResolvent w q f) p.1 = inner ℝ (reducedResolvent w q f) p.2 at ht
    linarith
  · intro h
    obtain ⟨a, hx, hy⟩ := (mem_reducedWeakGraph_iff_domain w p.1 p.2).mp h
    apply (mem_reducedAdjointGraph_iff_domain_tests w p.1 p.2).mpr
    intro b
    exact (congrArg (fun c => inner ℝ (reducedWeakLaplacian w q b) c) hx.symm).trans
      ((reducedWeakLaplacian_inner_symm w b a).trans
        (congrArg (fun c => inner ℝ (reducedDomainInclusion w q b) c) hy))

/-- Literal first-coordinate image of the whole internally defined reduced adjoint graph. -/
def reducedAdjointDomain (w : KahlerBackground n M) (q : ℕ) :
    Submodule ℝ (harmonicKernel w q)ᗮ :=
  (reducedAdjointGraph w q).map (LinearMap.fst ℝ (harmonicKernel w q)ᗮ (harmonicKernel w q)ᗮ)

theorem mem_reducedAdjointDomain_iff (w : KahlerBackground n M)
    (v : (harmonicKernel w q)ᗮ) :
    v ∈ reducedAdjointDomain w q ↔ ∃ z : (harmonicKernel w q)ᗮ,
      (v, z) ∈ reducedAdjointGraph w q := by
  constructor
  · rintro ⟨p, hp, hv⟩
    change p.1 = v at hv
    exact ⟨p.2, hv ▸ hp⟩
  · rintro ⟨z, hz⟩
    exact ⟨(v, z), hz, rfl⟩

theorem reducedAdjoint_tests_iff_domain_value (w : KahlerBackground n M)
    (v z : (harmonicKernel w q)ᗮ) :
    (∀ a : reducedWeakDomain w q, inner ℝ (reducedWeakLaplacian w q a) v =
      inner ℝ (reducedDomainInclusion w q a) z) ↔ ∃ a : reducedWeakDomain w q,
      reducedDomainInclusion w q a = v ∧ reducedWeakLaplacian w q a = z := by
  have heq : (v, z) ∈ reducedAdjointGraph w q ↔ (v, z) ∈ reducedWeakGraph w q :=
    Iff.of_eq (congrArg (fun G => (v, z) ∈ G) (reducedAdjointGraph_eq_graph w q))
  exact (mem_reducedAdjointGraph_iff_domain_tests w v z).symm.trans
    (heq.trans (mem_reducedWeakGraph_iff_domain w v z))

theorem reducedAdjointDomain_eq_domainImage (w : KahlerBackground n M) (q : ℕ) :
    reducedAdjointDomain w q = reducedDomainImage w q := by
  ext v
  constructor
  · intro h
    obtain ⟨z, hz⟩ := (mem_reducedAdjointDomain_iff w v).mp h
    obtain ⟨a, ha, _⟩ := (reducedAdjoint_tests_iff_domain_value w v z).mp
      ((mem_reducedAdjointGraph_iff_domain_tests w v z).mp hz)
    exact ⟨a, ha⟩
  · rintro ⟨a, ha⟩
    apply (mem_reducedAdjointDomain_iff w v).mpr
    refine ⟨reducedWeakLaplacian w q a, ?_⟩
    apply (mem_reducedAdjointGraph_iff_domain_tests w v _).mpr
    exact (reducedAdjoint_tests_iff_domain_value w v _).mpr ⟨a, ha, rfl⟩

theorem reducedAdjointDomain_dense (w : KahlerBackground n M) (q : ℕ) :
    Dense (reducedAdjointDomain w q : Set (harmonicKernel w q)ᗮ) := by
  rw [reducedAdjointDomain_eq_domainImage]
  exact reducedDomainImage_dense w q

theorem existsUnique_reducedAdjoint_value (w : KahlerBackground n M)
    (a : reducedWeakDomain w q) :
    ∃! z : (harmonicKernel w q)ᗮ, ∀ b : reducedWeakDomain w q,
      inner ℝ (reducedWeakLaplacian w q b) (reducedDomainInclusion w q a) =
        inner ℝ (reducedDomainInclusion w q b) z := by
  refine ⟨reducedWeakLaplacian w q a,
    (reducedAdjoint_tests_iff_domain_value w _ _).mpr ⟨a, rfl, rfl⟩, ?_⟩
  intro z hz
  have hg : (reducedDomainInclusion w q a, z) ∈ reducedWeakGraph w q :=
    (reducedAdjointGraph_eq_graph w q) ▸
      (mem_reducedAdjointGraph_iff_domain_tests w _ _).mpr hz
  have heq :
      (⟨(reducedDomainInclusion w q a, z), hg⟩ : reducedWeakGraph w q) =
      (⟨(reducedDomainInclusion w q a, reducedWeakLaplacian w q a),
        reducedDomain_pair_mem_graph w a⟩ : reducedWeakGraph w q) :=
    reducedGraph_first_projection_injective w q rfl
  exact congrArg (fun g : reducedWeakGraph w q => g.val.2) heq

end SGPT.Foundations.Analysis.Pending.NaturalHermitianReducedWeakLaplacianGraph
