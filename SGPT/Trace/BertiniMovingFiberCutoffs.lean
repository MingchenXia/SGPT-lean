import Mathlib.Topology.PartitionOfUnity
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Tactic

/-! Fixed ambient cutoffs on every nearby fibre of a closed compact incidence.
Blueprint: bertini-moving-fiber-cutoffs.tex. No section or weight inputs. -/
set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace SGPT.Trace.MovingFiberCutoffs
open Set
open scoped Topology BigOperators

variable {P X : Type*} [TopologicalSpace P] [TopologicalSpace X] [CompactSpace X]

theorem exists_uniform_fiber_in_open {J O : Set (P × X)} (hJ : IsClosed J)
    (hO : IsOpen O) (p₀ : P) (h₀ : ∀ x, (p₀,x) ∈ J → (p₀,x) ∈ O) :
    ∃ V : TopologicalSpace.Opens P, p₀ ∈ V ∧
      ∀ p ∈ V, ∀ x, (p,x) ∈ J → (p,x) ∈ O := by
  let B : Set (P × X) := J ∩ Oᶜ
  have hB : IsClosed B := hJ.inter hO.isClosed_compl
  have hproj : IsClosed (Prod.fst '' B) := isClosedMap_fst_of_compactSpace B hB
  refine ⟨⟨(Prod.fst '' B)ᶜ,hproj.isOpen_compl⟩,?_,?_⟩
  · rintro ⟨⟨p,x⟩,hx,hp⟩
    change p = p₀ at hp
    subst p
    exact hx.2 (h₀ x hx.1)
  · intro p hp x hx
    by_contra ho
    exact hp ⟨(p,x),⟨hx,ho⟩,rfl⟩

theorem exists_fixed_ambient_fiber_cutoffs [T2Space X] {J : Set (P × X)}
    (hJ : IsClosed J) (p₀ : P) (k : ℕ) (O : Fin k → Set (P × X))
    (hO : ∀ j, IsOpen (O j))
    (hcover : ∀ x, (p₀,x) ∈ J → ∃ j, (p₀,x) ∈ O j) :
    ∃ (V : TopologicalSpace.Opens P) (β : Fin k → C(X,ℝ)), p₀ ∈ V ∧
      (∀ j x, 0 ≤ β j x ∧ β j x ≤ 1) ∧
      (∀ j, HasCompactSupport (β j)) ∧
      (∀ p ∈ V, ∀ j, tsupport (β j) ⊆ {x | (p,x) ∈ O j}) ∧
      ∀ p ∈ V, ∀ x, (p,x) ∈ J → (∑ j, β j x) = 1 := by
  classical
  let K : Set X := {x | (p₀,x) ∈ J}
  let U : Fin k → Set X := fun j => {x | (p₀,x) ∈ O j}
  have hK : IsClosed K := hJ.preimage (continuous_const.prodMk continuous_id)
  have hU : ∀ j, IsOpen (U j) := fun j =>
    (hO j).preimage (continuous_const.prodMk continuous_id)
  obtain ⟨f,hfsub,hfone,hf,hfc⟩ := exists_continuous_sum_one_of_isOpen_isCompact
    hU hK.isCompact (fun x hx => mem_iUnion.mpr (hcover x hx))
  let S : X → ℝ := fun x => ∑ j, f j x
  have hS : Continuous S := by fun_prop
  have hone (x : X) (hx : (p₀,x) ∈ J) : S x = 1 := by
    simpa only [S,Finset.sum_apply,Pi.one_apply] using hfone hx
  have hopen : IsOpen {q : P × X | (1/2 : ℝ) < S q.2} :=
    isOpen_lt continuous_const (hS.comp continuous_snd)
  obtain ⟨V₀,hV₀,hSnear⟩ := exists_uniform_fiber_in_open hJ hopen p₀
    (fun x hx => by change (1/2 : ℝ) < S x; rw [hone x hx]; norm_num)
  have htube (j : Fin k) : ∃ V : TopologicalSpace.Opens P, p₀ ∈ V ∧
      ∀ p ∈ V, ∀ x ∈ tsupport (f j), (p,x) ∈ O j := by
    have hc : IsClosed {q : P × X | q.2 ∈ tsupport (f j)} :=
      (isClosed_tsupport _).preimage continuous_snd
    exact exists_uniform_fiber_in_open hc (hO j) p₀ (fun x hx => hfsub j hx)
  choose Vj hVj hsupport using htube
  let V : TopologicalSpace.Opens P :=
    ⟨(V₀ : Set P) ∩ ⋂ j, (Vj j : Set P),
      V₀.isOpen.inter (isOpen_iInter_of_finite fun j => (Vj j).isOpen)⟩
  have hden (x : X) : 0 < max (S x) (1/2 : ℝ) :=
    lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  let β : Fin k → C(X,ℝ) := fun j =>
    ⟨fun x => f j x / max (S x) (1/2 : ℝ),
      (f j).continuous.div (hS.max continuous_const) (fun x => (hden x).ne')⟩
  have hsβ (j : Fin k) : tsupport (β j) ⊆ tsupport (f j) := by
    change tsupport (fun x => f j x / max (S x) (1/2 : ℝ)) ⊆ tsupport (f j)
    simp only [div_eq_mul_inv]
    exact tsupport_mul_subset_left
  refine ⟨V,β,⟨hV₀,mem_iInter.mpr hVj⟩,?_,?_,?_,?_⟩
  · intro j x
    refine ⟨div_nonneg (hf j x).1 (hden x).le,?_⟩
    apply (div_le_one (hden x)).mpr
    exact (Finset.single_le_sum (fun i _ => (hf i x).1) (Finset.mem_univ j)).trans
      (le_max_left (S x) (1/2 : ℝ))
  · intro j
    exact (isClosed_tsupport _).isCompact
  · intro p hp j x hx
    exact hsupport j p (mem_iInter.mp hp.2 j) x (hsβ j hx)
  · intro p hp x hx
    have hs : (1/2 : ℝ) < S x := hSnear p hp.1 x hx
    change (∑ j, f j x / max (S x) (1/2 : ℝ)) = 1
    rw [← Finset.sum_div,max_eq_left hs.le]
    exact div_self (ne_of_gt (lt_trans (by norm_num) hs))

end SGPT.Trace.MovingFiberCutoffs
