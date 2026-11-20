import Mathlib.Topology.TietzeExtension
import Mathlib.Topology.Semicontinuity.Basic

set_option autoImplicit false

/-!
# Xia's Step 2 family: decreasing lower semicontinuous majorants of a quasi-continuous function

Xia, SGPT, proof of Theorem 2.4.4, Step 2 (`xia-sgpt:page-0082`).  For a
bounded quasi-continuous obstacle `F` one chooses open sets `V_j` of small
capacity with `F` continuous off `V_j`, extends `F|_{V_jᶜ}` to a continuous
`f_j` by Tietze, and sets

  `h_j := sup_{k ≥ j} f_k`,   `h := inf_j h_j`.

The `h_j` are lower semicontinuous, decreasing, bounded in the same interval as
`F`, and agree with `F` off `V_j`; consequently `h = F` off `⋂_j V_j`, which is
the set Xia discards as pluripolar.

This module is exactly that construction, with no pluripotential input at all:
capacity never appears, only the topology.  What a consumer has to supply is
the decreasing family `V_j` of open sets off which `F` is continuous — that is
the quasi-continuity — and what it gets back is the decreasing family of real
majorants required by
`Pending.RooftopMajorantFamilyConcentration.diagonalPotentialMeasure_rooftopEnvelope_lt_add_eq_zero_of_majorants`.

The members are only lower semicontinuous, and that is forced, not an artefact
of this construction: if `F` jumps upward inside `V` arbitrarily close to the
boundary of `V`, no *continuous* `G` with `G = F` off `V` can satisfy `G ≥ F`
on `V`, because continuity pins `G` to `F` near the boundary.  See
`Pending.RooftopMajorantFamilyConcentration` for what lower semicontinuity of
the members then costs.
-/

open Set

namespace SGPT.Foundations.Analysis.Pending.QuasiContinuousMajorantFamily

variable {M : Type*} [TopologicalSpace M]

/-! ### The tail supremum -/

/-- `h_j = sup_{k ≥ j} f_k`, written as a supremum over the shifted index so
that the index type stays `ℕ`. -/
noncomputable def tailSup (f : ℕ → M → ℝ) (j : ℕ) (x : M) : ℝ := ⨆ k : ℕ, f (j + k) x

section Tail

variable {f : ℕ → M → ℝ}

theorem bddAbove_tail (hf0 : ∀ k x, f k x ≤ 0) (j : ℕ) (x : M) :
    BddAbove (range fun k : ℕ => f (j + k) x) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨k, rfl⟩
  exact hf0 _ _

theorem le_tailSup (hf0 : ∀ k x, f k x ≤ 0) (j k : ℕ) (x : M) :
    f (j + k) x ≤ tailSup f j x :=
  le_ciSup (bddAbove_tail hf0 j x) k

theorem tailSup_le_zero (hf0 : ∀ k x, f k x ≤ 0) (j : ℕ) (x : M) : tailSup f j x ≤ 0 :=
  ciSup_le fun _ => hf0 _ _

theorem neg_le_tailSup {C : ℝ} (hf0 : ∀ k x, f k x ≤ 0) (hfC : ∀ k x, -C ≤ f k x) (j : ℕ) (x : M) :
    -C ≤ tailSup f j x :=
  (hfC j x).trans (by simpa using le_tailSup hf0 j 0 x)

theorem tailSup_mem_Icc {C : ℝ} (hf0 : ∀ k x, f k x ≤ 0) (hfC : ∀ k x, -C ≤ f k x) (j : ℕ) (x : M) :
    tailSup f j x ∈ Icc (-C) 0 :=
  ⟨neg_le_tailSup hf0 hfC j x, tailSup_le_zero hf0 j x⟩

/-- The tails decrease: fewer terms enter the supremum. -/
theorem tailSup_antitone (hf0 : ∀ k x, f k x ≤ 0) (x : M) :
    Antitone fun j => tailSup f j x := by
  intro i j hij
  refine ciSup_le fun k => ?_
  have : j + k = i + (j - i + k) := by omega
  rw [this]
  exact le_tailSup hf0 i _ x

/-- A supremum of continuous functions is lower semicontinuous. -/
theorem lowerSemicontinuous_tailSup (hcont : ∀ k, Continuous (f k))
    (hf0 : ∀ k x, f k x ≤ 0) (j : ℕ) : LowerSemicontinuous (tailSup f j) := by
  refine lowerSemicontinuous_ciSup (f := fun k x => f (j + k) x)
    (fun x => bddAbove_tail hf0 j x) ?_
  exact fun k => (hcont (j + k)).lowerSemicontinuous

/-- Where every late member of the family already equals `F`, so does the tail
supremum. -/
theorem tailSup_eq_of_forall_ge {F : M → ℝ} {j : ℕ} {x : M}
    (h : ∀ k, j ≤ k → f k x = F x) : tailSup f j x = F x := by
  have : ∀ k : ℕ, f (j + k) x = F x := fun k => h (j + k) (Nat.le_add_right _ _)
  simp only [tailSup, this]
  exact ciSup_const

/-- At a point which some `V_j` already misses, the infimum of the tails is the
original value. -/
theorem iInf_tailSup_eq {C : ℝ} (hf0 : ∀ k x, f k x ≤ 0) (hfC : ∀ k x, -C ≤ f k x)
    {F : M → ℝ} {x : M} {j₀ : ℕ} (h : ∀ k, j₀ ≤ k → f k x = F x) :
    (⨅ j : ℕ, tailSup f j x) = F x := by
  refine le_antisymm ?_ ?_
  · refine le_of_le_of_eq (ciInf_le ⟨-C, ?_⟩ j₀) (tailSup_eq_of_forall_ge h)
    rintro _ ⟨j, rfl⟩
    exact neg_le_tailSup hf0 hfC j x
  · refine le_ciInf fun j => ?_
    have hle : f (j + (j₀ - j + j₀)) x = F x := h _ (by omega)
    exact hle ▸ le_tailSup hf0 j _ x

end Tail

/-! ### Tietze: continuous extensions with the same bounds -/

/-- **Tietze extension with the obstacle's own bounds.**  A function continuous
off an open set, with values in `[-C, 0]`, extends to a continuous function on
all of `M` with values in the same interval, agreeing with it off that open
set. -/
theorem exists_continuous_mem_Icc_eq_of_isOpen [NormalSpace M] {V : Set M} (hV : IsOpen V)
    {F : M → ℝ} {C : ℝ} (hC : (0 : ℝ) ≤ C) (hmem : ∀ x, F x ∈ Icc (-C) 0)
    (hcont : ContinuousOn F Vᶜ) :
    ∃ G : M → ℝ, Continuous G ∧ (∀ x, G x ∈ Icc (-C) 0) ∧ ∀ x ∈ Vᶜ, G x = F x := by
  classical
  have hsc : IsClosed (Vᶜ : Set M) := hV.isClosed_compl
  set g : C((Vᶜ : Set M), ℝ) := ⟨fun x => F x.1, hcont.domRestrict⟩ with hg
  have hne : (Icc (-C) 0).Nonempty := ⟨-C, le_rfl, by linarith⟩
  obtain ⟨G, hGmem, hGres⟩ :=
    g.exists_restrict_eq_forall_mem_of_closed (t := Icc (-C) 0)
      (fun x => hmem x.1) hne hsc
  refine ⟨G, G.continuous, hGmem, fun x hx => ?_⟩
  exact congrArg (fun p : C((Vᶜ : Set M), ℝ) => p ⟨x, hx⟩) hGres

/-! ### The family -/

/-- **Xia's Step 2 family.**  From a decreasing sequence of open sets off which
`F` is continuous, one gets a decreasing sequence of lower semicontinuous real
functions with the same bounds, agreeing with `F` off the corresponding open
set, and whose pointwise infimum is `F` off the intersection.

This is exactly the input shape of
`Pending.RooftopMajorantFamilyConcentration.diagonalPotentialMeasure_rooftopEnvelope_lt_add_eq_zero_of_majorants`,
minus the two pluripotential facts about the members. -/
theorem exists_antitone_lowerSemicontinuous_family [NormalSpace M]
    {V : ℕ → Set M} (hVopen : ∀ j, IsOpen (V j)) (hVanti : Antitone V)
    {F : M → ℝ} {C : ℝ} (hC : (0 : ℝ) ≤ C) (hmem : ∀ x, F x ∈ Icc (-C) 0)
    (hcont : ∀ j, ContinuousOn F (V j)ᶜ) :
    ∃ h : ℕ → M → ℝ,
      (∀ j, LowerSemicontinuous (h j)) ∧
      (∀ j x, h j x ∈ Icc (-C) 0) ∧
      (∀ x, Antitone fun j => h j x) ∧
      (∀ j, ∀ x ∉ V j, h j x = F x) ∧
      (∀ x ∉ ⋂ j, V j, (⨅ j : ℕ, h j x) = F x) := by
  classical
  choose fam hfamcont hfammem hfameq using fun j =>
    exists_continuous_mem_Icc_eq_of_isOpen (C := C) (hVopen j) hC hmem (hcont j)
  have hf0 : ∀ k x, fam k x ≤ 0 := fun k x => (hfammem k x).2
  have hfC : ∀ k x, -C ≤ fam k x := fun k x => (hfammem k x).1
  refine ⟨tailSup fam, fun j => lowerSemicontinuous_tailSup hfamcont hf0 j,
    fun j x => tailSup_mem_Icc hf0 hfC j x, fun x => tailSup_antitone hf0 x, ?_, ?_⟩
  · intro j x hx
    refine tailSup_eq_of_forall_ge fun k hk => ?_
    exact hfameq k x (fun hmem' => hx (hVanti hk hmem'))
  · intro x hx
    obtain ⟨j₀, hj₀⟩ : ∃ j₀ : ℕ, x ∉ V j₀ := by
      by_contra hcon
      exact hx (mem_iInter.mpr fun j => not_not.mp fun hnot => hcon ⟨j, hnot⟩)
    refine iInf_tailSup_eq hf0 hfC (j₀ := j₀) fun k hk => ?_
    exact hfameq k x (fun hmem' => hj₀ (hVanti hk hmem'))

end SGPT.Foundations.Analysis.Pending.QuasiContinuousMajorantFamily
