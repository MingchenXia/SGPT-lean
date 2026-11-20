import SGPT.Unibranch.HironakaG10RdLemma454
import SGPT.Unibranch.HironakaG10RdSumStep
import SGPT.Unibranch.HironakaG10RdTopIndex
import SGPT.Unibranch.HironakaG10TmStratumBoundaryAt

/-!
# The `D_β` step at Hironaka's index `k` and its Lemma 4.5.4

Plan items G10-03-07.c/08 and the `i = 0` half of L4 (`hDβ` of `HironakaG10RdMacroStep`).  Source: H. Hironaka,
*Flattening theorem in complex-analytic geometry*, Amer. J. Math. 97 (1975), Lemmas 4.5.2–4.5.4 and the choice of
`D_β`, printed pp. 541–543; for the index `0`, the end of the proof of `II_{n-1} ⇒ I_n`, p. 544: "As i = 0,
s_i'' = B'. So the conclusion of (4.5.4) is exactly what is claimed in Theorem I_n."

* `mem_closure_diff_iff_of_common_support` — near a common support point two local flatteners give the same
  boundary closure (Hironaka 4.5.2: "Z_p and Z coincide within some neighborhood of y");
* **`exists_Dβ_permStep`** — at any index `k` (including `0`), from the centre
  `HironakaG10TmStratumBoundaryAt.exists_source_large_omega_sumCentreAt` and Lemma 4.4.5 for sum centres
  (`hT`, plan item G10-03-09): a permissible step whose centre is a sum centre for a positive exponent, with support
  exactly `C_k ∩ E_k`, after which every transported tracked support meets the strict transform of the stratum
  `s_k` relatively openly (Lemma 4.5.4);
* **`exists_Dβ_permStep_openTracked`** — at index `0`: the next datum satisfies `OpenTracked` (Theorem `I_n`'s
  conclusion for this step).

No named input is introduced.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Set Filter TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology

namespace SGPT.Unibranch.HironakaG10RdDbetaStep

open SGPT.Foundations.Analysis.Pending HironakaSingularModuleSheafStalk
open SGPT.Unibranch.HironakaG10HirLocalFlattener
  SGPT.Unibranch.HironakaG10HirGermFlattener
  SGPT.Unibranch.HironakaG10LocallyAnalyticTrace
  SGPT.Unibranch.HironakaG10RelativeNonflatStrata
  SGPT.Unibranch.HironakaG10SourceCSet
  SGPT.Unibranch.HironakaG10ChowTrackedDatum
  SGPT.Unibranch.HironakaG10ChowFlatteningDriver
  SGPT.Unibranch.HironakaG10ChowCentreMachine
  SGPT.Unibranch.HironakaG10ChowStrictFlatLocus
  SGPT.Unibranch.HironakaG10TmStratumBoundaryAt
  SGPT.Unibranch.HironakaG10RdPermRun
  SGPT.Unibranch.HironakaG10RdTopIndex
  SGPT.Unibranch.HironakaG10RdSumStep
  SGPT.Unibranch.HironakaG10RdLemma454
  SGPT.Unibranch.EmbeddedIdealBlowupNonunitLocus

noncomputable section

section Boundary

variable {X Y : SourceReducedComplexSpace} {f : Y ⟶ X}

theorem mem_closure_diff_of_common_support (Z₁ Z₂ : LocalFlattener f) (S : Set X.obj.left)
    {y : X.obj.left} (h₁ : y ∈ Z₁.support) (h₂ : y ∈ Z₂.support)
    (hy : y ∈ closure ((S ∩ Z₁.V) \ Z₁.support)) : y ∈ closure ((S ∩ Z₂.V) \ Z₂.support) := by
  have hN : ∀ᶠ z in 𝓝 y, z ∈ Z₁.V ∧ z ∈ Z₂.V ∧ Z₁.H z = Z₂.H z := by
    filter_upwards [Z₁.isOpen.mem_nhds h₁.1, Z₂.isOpen.mem_nhds h₂.1, Z₁.eventually_eq Z₂ h₁ h₂]
      with z hz1 hz2 hz3
    exact ⟨hz1, hz2, hz3⟩
  rw [mem_closure_iff_nhds] at hy ⊢
  intro t ht
  obtain ⟨z, ⟨hzt, hz1, hz2, hzH⟩, ⟨hzS, -⟩, hzZ⟩ := hy _ (inter_mem ht hN)
  refine ⟨z, hzt, ⟨hzS, hz2⟩, fun hz => hzZ ⟨hz1, ?_⟩⟩
  rw [hzH]
  exact hz.2

/-- Near a common support point two local flatteners give the same boundary closure. -/
theorem mem_closure_diff_iff_of_common_support (Z₁ Z₂ : LocalFlattener f) (S : Set X.obj.left)
    {y : X.obj.left} (h₁ : y ∈ Z₁.support) (h₂ : y ∈ Z₂.support) :
    y ∈ closure ((S ∩ Z₁.V) \ Z₁.support) ↔ y ∈ closure ((S ∩ Z₂.V) \ Z₂.support) :=
  ⟨mem_closure_diff_of_common_support Z₁ Z₂ S h₁ h₂, mem_closure_diff_of_common_support Z₂ Z₁ S h₂ h₁⟩

end Boundary

variable {s : Stage} {q : ℕ}

/-- **The `D_β` step at index `k`** (Hironaka pp. 541–543): a permissible step whose centre is a sum centre for
a positive exponent with support `C_k ∩ E_k`, after which every transported tracked support meets the strict
transform of `s_k` relatively openly (Lemma 4.5.4). -/
theorem exists_Dβ_permStep [CompactSpace s.X.obj.left] (R : FDatum s q)
    (Zaux : LocalFlattener s.f) (k : ℕ)
    (hS : ∀ p, IsLocallyAnalyticOn s.X (R.Z p).V (strata s.f R.B k))
    (hSaux : IsLocallyAnalyticOn s.X Zaux.V (strata s.f R.B k))
    (hSc : IsClosed (strata s.f R.B k))
    (N : ℕ) (hN : strata s.f R.B N = ∅)
    (hcover : ∀ j x, x ∈ strata s.f R.B j → ∃ C, IsStratumComponent s.f R.B j C ∧ x ∈ C)
    (hfinite : (selectedHigherComponents s.f R.B (fun p => (R.Z p).support) k).Finite)
    (hmax : ∀ jC ∈ badComponents s.f R.B (fun p => (R.Z p).support), jC.1 ≤ k)
    (hC : Cset s.f R.B (fun p => (R.Z p).support) k ⊆ Zaux.support)
    (hdense : Dense (nonflatImage s.f)ᶜ)
    (hT : ∀ (c : AdmissibleCentre s.f) (β : ℕ), IsSumCentreFor c.B c.b s.f β →
      (∀ x ∈ nonunitLocus c.B c.b, FlatOverAt s.f x (centreIdeal c x)) →
      ∃ Z' : Fin q → LocalFlattener (nextWith s c).f,
        ∀ p, (Z' p).support = (R.trackedTransport c).Z p) :
    ∃ st : PermStep R, (∃ β, β ≠ 0 ∧ IsSumCentreFor st.c.B st.c.b s.f β) ∧
      nonunitLocus st.c.B st.c.b = Cset s.f R.B (fun p => (R.Z p).support) k ∩
        stratumBoundaryAt s.f R.B Zaux.V Zaux.support k ∧
      ∀ p, IsRelOpen (strictSet s st.c (strata s.f R.B k)) (st.next.Z p).support := by
  obtain ⟨ω₀, hω⟩ := exists_source_large_omega_sumCentreAt s.f R.B R.Z Zaux k hS hSaux N hN hcover
    hfinite hmax hC hdense
  obtain ⟨_, _, -, -, -, α, hα⟩ := hω ω₀ le_rfl
  obtain ⟨c, hcQ, hsum, hflat, -, hagreeEv⟩ := hα (max α 1) (le_max_left _ _)
  have hβ : max α 1 ≠ 0 := by have := le_max_right α 1; omega
  have hsub : nonunitLocus c.B c.b ⊆ relNonflat s.f R.B := by
    rw [hcQ]
    exact inter_subset_left.trans (cset_subset_relNonflat _)
  obtain ⟨Z', hZ'⟩ := hT c _ hsum hflat
  refine ⟨PermStep.ofSumCentre R c _ hsum hflat hsub Z' hZ', ⟨_, hβ, hsum⟩, hcQ, fun p => ?_⟩
  refine isRelOpen_strictSet_of_sumCentre s c (R.Z p) hSc (max α 1) hβ ?_ ?_ (Z' p) ?_
  · -- the tracked boundary lies in the centre
    intro y hy
    have hyC := tracked_boundary_subset_csetAt s.f R.B R.Z k hS N hN hcover p hy
    have hyaux : y ∈ Zaux.support := hC hyC
    rw [hcQ]
    exact ⟨hyC, (mem_closure_diff_iff_of_common_support (R.Z p) Zaux _ hy.2 hyaux).mp hy.1, hyaux⟩
  · -- the centre formula at the centre points of the tracked support
    intro y hyD hyZ
    rw [hcQ] at hyD
    have hyaux : y ∈ Zaux.support := hyD.2.2
    have hyE : y ∈ stratumBoundaryAt s.f R.B (R.Z p).V (R.Z p).support k :=
      ⟨(mem_closure_diff_iff_of_common_support Zaux (R.Z p) _ hyaux hyZ).mp hyD.2.1, hyZ⟩
    exact (hagreeEv p y hyE).self_of_nhds
  · intro x'
    rw [hZ' p]
    rfl

/-- **At Hironaka's index `0` the `D_β` step ends with open tracked supports** (p. 544). -/
theorem exists_Dβ_permStep_openTracked [CompactSpace s.X.obj.left] (R : FDatum s q)
    (Zaux : LocalFlattener s.f)
    (hS : ∀ p, IsLocallyAnalyticOn s.X (R.Z p).V R.B)
    (hSaux : IsLocallyAnalyticOn s.X Zaux.V R.B)
    (N : ℕ) (hN : strata s.f R.B N = ∅)
    (hcover : ∀ j x, x ∈ strata s.f R.B j → ∃ C, IsStratumComponent s.f R.B j C ∧ x ∈ C)
    (hfinite : (selectedHigherComponents s.f R.B (fun p => (R.Z p).support) 0).Finite)
    (hmax : ∀ jC ∈ badComponents s.f R.B (fun p => (R.Z p).support), jC.1 ≤ 0)
    (hC : Cset s.f R.B (fun p => (R.Z p).support) 0 ⊆ Zaux.support)
    (hdense : Dense (nonflatImage s.f)ᶜ)
    (hT : ∀ (c : AdmissibleCentre s.f) (β : ℕ), IsSumCentreFor c.B c.b s.f β →
      (∀ x ∈ nonunitLocus c.B c.b, FlatOverAt s.f x (centreIdeal c x)) →
      ∃ Z' : Fin q → LocalFlattener (nextWith s c).f,
        ∀ p, (Z' p).support = (R.trackedTransport c).Z p) :
    ∃ st : PermStep R, OpenTracked st.next := by
  obtain ⟨st, -, -, hopen⟩ := exists_Dβ_permStep R Zaux 0 hS hSaux R.closed N hN hcover hfinite hmax
    hC hdense hT
  refine ⟨st, fun p => ?_⟩
  rw [st.next_B]
  exact hopen p

end

end SGPT.Unibranch.HironakaG10RdDbetaStep
