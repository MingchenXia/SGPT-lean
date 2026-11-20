import SGPT.Unibranch.HironakaG10LocallyAnalyticTrace
import SGPT.Foundations.Analysis.Pending.ConstantRankImage

/-!
# Locally constructible subsets of a complex space and Frisch's Lemma (IV,7)

J. Frisch, *Points de platitude d'un morphisme d'espaces analytiques complexes*, Invent. Math. 4
(1967), p. 132-133 (PDF p. 16-17):

* Déf. (IV,1): a subset of `X` is *constructible* if it lies in the smallest family of subsets stable
  under finite union, finite intersection and complement which contains the analytic subsets;
* Rem. (IV,2): a constructible set is a finite union `⋃ᵢ (Aᵢ - Bᵢ)` of differences of analytic sets;
* Déf. (IV,6): `E` is *locally constructible* if every point has an open neighbourhood `Ω` with
  `Ω ∩ E` constructible in `Ω`;
* **Lemme (IV,7)**: a closed, locally constructible subset is analytic (because
  `closure (A - B)` is analytic for analytic `A`, `B`).

Native form. `IsConstructibleOn X Ω E`: `E ∩ Ω` is a finite union of differences `p.1 \ p.2`
of sets which are analytic on the open set `Ω` (`IsLocallyAnalyticOn X Ω`), i.e. Rem. (IV,2)'s
normal form. This family contains the analytic sets of `Ω` and is closed under finite unions,
finite intersections and complements in `Ω` (`IsConstructibleOn.union`, `.inter`, `.compl`,
`.sdiff`), so it is exactly the Boolean algebra of Déf. (IV,1). `IsLocallyConstructible X E` is
Déf. (IV,6).

Main results:
* `IsConstructibleOn.isLocallyAnalyticOn`: a set constructible on an open `Ω` and relatively
  closed in `Ω` is analytic on `Ω` (local form of Lemme (IV,7));
* **`isAnalyticSubset_of_isClosed_of_isLocallyConstructible`** (Lemme (IV,7)) and
  `isAnalyticSubset_iff_isClosed_and_isLocallyConstructible`.

The only analytic input is `ClosureDifferenceAnalytic.isComplexAnalyticSubset_closure_diff`.
Lane G10FR, run 0081. Blueprint: `hironaka-g10fr-constructible.tex`.
-/

set_option autoImplicit false

open Set TopologicalSpace
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending

namespace SGPT.Unibranch.HironakaG10FrConstructible

open SGPT.Unibranch.SourceReducedComplexSpace SGPT.Unibranch.HironakaG10LocallyAnalyticTrace

noncomputable section

variable {X : SourceReducedComplexSpace}

/-! ## Analytic sets on an open set -/

/-- On an open `Ω`, local analyticity can be read in charts lying inside `Ω`. -/
theorem exists_chart_of_isLocallyAnalyticOn {Ω A : Set X.obj.left} (hΩ : IsOpen Ω)
    (hA : IsLocallyAnalyticOn X Ω A) {x : X.obj.left} (hx : x ∈ Ω) :
    ∃ e : LocalEmbedding X, x ∈ range e.toPoint ∧ range e.toPoint ⊆ Ω ∧
      IsComplexAnalyticSubset (n := e.dim) (Subtype.val '' (e.toPoint ⁻¹' A) : Set e.ambient) := by
  obtain ⟨e, hxe, heΩ, -⟩ := LocalEmbedding.exists_domain x hΩ hx
  exact ⟨e, hxe, heΩ, analytic_image_local_trace hA e heΩ⟩

/-- A trace is the preimage of its image under the inclusion of the carrier. -/
theorem trace_eq_preimage_image (e : LocalEmbedding X) (A : Set X.obj.left) :
    e.toPoint ⁻¹' A =
      (Subtype.val : e.carrier → e.ambient) ⁻¹' (Subtype.val '' (e.toPoint ⁻¹' A)) :=
  (preimage_image_eq _ Subtype.val_injective).symm

/-- Analyticity on `Ω` passes to smaller domains. -/
theorem isLocallyAnalyticOn_mono {Ω Ω' A : Set X.obj.left} (hA : IsLocallyAnalyticOn X Ω A)
    (h : Ω' ⊆ Ω) : IsLocallyAnalyticOn X Ω' A :=
  fun x hx => hA x (h hx)

/-- Analytic sets on `Ω` are stable under intersection. -/
theorem isLocallyAnalyticOn_inter {Ω A B : Set X.obj.left} (hΩ : IsOpen Ω)
    (hA : IsLocallyAnalyticOn X Ω A) (hB : IsLocallyAnalyticOn X Ω B) :
    IsLocallyAnalyticOn X Ω (A ∩ B) := by
  intro x hx
  obtain ⟨e, hxe, heΩ, hSA⟩ := exists_chart_of_isLocallyAnalyticOn hΩ hA hx
  have hSB := analytic_image_local_trace hB e heΩ
  refine ⟨e, hxe, _, hSA.inter hSB, ?_⟩
  simp only [preimage_inter, preimage_image_eq _ Subtype.val_injective]

/-- Analytic sets on `Ω` are stable under union. -/
theorem isLocallyAnalyticOn_union {Ω A B : Set X.obj.left} (hΩ : IsOpen Ω)
    (hA : IsLocallyAnalyticOn X Ω A) (hB : IsLocallyAnalyticOn X Ω B) :
    IsLocallyAnalyticOn X Ω (A ∪ B) := by
  intro x hx
  obtain ⟨e, hxe, heΩ, hSA⟩ := exists_chart_of_isLocallyAnalyticOn hΩ hA hx
  have hSB := analytic_image_local_trace hB e heΩ
  refine ⟨e, hxe, _, ConstantRankImage.IsComplexAnalyticSubset.union hSA hSB, ?_⟩
  simp only [preimage_union, preimage_image_eq _ Subtype.val_injective]

theorem isLocallyAnalyticOn_empty (Ω : Set X.obj.left) : IsLocallyAnalyticOn X Ω ∅ :=
  locallyAnalytic_of_analytic isAnalyticSubset_empty Ω

theorem isLocallyAnalyticOn_univ (Ω : Set X.obj.left) : IsLocallyAnalyticOn X Ω univ :=
  locallyAnalytic_of_analytic isAnalyticSubset_univ Ω

/-! ## Constructible sets on an open set (Frisch Déf. (IV,1), Rem. (IV,2)) -/

/-- **Constructible on `Ω`** (Frisch Déf. (IV,1) in the normal form of Rem. (IV,2)): `E ∩ Ω` is a
finite union of differences `A \ B` of sets analytic on `Ω`. -/
def IsConstructibleOn (X : SourceReducedComplexSpace) (Ω E : Set X.obj.left) : Prop :=
  ∃ P : Finset (Set X.obj.left × Set X.obj.left),
    (∀ p ∈ P, IsLocallyAnalyticOn X Ω p.1 ∧ IsLocallyAnalyticOn X Ω p.2) ∧
      E ∩ Ω = (⋃ p ∈ P, p.1 \ p.2) ∩ Ω

/-- **Locally constructible** (Frisch Déf. (IV,6)): every point has an open neighbourhood on which
the set is constructible. -/
def IsLocallyConstructible (X : SourceReducedComplexSpace) (E : Set X.obj.left) : Prop :=
  ∀ x : X.obj.left, ∃ Ω : Set X.obj.left, IsOpen Ω ∧ x ∈ Ω ∧ IsConstructibleOn X Ω E

namespace IsConstructibleOn

variable {Ω E F : Set X.obj.left}

/-- Constructibility on `Ω` only depends on the trace on `Ω`. -/
theorem congr (h : IsConstructibleOn X Ω E) (hEF : E ∩ Ω = F ∩ Ω) : IsConstructibleOn X Ω F := by
  obtain ⟨P, hP, hE⟩ := h
  exact ⟨P, hP, hEF ▸ hE⟩

/-- Constructibility passes to smaller open sets. -/
theorem mono (h : IsConstructibleOn X Ω E) {Ω' : Set X.obj.left} (hΩ' : Ω' ⊆ Ω) :
    IsConstructibleOn X Ω' E := by
  obtain ⟨P, hP, hE⟩ := h
  refine ⟨P, fun p hp => ⟨isLocallyAnalyticOn_mono (hP p hp).1 hΩ',
    isLocallyAnalyticOn_mono (hP p hp).2 hΩ'⟩, ?_⟩
  calc E ∩ Ω' = E ∩ Ω ∩ Ω' := by rw [inter_assoc, inter_eq_right.mpr hΩ']
    _ = (⋃ p ∈ P, p.1 \ p.2) ∩ Ω ∩ Ω' := by rw [hE]
    _ = (⋃ p ∈ P, p.1 \ p.2) ∩ Ω' := by rw [inter_assoc, inter_eq_right.mpr hΩ']

/-- Analytic sets on `Ω` are constructible on `Ω`. -/
theorem of_isLocallyAnalyticOn (hE : IsLocallyAnalyticOn X Ω E) : IsConstructibleOn X Ω E := by
  classical
  refine ⟨{(E, ∅)}, ?_, ?_⟩
  · intro p hp
    rw [Finset.mem_singleton] at hp
    subst hp
    exact ⟨hE, isLocallyAnalyticOn_empty Ω⟩
  · simp

/-- Analytic subsets of `X` are constructible on every open set. -/
theorem of_isAnalyticSubset (hE : X.IsAnalyticSubset E) : IsConstructibleOn X Ω E :=
  of_isLocallyAnalyticOn (locallyAnalytic_of_analytic hE Ω)

theorem empty : IsConstructibleOn X Ω ∅ := of_isAnalyticSubset isAnalyticSubset_empty

theorem univ : IsConstructibleOn X Ω Set.univ := of_isAnalyticSubset isAnalyticSubset_univ

/-- Finite unions. -/
theorem union (hE : IsConstructibleOn X Ω E) (hF : IsConstructibleOn X Ω F) :
    IsConstructibleOn X Ω (E ∪ F) := by
  classical
  obtain ⟨P, hP, hPE⟩ := hE
  obtain ⟨Q, hQ, hQF⟩ := hF
  refine ⟨P ∪ Q, fun p hp => ?_, ?_⟩
  · rcases Finset.mem_union.mp hp with h | h
    · exact hP p h
    · exact hQ p h
  · rw [Finset.set_biUnion_union, union_inter_distrib_right, union_inter_distrib_right, hPE, hQF]

/-- Finite intersections. -/
theorem inter (hΩ : IsOpen Ω) (hE : IsConstructibleOn X Ω E) (hF : IsConstructibleOn X Ω F) :
    IsConstructibleOn X Ω (E ∩ F) := by
  classical
  obtain ⟨P, hP, hPE⟩ := hE
  obtain ⟨Q, hQ, hQF⟩ := hF
  refine ⟨(P ×ˢ Q).image (fun pq => (pq.1.1 ∩ pq.2.1, pq.1.2 ∪ pq.2.2)), ?_, ?_⟩
  · intro r hr
    obtain ⟨⟨p, q⟩, hpq, rfl⟩ := Finset.mem_image.mp hr
    obtain ⟨hp, hq⟩ := Finset.mem_product.mp hpq
    exact ⟨isLocallyAnalyticOn_inter hΩ (hP p hp).1 (hQ q hq).1,
      isLocallyAnalyticOn_union hΩ (hP p hp).2 (hQ q hq).2⟩
  · have key : (⋃ r ∈ (P ×ˢ Q).image (fun pq : (Set X.obj.left × Set X.obj.left) ×
          (Set X.obj.left × Set X.obj.left) => (pq.1.1 ∩ pq.2.1, pq.1.2 ∪ pq.2.2)), r.1 \ r.2) =
        (⋃ p ∈ P, p.1 \ p.2) ∩ ⋃ q ∈ Q, q.1 \ q.2 := by
      ext z
      simp only [Finset.set_biUnion_finset_image, mem_iUnion, mem_inter_iff, mem_sdiff,
        mem_union, Finset.mem_product, exists_prop, Prod.exists]
      constructor
      · rintro ⟨p₁, p₂, q₁, q₂, ⟨hp, hq⟩, ⟨hz₁, hz₂⟩, hn⟩
        exact ⟨⟨p₁, p₂, hp, hz₁, fun h => hn (Or.inl h)⟩,
          ⟨q₁, q₂, hq, hz₂, fun h => hn (Or.inr h)⟩⟩
      · rintro ⟨⟨p₁, p₂, hp, hz₁, hn₁⟩, ⟨q₁, q₂, hq, hz₂, hn₂⟩⟩
        exact ⟨p₁, p₂, q₁, q₂, ⟨hp, hq⟩, ⟨hz₁, hz₂⟩, fun h => h.elim hn₁ hn₂⟩
    rw [key]
    calc E ∩ F ∩ Ω = (E ∩ Ω) ∩ (F ∩ Ω) := by
          rw [inter_inter_inter_comm, inter_self]
      _ = ((⋃ p ∈ P, p.1 \ p.2) ∩ Ω) ∩ ((⋃ q ∈ Q, q.1 \ q.2) ∩ Ω) := by rw [hPE, hQF]
      _ = _ := by rw [inter_inter_inter_comm, inter_self]

/-- The complement of a finite union of differences of analytic sets is constructible. -/
theorem compl_biUnion (hΩ : IsOpen Ω) (P : Finset (Set X.obj.left × Set X.obj.left))
    (hP : ∀ p ∈ P, IsLocallyAnalyticOn X Ω p.1 ∧ IsLocallyAnalyticOn X Ω p.2) :
    IsConstructibleOn X Ω (⋃ p ∈ P, p.1 \ p.2)ᶜ := by
  classical
  induction P using Finset.induction_on with
  | empty => simpa using (univ : IsConstructibleOn X Ω Set.univ)
  | insert q P hq ih =>
    rw [Finset.set_biUnion_insert, compl_union]
    have hq' := hP q (Finset.mem_insert_self q P)
    have hrest := ih fun p hp => hP p (Finset.mem_insert_of_mem hp)
    have hdq : IsConstructibleOn X Ω (q.1 \ q.2)ᶜ := by
      have h1 : IsConstructibleOn X Ω (Set.univ \ q.1) := by
        refine ⟨{(Set.univ, q.1)}, ?_, by simp⟩
        intro p hp
        rw [Finset.mem_singleton] at hp
        subst hp
        exact ⟨isLocallyAnalyticOn_univ Ω, hq'.1⟩
      have h2 := of_isLocallyAnalyticOn hq'.2
      refine (h1.union h2).congr ?_
      congr 1
      ext z
      simp only [mem_union, mem_sdiff, mem_univ, true_and, mem_compl_iff, not_and, not_not]
      tauto
    exact hdq.inter hΩ hrest

/-- Complements in `Ω`. -/
theorem compl (hΩ : IsOpen Ω) (hE : IsConstructibleOn X Ω E) : IsConstructibleOn X Ω Eᶜ := by
  obtain ⟨P, hP, hPE⟩ := hE
  refine (compl_biUnion hΩ P hP).congr ?_
  ext z
  have h := Set.ext_iff.mp hPE z
  simp only [mem_inter_iff, mem_compl_iff] at h ⊢
  tauto

/-- Differences. -/
theorem sdiff (hΩ : IsOpen Ω) (hE : IsConstructibleOn X Ω E) (hF : IsConstructibleOn X Ω F) :
    IsConstructibleOn X Ω (E \ F) :=
  hE.inter hΩ (hF.compl hΩ)

/-- **Frisch Lemme (IV,7), local form.** A set which is constructible on an open `Ω` and
relatively closed in `Ω` is analytic on `Ω`. -/
theorem isLocallyAnalyticOn (hΩ : IsOpen Ω) (hE : IsConstructibleOn X Ω E)
    (hcl : closure (E ∩ Ω) ∩ Ω ⊆ E) : IsLocallyAnalyticOn X Ω E := by
  classical
  obtain ⟨P, hP, hPE⟩ := hE
  intro x hx
  obtain ⟨e, hxe, heΩ, -⟩ := LocalEmbedding.exists_domain x hΩ hx
  -- ambient images of the traces of the analytic pieces
  let SA : Set X.obj.left × Set X.obj.left → Set e.ambient :=
    fun p => Subtype.val '' (e.toPoint ⁻¹' p.1)
  let SB : Set X.obj.left × Set X.obj.left → Set e.ambient :=
    fun p => Subtype.val '' (e.toPoint ⁻¹' p.2)
  have hSA : ∀ p ∈ P, IsComplexAnalyticSubset (n := e.dim) (SA p) := fun p hp =>
    analytic_image_local_trace (hP p hp).1 e heΩ
  have hSB : ∀ p ∈ P, IsComplexAnalyticSubset (n := e.dim) (SB p) := fun p hp =>
    analytic_image_local_trace (hP p hp).2 e heΩ
  refine ⟨e, hxe, ⋃ p ∈ P, closure (SA p \ SB p),
    ConstantRankImage.isComplexAnalyticSubset_biUnion P fun p hp =>
      ClosureDifferenceAnalytic.isComplexAnalyticSubset_closure_diff (hSA p hp) (hSB p hp), ?_⟩
  have hrange : e.toPoint ⁻¹' Ω = Set.univ :=
    eq_univ_of_forall fun c => heΩ ⟨c, rfl⟩
  -- the trace of `E` is the trace of the finite union of differences
  have htrace : e.toPoint ⁻¹' E = ⋃ p ∈ P, (e.toPoint ⁻¹' p.1 \ e.toPoint ⁻¹' p.2) := by
    have h1 : e.toPoint ⁻¹' E = e.toPoint ⁻¹' (E ∩ Ω) := by
      rw [preimage_inter, hrange, inter_univ]
    rw [h1, hPE, preimage_inter, hrange, inter_univ, preimage_iUnion₂]
    simp only [preimage_sdiff]
  -- the trace of `E` is closed in the carrier
  have hclosed : closure (e.toPoint ⁻¹' E) ⊆ e.toPoint ⁻¹' E := by
    have h1 : closure (e.toPoint ⁻¹' E) ⊆ closure (e.toPoint ⁻¹' (E ∩ Ω)) := by
      apply closure_mono
      intro c hc
      exact ⟨hc, heΩ ⟨c, rfl⟩⟩
    refine h1.trans ?_
    rw [← e.isOpenEmbedding_toPoint.isOpenMap.preimage_closure_eq_closure_preimage
      e.isOpenEmbedding_toPoint.continuous]
    intro c hc
    exact hcl ⟨hc, heΩ ⟨c, rfl⟩⟩
  have hEq : e.toPoint ⁻¹' E = closure (e.toPoint ⁻¹' E) :=
    Subset.antisymm subset_closure hclosed
  rw [hEq, htrace, Finset.closure_biUnion, preimage_iUnion₂]
  refine iUnion₂_congr fun p _ => ?_
  rw [Topology.IsEmbedding.subtypeVal.closure_eq_preimage_closure_image,
    Set.image_sdiff Subtype.val_injective]

end IsConstructibleOn

/-! ## Locally constructible sets and Lemme (IV,7) -/

namespace IsLocallyConstructible

variable {E F : Set X.obj.left}

theorem of_isAnalyticSubset (hE : X.IsAnalyticSubset E) : IsLocallyConstructible X E :=
  fun _ => ⟨Set.univ, isOpen_univ, mem_univ _, IsConstructibleOn.of_isAnalyticSubset hE⟩

theorem union (hE : IsLocallyConstructible X E) (hF : IsLocallyConstructible X F) :
    IsLocallyConstructible X (E ∪ F) := by
  intro x
  obtain ⟨Ω, hΩ, hx, h⟩ := hE x
  obtain ⟨Ω', hΩ', hx', h'⟩ := hF x
  exact ⟨Ω ∩ Ω', hΩ.inter hΩ', ⟨hx, hx'⟩,
    (h.mono inter_subset_left).union (h'.mono inter_subset_right)⟩

theorem inter (hE : IsLocallyConstructible X E) (hF : IsLocallyConstructible X F) :
    IsLocallyConstructible X (E ∩ F) := by
  intro x
  obtain ⟨Ω, hΩ, hx, h⟩ := hE x
  obtain ⟨Ω', hΩ', hx', h'⟩ := hF x
  exact ⟨Ω ∩ Ω', hΩ.inter hΩ', ⟨hx, hx'⟩,
    (h.mono inter_subset_left).inter (hΩ.inter hΩ') (h'.mono inter_subset_right)⟩

theorem compl (hE : IsLocallyConstructible X E) : IsLocallyConstructible X Eᶜ := by
  intro x
  obtain ⟨Ω, hΩ, hx, h⟩ := hE x
  exact ⟨Ω, hΩ, hx, h.compl hΩ⟩

theorem sdiff (hE : IsLocallyConstructible X E) (hF : IsLocallyConstructible X F) :
    IsLocallyConstructible X (E \ F) :=
  hE.inter hF.compl

end IsLocallyConstructible

/-- **Frisch, Lemme (IV,7)** (p. 133): a closed, locally constructible subset of a complex space is
analytic. -/
theorem isAnalyticSubset_of_isClosed_of_isLocallyConstructible {E : Set X.obj.left}
    (hcl : IsClosed E) (hE : IsLocallyConstructible X E) : X.IsAnalyticSubset E := by
  intro x
  obtain ⟨Ω, hΩ, hx, h⟩ := hE x
  have hloc : IsLocallyAnalyticOn X Ω E := h.isLocallyAnalyticOn hΩ
    (fun z hz => hcl.closure_subset (closure_mono inter_subset_left hz.1))
  exact hloc x hx

/-- Analytic subsets are exactly the closed locally constructible subsets. -/
theorem isAnalyticSubset_iff_isClosed_and_isLocallyConstructible {E : Set X.obj.left} :
    X.IsAnalyticSubset E ↔ IsClosed E ∧ IsLocallyConstructible X E :=
  ⟨fun h => ⟨h.isClosed, IsLocallyConstructible.of_isAnalyticSubset h⟩,
    fun h => isAnalyticSubset_of_isClosed_of_isLocallyConstructible h.1 h.2⟩

end
end SGPT.Unibranch.HironakaG10FrConstructible
