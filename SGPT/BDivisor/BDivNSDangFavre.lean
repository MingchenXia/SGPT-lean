import SGPT.Hodge.SourceNefMixedOrder
import SGPT.Hodge.SourceNefCartierOrder
import SGPT.Hodge.SourceCartierSequence
import SGPT.Hodge.SourceNefIntersection

/-!
# The intersection of nef b-divisors is the Dang--Favre intersection

Source `rmk:bdiv:L749` (`chapter_bdiv.tex`): the algebraic nef b-divisors and their
intersection theory are due to Dang--Favre; "it is a straightforward application of the
results proved in this section that our transcendental intersection theory coincides with
theirs in the algebraic setting".

Dang--Favre define the intersection of nef b-divisor classes from the classical intersection
numbers of nef Cartier b-divisor classes, computed on a model where all of them are realized,
by passing to decreasing limits (equivalently, by taking the infimum over nef Cartier
majorants). This file proves the transcendental content of the comparison for the
intersection product of `def:DF_ext` (`SourceNefIntersectionDraft.nefIntersection`) over a
compact Kähler manifold `X` of positive dimension `m + 1`:

* `CommonNefRealization`: a realization of a tuple of nef Cartier b-divisors by nef smooth
  forms on one blow-up model, and its classical intersection number
  `CommonNefRealization.intersection` (the top integral of the realizing forms);
  `CommonNefRealization.intersection_eq` identifies it with the b-divisor product, so it does
  not depend on the realization (`CommonNefRealization.intersection_congr`);
* `tendsto_intersection_of_antitone`: for **every** decreasing net of nef Cartier b-divisors
  converging to nef b-divisors, the classical intersection numbers of the approximants converge
  to the b-divisor product (the Dang--Favre recipe computes our product);
* `exists_antitone_cartier_approximation`: such decreasing approximating sequences, with their
  common realizations, exist for every nef tuple;
* `nefIntersection_toReal_eq_sInf`: the product is the infimum of the classical intersection
  numbers of nef Cartier majorants;
* `eq_nefIntersection_of_cartier_of_antitone`: uniqueness: every real function on tuples of
  b-divisors that equals the classical intersection number on nef Cartier tuples and is
  continuous along decreasing sequences of nef Cartier tuples coincides with the product on all
  nef tuples.

The identification of the *algebraic* objects of Dang--Favre (b-divisor classes in the
Néron--Severi spaces of the models of a projective variety, the cycle class map to
`H^{1,1}`, and their algebraic decreasing approximations) is not formalized here.
-/

set_option autoImplicit false

noncomputable section

universe u

namespace SGPT.BDivisor.DangFavre

open Filter
open scoped Topology ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses
  SGPT.Hodge.BDivChain.NativeDraft SGPT.Hodge.BDivChain.NativeDraft.VolumeNetDraft
  SGPT.Hodge.BDivChain.SourceNefIntersectionDraft SGPT.Hodge.BDivChain.SourceMixedOrderDraft
  SGPT.Hodge.BDivChain.SourceCartierSequenceDraft

variable {m : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (m + 1)) X] [IsComplexManifold (m + 1) X]
  [CompactSpace X] [ConnectedSpace X] [MeasurableSpace X] [BorelSpace X]

local notation "Sys" => ModelSystem.blowup (m + 1) X

/-- A common nef realization of a tuple `C` of b-divisors over `X`: one blow-up model `Y` of
`X`, a Kähler form on `Y`, and closed real `(1,1)`-forms on `Y`, nef with respect to that
Kähler form, whose classes realize the `C i` (`def:bdiv:L116`, `def:nefCar`). -/
structure CommonNefRealization (C : Fin (m + 1) → WeilFamilyAny Sys) where
  /-- The model on which all the b-divisors are realized. -/
  model : (ModelSystem.blowup (m + 1) X).Model
  /-- A Kähler form on the model. -/
  kahler : KahlerBackground (m + 1) model.1.carrier
  /-- The realizing forms. -/
  form : Fin (m + 1) → ClosedRealOneOneForm (m + 1) model.1.carrier
  /-- The class of `form i` realizes `C i`. -/
  realizes : ∀ i, IsRealizationAny (C i) model (RealBottChern.ofRepresentative (form i))
  /-- The realizing forms are nef. -/
  nef : ∀ i, NefWithRespectTo kahler (form i)

namespace CommonNefRealization

/-- The classical intersection number `∫_Y θ_1 ∧ ⋯ ∧ θ_{m+1}` of a common nef realization. -/
def intersection {C : Fin (m + 1) → WeilFamilyAny Sys} (r : CommonNefRealization C) : ℝ :=
  modelSlotIntegral r.model r.kahler r.form

omit [ConnectedSpace X] [MeasurableSpace X] [BorelSpace X] in
/-- The members of a tuple with a common nef realization are nef Cartier b-divisors. -/
theorem isNefCartierAny {C : Fin (m + 1) → WeilFamilyAny Sys} (r : CommonNefRealization C)
    (i : Fin (m + 1)) :
    IsNefCartierAny (C i) :=
  ⟨r.model, _, r.realizes i, r.kahler, r.nef i⟩

/-- The b-divisor intersection product of a nef Cartier tuple is the classical intersection
number of any common nef realization. -/
theorem intersection_eq (ω : KahlerBackground (m + 1) X) {C : Fin (m + 1) → WeilFamilyAny Sys}
    (r : CommonNefRealization C) :
    r.intersection = (nefIntersection C).toReal :=
  (nefIntersection_of_common_nef_realization ω C r.model r.kahler r.form r.realizes r.nef).symm

/-- The classical intersection number does not depend on the common realization. -/
theorem intersection_congr (ω : KahlerBackground (m + 1) X) {C : Fin (m + 1) → WeilFamilyAny Sys}
    (r r' : CommonNefRealization C) : r.intersection = r'.intersection := by
  rw [r.intersection_eq ω, r'.intersection_eq ω]

end CommonNefRealization

omit [ConnectedSpace X] [MeasurableSpace X] [BorelSpace X] in
/-- Every tuple of nef Cartier b-divisors has a common nef realization. -/
theorem nonempty_commonNefRealization (ω : KahlerBackground (m + 1) X)
    (C : Fin (m + 1) → WeilFamilyAny Sys) (hC : ∀ i, IsNefCartierAny (C i)) :
    Nonempty (CommonNefRealization C) := by
  obtain ⟨π, κ, θ, hr, hn⟩ := exists_common_nef_realization ω C hC
  exact ⟨⟨π, κ, θ, hr, hn⟩⟩

/-- **The Dang--Favre limit formula.** Let `(C i j)_j` be decreasing nets of nef Cartier
b-divisors converging to `D i`, and choose common nef realizations of the tuples
`(C i j)_i`. Then the `D i` are nef and the classical intersection numbers of the realizations
converge to the b-divisor intersection product `(D_1, …, D_{m+1})`. -/
theorem tendsto_intersection_of_antitone (ω : KahlerBackground (m + 1) X)
    {J : Type*} [Preorder J] [IsDirected J (· ≤ ·)] [Nonempty J]
    (C : Fin (m + 1) → J → WeilFamilyAny Sys) (D : Fin (m + 1) → WeilFamilyAny Sys)
    (hC : ∀ i j, IsNefCartierAny (C i j))
    (ha : ∀ i j k, j ≤ k → LEAny (C i k) (C i j))
    (hc : ∀ i, ConvergesAny atTop (C i) (D i))
    (r : ∀ j, CommonNefRealization (fun i => C i j)) :
    (∀ i, IsNefAny (D i)) ∧
      Tendsto (fun j => (r j).intersection) atTop (𝓝 (nefIntersection D).toReal) := by
  obtain ⟨hD, ht⟩ := source_DFdecnet ω C D (fun i j => isNefAny_of_isNefCartierAny (hC i j)) ha hc
  refine ⟨hD, ?_⟩
  have hreal := (ENNReal.tendsto_toReal (nefIntersection_lt_top D).ne).comp ht
  refine hreal.congr' (Eventually.of_forall fun j => ?_)
  exact ((r j).intersection_eq ω).symm

/-- Every tuple of nef b-divisors is approximated, as in the Dang--Favre construction, by
decreasing sequences of nef Cartier b-divisors with common nef realizations, along which the
classical intersection numbers converge to the b-divisor product. -/
theorem exists_antitone_cartier_approximation (ω : KahlerBackground (m + 1) X)
    (D : Fin (m + 1) → WeilFamilyAny Sys) (hD : ∀ i, IsNefAny (D i)) :
    ∃ (C : Fin (m + 1) → ℕ → WeilFamilyAny Sys)
      (r : ∀ j, CommonNefRealization (fun i => C i j)),
      (∀ i j, IsNefCartierAny (C i j)) ∧ (∀ i j k, j ≤ k → LEAny (C i k) (C i j)) ∧
        (∀ i, ConvergesAny atTop (C i) (D i)) ∧
          Tendsto (fun j => (r j).intersection) atTop (𝓝 (nefIntersection D).toReal) := by
  choose C hC ha hc using fun i => source_nef_Cartierseq ω (D i) (hD i)
  have hCart : ∀ i j, IsNefCartierAny (C i j) := fun i j => (hC i j).1
  have r : ∀ j, CommonNefRealization (fun i => C i j) := fun j =>
    Classical.choice (nonempty_commonNefRealization ω (fun i => C i j) (fun i => hCart i j))
  exact ⟨C, r, hCart, ha, hc, (tendsto_intersection_of_antitone ω C D hCart ha hc r).2⟩

/-- **The Dang--Favre infimum formula.** The intersection product of nef b-divisors is the
infimum of the classical intersection numbers of nef Cartier b-divisors dominating them. -/
theorem nefIntersection_toReal_eq_sInf (ω : KahlerBackground (m + 1) X)
    (D : Fin (m + 1) → WeilFamilyAny Sys) (hD : ∀ i, IsNefAny (D i)) :
    (nefIntersection D).toReal = sInf {x : ℝ | ∃ (C : Fin (m + 1) → WeilFamilyAny Sys)
      (r : CommonNefRealization C), (∀ i, LEAny (D i) (C i)) ∧ x = r.intersection} := by
  set S := {x : ℝ | ∃ (C : Fin (m + 1) → WeilFamilyAny Sys)
      (r : CommonNefRealization C), (∀ i, LEAny (D i) (C i)) ∧ x = r.intersection}
  have hlow : ∀ x ∈ S, (nefIntersection D).toReal ≤ x := by
    rintro x ⟨C, r, hDC, rfl⟩
    rw [r.intersection_eq ω]
    exact ENNReal.toReal_mono (nefIntersection_lt_top C).ne
      (source_nefIntersection_mono ω D C hD
        (fun i => isNefAny_of_isNefCartierAny (r.isNefCartierAny i)) hDC)
  obtain ⟨C, r, -, ha, hc, ht⟩ := exists_antitone_cartier_approximation ω D hD
  have hmem : ∀ j, (r j).intersection ∈ S := fun j =>
    ⟨fun i => C i j, r j, fun i => leAny_of_antitone_converges ω (C i) (D i)
      (fun j k hjk => ha i j k hjk) (hc i) j, rfl⟩
  have hglb : IsGLB S (nefIntersection D).toReal :=
    isGLB_of_tendsto_atTop' hlow hmem ht
  exact (hglb.csInf_eq ⟨_, hmem 0⟩).symm
where
  /-- A lower bound which is a limit of members of the set is its greatest lower bound. -/
  isGLB_of_tendsto_atTop' {S : Set ℝ} {a : ℝ} {u : ℕ → ℝ} (hlow : ∀ x ∈ S, a ≤ x)
      (hmem : ∀ j, u j ∈ S) (ht : Tendsto u atTop (𝓝 a)) : IsGLB S a := by
    refine ⟨hlow, fun b hb => ?_⟩
    exact ge_of_tendsto ht (Eventually.of_forall fun j => hb (hmem j))

/-- **Uniqueness (Dang--Favre characterization).** A real function `I` on tuples of
b-divisors over `X` which equals the classical intersection number on every tuple of nef Cartier
b-divisors with a common nef realization, and which is continuous along decreasing sequences of
nef Cartier tuples converging to nef tuples, coincides with the b-divisor intersection product
on all tuples of nef b-divisors. -/
theorem eq_nefIntersection_of_cartier_of_antitone (ω : KahlerBackground (m + 1) X)
    (I : (Fin (m + 1) → WeilFamilyAny Sys) → ℝ)
    (hcart : ∀ (C : Fin (m + 1) → WeilFamilyAny Sys) (r : CommonNefRealization C),
      I C = r.intersection)
    (hdec : ∀ (C : Fin (m + 1) → ℕ → WeilFamilyAny Sys) (D : Fin (m + 1) → WeilFamilyAny Sys),
      (∀ i j, IsNefCartierAny (C i j)) → (∀ i j k, j ≤ k → LEAny (C i k) (C i j)) →
        (∀ i, ConvergesAny atTop (C i) (D i)) → (∀ i, IsNefAny (D i)) →
          Tendsto (fun j => I (fun i => C i j)) atTop (𝓝 (I D)))
    (D : Fin (m + 1) → WeilFamilyAny Sys) (hD : ∀ i, IsNefAny (D i)) :
    I D = (nefIntersection D).toReal := by
  obtain ⟨C, r, hC, ha, hc, ht⟩ := exists_antitone_cartier_approximation ω D hD
  have hI := hdec C D hC ha hc hD
  have hI' : Tendsto (fun j => (r j).intersection) atTop (𝓝 (I D)) :=
    hI.congr' (Eventually.of_forall fun j => hcart (fun i => C i j) (r j))
  exact tendsto_nhds_unique hI' ht

/-- The b-divisor intersection product itself has the two properties of the Dang--Favre
characterization: it is the classical intersection number on nef Cartier tuples with a common
nef realization, and it is continuous along decreasing nets of nef Cartier tuples. -/
theorem nefIntersection_isDangFavre (ω : KahlerBackground (m + 1) X) :
    (∀ (C : Fin (m + 1) → WeilFamilyAny Sys) (r : CommonNefRealization C),
      (nefIntersection C).toReal = r.intersection) ∧
    (∀ {J : Type u} [Preorder J] [IsDirected J (· ≤ ·)] [Nonempty J]
      (C : Fin (m + 1) → J → WeilFamilyAny Sys) (D : Fin (m + 1) → WeilFamilyAny Sys),
      (∀ i j, IsNefCartierAny (C i j)) → (∀ i j k, j ≤ k → LEAny (C i k) (C i j)) →
        (∀ i, ConvergesAny atTop (C i) (D i)) →
          Tendsto (fun j => (nefIntersection (fun i => C i j)).toReal) atTop
            (𝓝 (nefIntersection D).toReal)) := by
  refine ⟨fun C r => (r.intersection_eq ω).symm, ?_⟩
  intro J _ _ _ C D hC ha hc
  obtain ⟨-, ht⟩ := source_DFdecnet ω C D (fun i j => isNefAny_of_isNefCartierAny (hC i j)) ha hc
  exact (ENNReal.tendsto_toReal (nefIntersection_lt_top D).ne).comp ht

end SGPT.BDivisor.DangFavre
