import SGPT.BDivisor.BD6Cycle
import SGPT.BDivisor.BD5Algebraization
import SGPT.BDivisor.DFAlgComparison
import SGPT.BDivisor.BDBlowupProjective
import SGPT.Okounkov.OF14Integral

/-!
# GAGA for divisors on the algebraized models of the book's system

Source: `rmk:bdiv:L749` ("our transcendental intersection theory coincides with [Dang–Favre's] in
the algebraic setting").

Taken over from the uncompiled draft `BD6Models.lean` (renamed into namespace `BD7`).
`BD6Cycle` proves that the analytic Néron–Severi space of `V(ℂ)` (`V` integral smooth projective
over `ℂ`) is spanned by the Chern classes of algebraic line bundles.  Here this is transported to
the book's models:

* integrality of the algebraizations: lane OF14's
  `SGPT.Okounkov.OF14.isIntegral_of_connectedSpace_schemeComplexPoint` (a smooth projective
  complex scheme with connected `V(ℂ)` is integral);
* `mem_neronSeveri_iff_exists_realCartier`: for a biholomorphism `e : V(ℂ) ≃ Y`, a class `α` of
  `Y` lies in `NS(Y)_ℝ` iff `e^*α = {∑_A v(A) c₁(A, K_A)}` for an algebraic real Cartier class `v`
  of `V` (for all smooth metrics `K`);
* `exists_algebraization_neronSeveri_bd7`: every model `π : Y → X(ℂ)` of the book's blow-up
  system has an algebraization `e : V(ℂ) ≃ Y`, `V` integral smooth projective, identifying
  `NS(Y)_ℝ` with the real Cartier classes of `V`;
* `isAlgNefCartierAny_iff_exists_algebraic_realization`: the algebraic nef Cartier b-divisors
  (`IsAlgNefCartierAny`, realized by nef classes of the analytic `NS(Y)_ℝ`) are exactly the
  b-divisors realized on an algebraized model by (the push-forward of) a nef algebraic real
  Cartier class of `V`, Dang–Favre's nef Cartier classes;
* `nefIntersectionReal_eq_originalRealMixedEuler_of_neronSeveri_bd7`: for b-divisors realized on
  a common model by nef classes of `NS(Y)_ℝ` (algebraic nef Cartier tuples with a common
  realization) the book's product equals Dang–Favre's number (multilinear Snapper–Kleiman) of the
  corresponding algebraic real Cartier classes on the algebraization.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.unusedSectionVars false

noncomputable section

namespace SGPT.BDivisor.BD7

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Set Filter
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open SGPT.Okounkov SGPT.GAGA.H0S SGPT.Projective
open SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
open SGPT.BDivisor.DFAlg SGPT.BDivisor.BD6

local instance bd7ModTopology {X : Scheme.{0}} (h : X ⟶ Spec (.of ℂ)) :
    TopologicalSpace (SchemeComplexPoint h) := schemeAnalyticPointTopology h
local instance bd7ModCharts {X : Scheme.{0}} (h : X ⟶ Spec (.of ℂ)) (d : ℕ)
    [SmoothOfRelativeDimension d h] : ChartedSpace (ComplexModel d) (SchemeComplexPoint h) :=
  schemeAnalyticTNChartedSpace h d
local instance bd7ModManifold {X : Scheme.{0}} (h : X ⟶ Spec (.of ℂ)) (d : ℕ)
    [SmoothOfRelativeDimension d h] [IsSeparated h] [QuasiCompact h] :
    IsComplexManifold d (SchemeComplexPoint h) := schemeAnalyticTN_isComplexManifold h d

/-! ### Transport along a biholomorphism -/

section Transport

variable {m : ℕ} {M Y : Type} [TopologicalSpace M] [ChartedSpace (ComplexModel (m + 1)) M]
  [IsComplexManifold (m + 1) M] [TopologicalSpace Y] [ChartedSpace (ComplexModel (m + 1)) Y]
  [IsComplexManifold (m + 1) Y]
  (e : M ≃ₘ⟮𝓘(ℂ, ComplexModel (m + 1)), 𝓘(ℂ, ComplexModel (m + 1))⟯ Y)

theorem exceptionalLocus_diffeomorph : exceptionalLocus (m + 1) e = ∅ := by
  ext x
  simp only [exceptionalLocus, Set.mem_ofPred_eq, mem_empty_iff_false, iff_false, not_not]
  rw [← Diffeomorph.mfderivToContinuousLinearEquiv_coe e (by simp)]
  exact (e.mfderivToContinuousLinearEquiv (by simp) x).bijective

theorem classPullback_symm_classPullback (α : RealBottChern (m + 1) Y) :
    classPullback e.symm.contMDiff (classPullback e.contMDiff α) = α := by
  rw [← classPullback_comp e.contMDiff e.symm.contMDiff,
    classPullback_congr (show (e ∘ e.symm : Y → Y) = id from funext e.apply_symm_apply)
      _ contMDiff_id, classPullback_id]

theorem classPullback_mem_neronSeveri_diffeomorph {α : RealBottChern (m + 1) Y}
    (hα : α ∈ neronSeveri (m + 1) Y) : classPullback e.contMDiff α ∈ neronSeveri (m + 1) M :=
  classPullback_mem_neronSeveri e.contMDiff (by rw [exceptionalLocus_diffeomorph, interior_empty]) hα

/-- `NS` is invariant under biholomorphisms. -/
theorem mem_neronSeveri_iff_classPullback (α : RealBottChern (m + 1) Y) :
    α ∈ neronSeveri (m + 1) Y ↔ classPullback e.contMDiff α ∈ neronSeveri (m + 1) M := by
  refine ⟨classPullback_mem_neronSeveri_diffeomorph e, fun h => ?_⟩
  rw [← classPullback_symm_classPullback e α]
  exact classPullback_mem_neronSeveri_diffeomorph e.symm h

end Transport

/-! ### Real Cartier classes -/

section RealCartier

variable {V : Scheme.{0}} (g : V ⟶ Spec (.of ℂ)) (EV : ClosedProjectiveEmbedding g) (m : ℕ)
  [SmoothOfRelativeDimension (m + 1) g] [IsSeparated g] [QuasiCompact g]

theorem ofRepresentative_linearCombination {ι : Type*} (θ : ι → ClosedRealOneOneForm (m + 1)
    (SchemeComplexPoint g)) (v : ι →₀ ℝ) :
    RealBottChern.ofRepresentative (Finsupp.linearCombination ℝ θ v) =
      Finsupp.linearCombination ℝ (fun i => RealBottChern.ofRepresentative (θ i)) v := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v w hv hw => rw [map_add, map_add, RealBottChern.ofRepresentative_add, hv, hw]
  | single i a => simp [Finsupp.linearCombination_single]

/-- The Chern classes of an algebraic real Cartier class do not depend on the metrics. -/
theorem ofRepresentative_realCartier_eq
    (K : ∀ A : IntrinsicLineBundle V, SchemeLineBundleMetric g (m + 1) EV A.sheaf)
    (v : IntrinsicLineBundle V →₀ ℝ) :
    RealBottChern.ofRepresentative (Finsupp.linearCombination ℝ
        (fun A : IntrinsicLineBundle V => (K A).curvature A.atlas) v) =
      Finsupp.linearCombination ℝ (algChern g EV m) v := by
  rw [ofRepresentative_linearCombination]
  have h : (fun A : IntrinsicLineBundle V => RealBottChern.ofRepresentative ((K A).curvature A.atlas)) =
      algChern g EV m := funext fun A =>
    (K A).chernClass_independent (schemeLineBundleMetric g (m + 1) EV A.atlas) A.atlas A.atlas
  rw [h]

variable [IsIntegral V] [CompactSpace (SchemeComplexPoint g)]

/-- **`NS(V(ℂ))_ℝ` is the space of Chern classes of algebraic real Cartier classes**, for any
smooth metrics. -/
theorem mem_neronSeveri_iff_exists_realCartier (β : RealBottChern (m + 1) (SchemeComplexPoint g)) :
    β ∈ neronSeveri (m + 1) (SchemeComplexPoint g) ↔
      ∃ v : IntrinsicLineBundle V →₀ ℝ,
        ∀ K : ∀ A : IntrinsicLineBundle V, SchemeLineBundleMetric g (m + 1) EV A.sheaf,
          β = RealBottChern.ofRepresentative (Finsupp.linearCombination ℝ
            (fun A : IntrinsicLineBundle V => (K A).curvature A.atlas) v) := by
  rw [neronSeveri_eq_span_algChern g EV m]
  constructor
  · intro hβ
    obtain ⟨v, hv⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hβ
    refine ⟨v, fun K => ?_⟩
    rw [ofRepresentative_realCartier_eq g EV m K v, Finsupp.linearCombination_apply, hv]
  · rintro ⟨v, hv⟩
    rw [hv (fun A => schemeLineBundleMetric g (m + 1) EV A.atlas),
      ofRepresentative_realCartier_eq]
    exact Finsupp.mem_span_range_iff_exists_finsupp.mpr ⟨v, (Finsupp.linearCombination_apply ℝ v).symm⟩

end RealCartier

/-! ### The book's models -/

section Models

open SGPT.Hodge.BDivChain.NativeDraft SGPT.Hodge.BDivChain.SourceNefIntersectionDraft
open SGPT.Hodge.BDivChain.SourceMixedOrderDraft SGPT.Foundations.Analysis.FirstPass.PositiveClasses

variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (E : ClosedProjectiveEmbedding f) [IsIntegral X]
  {k : ℕ} [SmoothOfRelativeDimension (k + 1) f] [Nonempty (SchemeComplexPoint f)]

/-- **GAGA for divisors on the book's models.**  Every model `π : Y → X(ℂ)` of the book's blow-up
system has an algebraization `e : V(ℂ) ≃ Y` by an integral smooth projective complex scheme `V`,
such that a class `α` of `Y` lies in the analytic Néron–Severi space `NS(Y)_ℝ` iff
`e^*α = {∑_A v(A) c₁(A, K_A)}` for an algebraic real Cartier class `v` of `V` (all metrics `K`). -/
theorem exists_algebraization_neronSeveri_bd7 :
    let := E.isSeparated
    let := E.quasiCompact
    let : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
    let : ConnectedSpace (SchemeComplexPoint f) :=
      SGPT.GAGA.OkoClose.connectedSpace_of_isIntegral f E (k + 1)
    ∀ π : (ModelSystem.blowup (k + 1) (SchemeComplexPoint f)).Model,
      ∃ (V : Scheme.{0}) (g : V ⟶ Spec (.of ℂ)) (hsm : SmoothOfRelativeDimension (k + 1) g)
        (EV : ClosedProjectiveEmbedding g),
        letI := hsm
        letI := EV.isSeparated
        letI := EV.quasiCompact
        IsIntegral V ∧
        ∃ e : SchemeComplexPoint g ≃ₘ⟮𝓘(ℂ, ComplexModel (k + 1)), 𝓘(ℂ, ComplexModel (k + 1))⟯
            π.1.carrier,
          ∀ α : RealBottChern (k + 1) π.1.carrier, α ∈ neronSeveri (k + 1) π.1.carrier ↔
            ∃ v : IntrinsicLineBundle V →₀ ℝ,
              ∀ K : ∀ A : IntrinsicLineBundle V, SchemeLineBundleMetric g (k + 1) EV A.sheaf,
                classPullback e.contMDiff α = RealBottChern.ofRepresentative
                  (Finsupp.linearCombination ℝ
                    (fun A : IntrinsicLineBundle V => (K A).curvature A.atlas) v) := by
  let := E.isSeparated
  let := E.quasiCompact
  let : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  let : ConnectedSpace (SchemeComplexPoint f) :=
    SGPT.GAGA.OkoClose.connectedSpace_of_isIntegral f E (k + 1)
  dsimp only
  intro π
  obtain ⟨V, g, hsm, EV, ⟨e⟩⟩ := BD5.exists_algebraization_of_blowup_model_bd5 f E π
  refine ⟨V, g, hsm, EV, ?_⟩
  let := hsm
  let := EV.isSeparated
  let := EV.quasiCompact
  have : ConnectedSpace π.1.carrier := blowup_model_connectedSpace π
  have : ConnectedSpace (SchemeComplexPoint g) :=
    e.symm.toHomeomorph.surjective.connectedSpace e.symm.continuous
  have hint : IsIntegral V :=
    SGPT.Okounkov.OF14.isIntegral_of_connectedSpace_schemeComplexPoint g (k + 1) EV
  have : CompactSpace (SchemeComplexPoint g) := EV.analyticCompact
  refine ⟨hint, e, fun α => ?_⟩
  rw [mem_neronSeveri_iff_classPullback e α]
  exact mem_neronSeveri_iff_exists_realCartier g EV k _

/-- **GAGA for divisors on every algebraization of a model.**  Let `π : Y → X(ℂ)` be a model of
the book's blow-up system and `e : V(ℂ) ≃ Y` an algebraization of `Y` by a smooth projective complex
scheme `V` (for instance lane BD5's).  Then `V` is integral and a class `α` of `Y` lies in the
analytic Néron–Severi space `NS(Y)_ℝ` iff `e^*α = {∑_A v(A) c₁(A, K_A)}` for an algebraic real
Cartier class `v` of `V` (for all smooth metrics `K`): every class of `NS(Y)_ℝ` is `e_*` of an
algebraic real Cartier class of `V`, and conversely. -/
theorem mem_neronSeveri_iff_of_algebraization :
    let := E.isSeparated
    let := E.quasiCompact
    let : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
    let : ConnectedSpace (SchemeComplexPoint f) :=
      SGPT.GAGA.OkoClose.connectedSpace_of_isIntegral f E (k + 1)
    ∀ (π : (ModelSystem.blowup (k + 1) (SchemeComplexPoint f)).Model) {V : Scheme.{0}}
      (g : V ⟶ Spec (.of ℂ)) [SmoothOfRelativeDimension (k + 1) g] [IsSeparated g] [QuasiCompact g]
      (EV : ClosedProjectiveEmbedding g)
      (e : SchemeComplexPoint g ≃ₘ⟮𝓘(ℂ, ComplexModel (k + 1)), 𝓘(ℂ, ComplexModel (k + 1))⟯
        π.1.carrier),
      IsIntegral V ∧ ∀ α : RealBottChern (k + 1) π.1.carrier, α ∈ neronSeveri (k + 1) π.1.carrier ↔
        ∃ v : IntrinsicLineBundle V →₀ ℝ,
          ∀ K : ∀ A : IntrinsicLineBundle V, SchemeLineBundleMetric g (k + 1) EV A.sheaf,
            classPullback e.contMDiff α = RealBottChern.ofRepresentative
              (Finsupp.linearCombination ℝ
                (fun A : IntrinsicLineBundle V => (K A).curvature A.atlas) v) := by
  let := E.isSeparated
  let := E.quasiCompact
  let : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  let : ConnectedSpace (SchemeComplexPoint f) :=
    SGPT.GAGA.OkoClose.connectedSpace_of_isIntegral f E (k + 1)
  dsimp only
  intro π V g _ _ _ EV e
  have : ConnectedSpace π.1.carrier := blowup_model_connectedSpace π
  have : ConnectedSpace (SchemeComplexPoint g) :=
    e.symm.toHomeomorph.surjective.connectedSpace e.symm.continuous
  have hint : IsIntegral V :=
    SGPT.Okounkov.OF14.isIntegral_of_connectedSpace_schemeComplexPoint g (k + 1) EV
  have : CompactSpace (SchemeComplexPoint g) := EV.analyticCompact
  refine ⟨hint, fun α => ?_⟩
  rw [mem_neronSeveri_iff_classPullback e α]
  exact mem_neronSeveri_iff_exists_realCartier g EV k _

/-- **Algebraic b-divisors are those with algebraic incarnations.**  A Weil b-divisor `D` over
`X(ℂ)` (book's blow-up models) is algebraic (`IsAlgebraicAny`: every incarnation lies in the analytic
`NS(Y)_ℝ`) iff for every model `π : Y → X(ℂ)` and every algebraization `e : V(ℂ) ≃ Y` by a smooth
projective complex scheme `V`, the incarnation `D_Y` is `e_*` of an algebraic real Cartier class
of `V`: `e^* D_Y = {∑_A v(A) c₁(A, K_A)}` for all metrics `K`. -/
theorem isAlgebraicAny_iff_forall_algebraization :
    let := E.isSeparated
    let := E.quasiCompact
    let : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
    let : ConnectedSpace (SchemeComplexPoint f) :=
      SGPT.GAGA.OkoClose.connectedSpace_of_isIntegral f E (k + 1)
    ∀ D : WeilFamilyAny (ModelSystem.blowup (k + 1) (SchemeComplexPoint f)),
      IsAlgebraicAny D ↔
        ∀ (π : (ModelSystem.blowup (k + 1) (SchemeComplexPoint f)).Model) {V : Scheme.{0}}
          (g : V ⟶ Spec (.of ℂ)) [SmoothOfRelativeDimension (k + 1) g] [IsSeparated g]
          [QuasiCompact g] (EV : ClosedProjectiveEmbedding g)
          (e : SchemeComplexPoint g ≃ₘ⟮𝓘(ℂ, ComplexModel (k + 1)), 𝓘(ℂ, ComplexModel (k + 1))⟯
            π.1.carrier),
          ∃ v : IntrinsicLineBundle V →₀ ℝ,
            ∀ K : ∀ A : IntrinsicLineBundle V, SchemeLineBundleMetric g (k + 1) EV A.sheaf,
              classPullback e.contMDiff (D.val π) = RealBottChern.ofRepresentative
                (Finsupp.linearCombination ℝ
                  (fun A : IntrinsicLineBundle V => (K A).curvature A.atlas) v) := by
  let := E.isSeparated
  let := E.quasiCompact
  let : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  let : ConnectedSpace (SchemeComplexPoint f) :=
    SGPT.GAGA.OkoClose.connectedSpace_of_isIntegral f E (k + 1)
  dsimp only
  intro D
  constructor
  · intro hD π V g _ _ _ EV e
    exact ((mem_neronSeveri_iff_of_algebraization f E π g EV e).2 _).mp (hD π)
  · intro h π
    obtain ⟨V, g, hsm, EV, ⟨e⟩⟩ := BD5.exists_algebraization_of_blowup_model_bd5 f E π
    let := hsm
    let := EV.isSeparated
    let := EV.quasiCompact
    exact ((mem_neronSeveri_iff_of_algebraization f E π g EV e).2 _).mpr (h π g EV e)

/-- **The book's product equals Dang–Favre's number for algebraic nef Cartier tuples with a common
realization.**  Every model `π : Y → X(ℂ)` has an algebraization `e : V(ℂ) ≃ Y` (`V` integral smooth
projective) such that for every Kähler form `κ` of `Y` and all `κ`-nef closed real `(1,1)`-forms
`θᵢ` with classes in the analytic `NS(Y)_ℝ`, there are algebraic real Cartier classes `vᵢ` of `V`
with `e^*{θᵢ} = {∑_A vᵢ(A) c₁(A)}` (any metrics), and the Weil b-divisors `Dᵢ` realized on `Y` by
`{θᵢ}` have book product `(D₀, …, D_k)` equal to Dang–Favre's (multilinearly extended
Snapper–Kleiman) number of the `vᵢ` on `V`, for every base line bundle `B`. -/
theorem nefIntersectionReal_eq_originalRealMixedEuler_of_neronSeveri_bd7 :
    let := E.isSeparated
    let := E.quasiCompact
    let : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
    let : ConnectedSpace (SchemeComplexPoint f) :=
      SGPT.GAGA.OkoClose.connectedSpace_of_isIntegral f E (k + 1)
    ∀ π : (ModelSystem.blowup (k + 1) (SchemeComplexPoint f)).Model,
      ∃ (V : Scheme.{0}) (g : V ⟶ Spec (.of ℂ)) (hsm : SmoothOfRelativeDimension (k + 1) g)
        (EV : ClosedProjectiveEmbedding g),
        letI := hsm
        letI := EV.isSeparated
        letI := EV.quasiCompact
        IsIntegral V ∧
        ∃ e : SchemeComplexPoint g ≃ₘ⟮𝓘(ℂ, ComplexModel (k + 1)), 𝓘(ℂ, ComplexModel (k + 1))⟯
            π.1.carrier,
          ∀ (κ : KahlerBackground (k + 1) π.1.carrier)
            (θ : Fin (k + 1) → ClosedRealOneOneForm (k + 1) π.1.carrier),
            (∀ i, NefWithRespectTo κ (θ i)) →
            (∀ i, RealBottChern.ofRepresentative (θ i) ∈ neronSeveri (k + 1) π.1.carrier) →
            ∃ v : Fin (k + 1) → IntrinsicLineBundle V →₀ ℝ,
              (∀ i, ∀ K : ∀ A : IntrinsicLineBundle V, SchemeLineBundleMetric g (k + 1) EV A.sheaf,
                RealBottChern.ofRepresentative (ClosedRealOneOneForm.pullback e.contMDiff (θ i)) =
                  RealBottChern.ofRepresentative (Finsupp.linearCombination ℝ
                    (fun A : IntrinsicLineBundle V => (K A).curvature A.atlas) (v i))) ∧
              ∀ D : Fin (k + 1) →
                  WeilFamilyAny (ModelSystem.blowup (k + 1) (SchemeComplexPoint f)),
                (∀ i, IsRealizationAny (D i) π (RealBottChern.ofRepresentative (θ i))) →
                ∀ B : IntrinsicLineBundle V,
                  nefIntersectionReal D = originalRealMixedEuler g EV (k + 1) B v := by
  let := E.isSeparated
  let := E.quasiCompact
  let : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  let : ConnectedSpace (SchemeComplexPoint f) :=
    SGPT.GAGA.OkoClose.connectedSpace_of_isIntegral f E (k + 1)
  dsimp only
  intro π
  obtain ⟨V, g, hsm, EV, hint, e, hiff⟩ := exists_algebraization_neronSeveri_bd7 f E π
  refine ⟨V, g, hsm, EV, hint, e, fun κ θ hnef hNS => ?_⟩
  let := hsm
  let := EV.isSeparated
  let := EV.quasiCompact
  choose v hv using fun i => (hiff (RealBottChern.ofRepresentative (θ i))).mp (hNS i)
  refine ⟨v, fun i K => hv i K, fun D hD B => ?_⟩
  exact nefIntersectionReal_eq_originalRealMixedEuler_of_diffeomorph_bd5 f E g EV
    (fun A => schemeLineBundleMetric g (k + 1) EV A.atlas) B v π e κ θ hnef
    (fun i => hv i _) D hD

/-- **The algebraic nef Cartier b-divisors are the images of Dang–Favre's nef Cartier classes on
the algebraized models.**  A Weil b-divisor `C` over `X(ℂ)` is algebraic nef Cartier
(`IsAlgNefCartierAny`: realized on a model `Y` by a nef class of the analytic `NS(Y)_ℝ`) iff it is
realized on some model `π : Y → X(ℂ)` with an algebraization `e : V(ℂ) ≃ Y` (`V` smooth projective) by
the push-forward `(e⁻¹)^*{∑_A v(A) c₁(A)}` of an algebraic real Cartier class `v` of `V` which is
nef. -/
theorem isAlgNefCartierAny_iff_exists_algebraic_realization :
    let := E.isSeparated
    let := E.quasiCompact
    let : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
    let : ConnectedSpace (SchemeComplexPoint f) :=
      SGPT.GAGA.OkoClose.connectedSpace_of_isIntegral f E (k + 1)
    ∀ C : WeilFamilyAny (ModelSystem.blowup (k + 1) (SchemeComplexPoint f)),
    IsAlgNefCartierAny C ↔
      ∃ (π : (ModelSystem.blowup (k + 1) (SchemeComplexPoint f)).Model) (V : Scheme.{0})
        (g : V ⟶ Spec (.of ℂ)) (hsm : SmoothOfRelativeDimension (k + 1) g)
        (EV : ClosedProjectiveEmbedding g),
        letI := hsm
        letI := EV.isSeparated
        letI := EV.quasiCompact
        ∃ (e : SchemeComplexPoint g ≃ₘ⟮𝓘(ℂ, ComplexModel (k + 1)), 𝓘(ℂ, ComplexModel (k + 1))⟯
            π.1.carrier) (v : IntrinsicLineBundle V →₀ ℝ),
          IsRealizationAny C π
            (classPullback e.symm.contMDiff (Finsupp.linearCombination ℝ (algChern g EV k) v)) ∧
          ∃ κ : KahlerBackground (k + 1) π.1.carrier, ClassNefWithRespectTo κ
            (classPullback e.symm.contMDiff (Finsupp.linearCombination ℝ (algChern g EV k) v)) := by
  let := E.isSeparated
  let := E.quasiCompact
  let : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  let : ConnectedSpace (SchemeComplexPoint f) :=
    SGPT.GAGA.OkoClose.connectedSpace_of_isIntegral f E (k + 1)
  dsimp only
  intro C
  constructor
  · rintro ⟨π, α, hα, hr, κ, hn⟩
    obtain ⟨V, g, hsm, EV, hint, e, hiff⟩ := exists_algebraization_neronSeveri_bd7 f E π
    let := hsm
    let := EV.isSeparated
    let := EV.quasiCompact
    obtain ⟨v, hv⟩ := (hiff α).mp hα
    have hβ : Finsupp.linearCombination ℝ (algChern g EV k) v = classPullback e.contMDiff α := by
      rw [hv (fun A => schemeLineBundleMetric g (k + 1) EV A.atlas),
        ofRepresentative_realCartier_eq]
    refine ⟨π, V, g, hsm, EV, e, v, ?_, κ, ?_⟩
    · rw [hβ, classPullback_symm_classPullback]; exact hr
    · rw [hβ, classPullback_symm_classPullback]; exact hn
  · rintro ⟨π, V, g, hsm, EV, e, v, hr, κ, hn⟩
    let := hsm
    let := EV.isSeparated
    let := EV.quasiCompact
    refine ⟨π, _, ?_, hr, κ, hn⟩
    apply classPullback_mem_neronSeveri_diffeomorph e.symm
    rw [Finsupp.linearCombination_apply]
    refine Submodule.sum_mem _ fun A _ => Submodule.smul_mem _ _ ?_
    exact originalProjectiveLine_chern_mem_neronSeveri g (k + 1) EV A.atlas _

/-- **The algebraic nef b-divisors are the images of Dang–Favre's nef classes on the algebraized
models.**  A Weil b-divisor `D` over `X(ℂ)` is algebraic nef (`IsAlgNefAny`, lanes DF-ALG/BD2) iff it
is algebraic and the limit of a net of b-divisors `C_i`, each realized on a model `π_i : Y_i → X(ℂ)`
with an algebraization `e_i : V_i(ℂ) ≃ Y_i` (`V_i` smooth projective) by the push-forward
`(e_i⁻¹)^*{∑_A v_i(A) c₁(A)}` of a nef algebraic real Cartier class `v_i` of `V_i`. -/
theorem isAlgNefAny_iff_exists_algebraic_realizations :
    let := E.isSeparated
    let := E.quasiCompact
    let : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
    let : ConnectedSpace (SchemeComplexPoint f) :=
      SGPT.GAGA.OkoClose.connectedSpace_of_isIntegral f E (k + 1)
    ∀ D : WeilFamilyAny (ModelSystem.blowup (k + 1) (SchemeComplexPoint f)),
    IsAlgNefAny D ↔ IsAlgebraicAny D ∧
      ∃ (ι : Type 1) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι)
        (C : ι → WeilFamilyAny (ModelSystem.blowup (k + 1) (SchemeComplexPoint f))),
        (∀ i, ∃ (π : (ModelSystem.blowup (k + 1) (SchemeComplexPoint f)).Model) (V : Scheme.{0})
          (g : V ⟶ Spec (.of ℂ)) (hsm : SmoothOfRelativeDimension (k + 1) g)
          (EV : ClosedProjectiveEmbedding g),
          letI := hsm
          letI := EV.isSeparated
          letI := EV.quasiCompact
          ∃ (e : SchemeComplexPoint g ≃ₘ⟮𝓘(ℂ, ComplexModel (k + 1)), 𝓘(ℂ, ComplexModel (k + 1))⟯
              π.1.carrier) (v : IntrinsicLineBundle V →₀ ℝ),
            IsRealizationAny (C i) π
              (classPullback e.symm.contMDiff (Finsupp.linearCombination ℝ (algChern g EV k) v)) ∧
            ∃ κ : KahlerBackground (k + 1) π.1.carrier, ClassNefWithRespectTo κ
              (classPullback e.symm.contMDiff (Finsupp.linearCombination ℝ (algChern g EV k) v))) ∧
        ConvergesAny atTop C D := by
  let := E.isSeparated
  let := E.quasiCompact
  let : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  let : ConnectedSpace (SchemeComplexPoint f) :=
    SGPT.GAGA.OkoClose.connectedSpace_of_isIntegral f E (k + 1)
  dsimp only
  intro D
  constructor
  · rintro ⟨hD, ι, i₁, i₂, i₃, C, hC, hc⟩
    exact ⟨hD, ι, i₁, i₂, i₃, C,
      fun i => (isAlgNefCartierAny_iff_exists_algebraic_realization f E (C i)).mp (hC i), hc⟩
  · rintro ⟨hD, ι, i₁, i₂, i₃, C, hC, hc⟩
    exact ⟨hD, ι, i₁, i₂, i₃, C,
      fun i => (isAlgNefCartierAny_iff_exists_algebraic_realization f E (C i)).mpr (hC i), hc⟩

/-- **Pull-backs of algebraic classes to the models are algebraic.**  For every model
`π : Y → X(ℂ)` and its algebraization `e : V(ℂ) ≃ Y` of `exists_algebraization_neronSeveri_bd7`,
the analytic pull-back `π^*c₁(L)` of the Chern class of every algebraic line bundle `L` of `X`
(any metric) is, read on `V` through `e`, the Chern class of an algebraic real Cartier class of
`V` (class-level compatibility of pull-backs; the algebraicity of `π` itself is not used). -/
theorem exists_algebraization_classPullback_bd7 :
    let := E.isSeparated
    let := E.quasiCompact
    let : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
    let : ConnectedSpace (SchemeComplexPoint f) :=
      SGPT.GAGA.OkoClose.connectedSpace_of_isIntegral f E (k + 1)
    ∀ π : (ModelSystem.blowup (k + 1) (SchemeComplexPoint f)).Model,
      ∃ (V : Scheme.{0}) (g : V ⟶ Spec (.of ℂ)) (hsm : SmoothOfRelativeDimension (k + 1) g)
        (EV : ClosedProjectiveEmbedding g),
        letI := hsm
        letI := EV.isSeparated
        letI := EV.quasiCompact
        IsIntegral V ∧
        ∃ e : SchemeComplexPoint g ≃ₘ⟮𝓘(ℂ, ComplexModel (k + 1)), 𝓘(ℂ, ComplexModel (k + 1))⟯
            π.1.carrier,
          ∀ {L : X.Modules} (a : LineBundleAtlas L) (H : SchemeLineBundleMetric f (k + 1) E L),
            ∃ v : IntrinsicLineBundle V →₀ ℝ,
              ∀ K : ∀ A : IntrinsicLineBundle V, SchemeLineBundleMetric g (k + 1) EV A.sheaf,
                classPullback e.contMDiff (classPullback π.1.isAnalyticModification.1
                    (RealBottChern.ofRepresentative (H.curvature a))) =
                  RealBottChern.ofRepresentative (Finsupp.linearCombination ℝ
                    (fun A : IntrinsicLineBundle V => (K A).curvature A.atlas) v) := by
  let := E.isSeparated
  let := E.quasiCompact
  let : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  let : ConnectedSpace (SchemeComplexPoint f) :=
    SGPT.GAGA.OkoClose.connectedSpace_of_isIntegral f E (k + 1)
  dsimp only
  intro π
  obtain ⟨V, g, hsm, EV, hint, e, hiff⟩ := exists_algebraization_neronSeveri_bd7 f E π
  refine ⟨V, g, hsm, EV, hint, e, fun a H => ?_⟩
  exact (hiff _).mp (classPullback_map_mem_neronSeveri π.1
    (originalProjectiveLine_chern_mem_neronSeveri f (k + 1) E a H))

end Models

end SGPT.BDivisor.BD7
