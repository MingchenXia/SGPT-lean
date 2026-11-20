import SGPT.Projective.NativeCITowerDegree
import SGPT.Projective.ActualClopenPeriodSum
import SGPT.Foundations.Analysis.Pending.OpensRestrictionMeasure
import SGPT.Hodge.SourceSmoothMixedCohomology

/-!
# Curve-nef forms against complete-intersection curves

Toward the Kleiman half of `rmk:bdiv:L749` (Dang–Favre's nef classes are curve-nef numerical
classes; the book's are nef `(1,1)`-classes).  Let `X` be a compact complex manifold of
dimension `k + 1` and `a` a closed real `(1,1)`-form which is *curve-nef*: `∫_C g^*a ≥ 0` for
every holomorphic map `g : C → X` from a compact **connected** Riemann surface.

* `degreeAlong_nonneg_of_curveNef`: then `∫_C g^*a ≥ 0` also for every compact, possibly
  disconnected, Riemann surface `C` (sum over the finitely many connected components,
  `ActualClopenPeriodSum.slotIntegral_sum_fullOpen`).
* `slotIntegral_cons_positive_nonneg`: for positive Hermitian line bundles `P₁, …, P_k` on `X`,
  `∫_X a ∧ c₁(P₁) ∧ ⋯ ∧ c₁(P_k) ≥ 0`: the integral is a positive multiple of the degree of `a`
  on a smooth complete-intersection curve cut out by sections of powers of the `Pᵢ`
  (`WholeNativeCITower.terminal_degree_eq_power_product`).
* `slotIntegral_cons_positiveCombination_nonneg`: the same for slots which are nonnegative
  combinations of the curvature forms of finitely many positive bundles (up to `ddᶜ`).
-/

set_option autoImplicit false

noncomputable section

open Set TopologicalSpace
open scoped Topology Manifold ContDiff BigOperators

namespace SGPT.BDivisor.Kleiman

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.NefMixedMass
open SGPT.Projective.NumEq SGPT.Projective.NumEq.CompleteIntersections
open SGPT.Hodge.BDivChain.SourceMixedOrderDraft

section Components

variable {n : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X]

/-- **Curve-nef forms have nonnegative degree on every compact curve**, connected or not: the
degree is the sum of the degrees on the (finitely many, clopen) connected components. -/
theorem degreeAlong_nonneg_of_curveNef (θ : ClosedRealOneOneForm n X)
    (hθ : ∀ (C : Type) [TopologicalSpace C] [ChartedSpace (ComplexModel 1) C]
      [IsComplexManifold 1 C] [CompactSpace C] [ConnectedSpace C] (κ : KahlerBackground 1 C)
      (g : C → X) (hg : ContMDiff 𝓘(ℂ, ComplexModel 1) 𝓘(ℂ, ComplexModel n) ∞ g),
      0 ≤ degreeAlong κ hg θ)
    {C : Type} [TopologicalSpace C] [ChartedSpace (ComplexModel 1) C] [IsComplexManifold 1 C]
    [CompactSpace C] (κ : KahlerBackground 1 C) {g : C → X}
    (hg : ContMDiff 𝓘(ℂ, ComplexModel 1) 𝓘(ℂ, ComplexModel n) ∞ g) :
    0 ≤ degreeAlong κ hg θ := by
  classical
  let : LocallyConnectedSpace C := ChartedSpace.locallyConnectedSpace (ComplexModel 1) C
  let : MeasurableSpace C := borel C
  have : BorelSpace C := ⟨rfl⟩
  have hfin : Finite (ConnectedComponents C) := by
    have : CompactSpace (ConnectedComponents C) :=
      ⟨by
        rw [← ConnectedComponents.surjective_coe.range_eq, ← Set.image_univ]
        exact isCompact_univ.image ConnectedComponents.continuous_coe⟩
    exact finite_of_compact_of_discrete
  let : Fintype (ConnectedComponents C) := Fintype.ofFinite _
  let anchor : ConnectedComponents C → C := Quotient.out
  have hanchor (c : ConnectedComponents C) : ConnectedComponents.mk (anchor c) = c :=
    Quotient.out_eq c
  let U : ConnectedComponents C → Opens C := fun c =>
    ⟨connectedComponent (anchor c), isOpen_connectedComponent⟩
  have hUclopen (c : ConnectedComponents C) : IsClopen (U c : Set C) :=
    isClopen_connectedComponent
  have hx (x : C) : x ∈ U (ConnectedComponents.mk x) :=
    ConnectedComponents.coe_eq_coe'.mp (hanchor (ConnectedComponents.mk x)).symm
  let : ∀ c, MeasurableSpace (U c) := fun c => borel (U c)
  have : ∀ c, BorelSpace (U c) := fun c => ⟨rfl⟩
  have : ∀ c, CompactSpace (U c) := fun c =>
    OpensRestrictionMeasure.compactSpace_of_isClopen (hUclopen c)
  have hdisj : Pairwise (fun c d => Disjoint (U c : Set C) (U d : Set C)) := by
    intro c d hcd
    apply Set.disjoint_left.mpr
    intro x hxc hxd
    apply hcd
    have h1 : ConnectedComponents.mk x = c :=
      (ConnectedComponents.coe_eq_coe'.mpr hxc).trans (hanchor c)
    have h2 : ConnectedComponents.mk x = d :=
      (ConnectedComponents.coe_eq_coe'.mpr hxd).trans (hanchor d)
    exact h1.symm.trans h2
  have hcover : (⋃ c, (U c : Set C)) = univ :=
    Set.eq_univ_of_forall fun x => Set.mem_iUnion.mpr ⟨_, hx x⟩
  have hsum := SGPT.Projective.NumEq.AlgebraicCurveDegree.slotIntegral_sum_fullOpen
    (Y := fun c => U c) (fun c => Subtype.val) (fun c => OpensRestriction.contMDiff_val (U c))
    (fun c => (U c : Set C)) (fun c => (U c).isOpen)
    (fun c => OpensRestrictionMeasure.isIsomorphismOver_val (U := U c))
    (fun c => by ext y; simp only [mem_preimage, Subtype.coe_prop, mem_univ])
    hdisj hcover κ (fun c => OpensRestriction.restrictKahler (U c) κ)
    (fun _ => ClosedRealOneOneForm.pullback hg θ)
  change _ = slotIntegral κ (fun _ => ClosedRealOneOneForm.pullback hg θ) at hsum
  change 0 ≤ slotIntegral κ (fun _ => ClosedRealOneOneForm.pullback hg θ)
  rw [← hsum]
  refine Finset.sum_nonneg fun c _ => ?_
  have : ConnectedSpace (U c) :=
    isConnected_iff_connectedSpace.mp isConnected_connectedComponent
  have hdeg := hθ (U c) (OpensRestriction.restrictKahler (U c) κ) (g ∘ Subtype.val)
    (hg.comp (OpensRestriction.contMDiff_val (U c)))
  have hrel : ∀ _i : Fin 1, ClosedRealOneOneForm.BottChernRel
      (ClosedRealOneOneForm.pullback (hg.comp (OpensRestriction.contMDiff_val (U c))) θ)
      (ClosedRealOneOneForm.pullback (OpensRestriction.contMDiff_val (U c))
        (ClosedRealOneOneForm.pullback hg θ)) := fun _ =>
    ClosedRealOneOneForm.bottChernRel_of_geometricallyEq
      (FormPullbackCompMixed.pullback_comp_geometricallyEq hg
        (OpensRestriction.contMDiff_val (U c)) θ.val)
  change 0 ≤ slotIntegral _ (fun _ => _) at hdeg
  rw [slotIntegral_eq_of_bottChernRel _ _ _ hrel] at hdeg
  exact hdeg

end Components

section CompleteIntersection

variable {k : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel (k + 1)) X]
  [IsComplexManifold (k + 1) X] [CompactSpace X]

/-- **A curve-nef form against positive line bundles.**  If `a` is curve-nef and `P₁, …, P_k`
are positive Hermitian line bundles on the compact manifold `X` of dimension `k + 1`, then
`∫_X a ∧ c₁(P₁) ∧ ⋯ ∧ c₁(P_k) ≥ 0`: the integral is a positive multiple of the degree of `a`
on a smooth complete-intersection curve. -/
theorem slotIntegral_cons_positive_nonneg (P : Fin k → NativePositiveLine (k + 1) X)
    (κ : KahlerBackground (k + 1) X) (a : ClosedRealOneOneForm (k + 1) X)
    (ha : ∀ (C : Type) [TopologicalSpace C] [ChartedSpace (ComplexModel 1) C]
      [IsComplexManifold 1 C] [CompactSpace C] [ConnectedSpace C] (κC : KahlerBackground 1 C)
      (g : C → X) (hg : ContMDiff 𝓘(ℂ, ComplexModel 1) 𝓘(ℂ, ComplexModel (k + 1)) ∞ g),
      0 ≤ degreeAlong κC hg a) :
    let : MeasurableSpace X := borel X
    0 ≤ slotIntegral κ (Fin.cons a (fun i => (P i).curvature)) := by
  let : MeasurableSpace X := borel X
  have : BorelSpace X := ⟨rfl⟩
  dsimp only
  obtain ⟨T⟩ := exists_wholeNativeCITower k X P
  have hdegree := WholeNativeCITower.terminal_degree_eq_power_product k X T κ a
  have hnonneg := degreeAlong_nonneg_of_curveNef a ha
    (WholeNativeCITower.terminal k X T κ).background
    (WholeNativeCITower.terminal k X T κ).inclusion.contMDiff
  have hprod := WholeNativeCITower.powers_real_prod_pos k T
  dsimp only at hdegree
  rw [hdegree] at hnonneg
  exact (mul_nonneg_iff_of_pos_left hprod).mp hnonneg

end CompleteIntersection

end SGPT.BDivisor.Kleiman
