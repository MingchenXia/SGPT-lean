import SGPT.Foundations.Analysis.Pending.ModificationMassInvariance
import SGPT.Foundations.Analysis.Pending.ProductMapIsomorphismOver

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Mixed measures pulled back along `μ × id` do not lose mass

Step U1(b) of the uniform nef core of Boucksom 4.8 (TN.4 plan §1 F6 "STATUS (run 0157 end)",
the proof of Boucksom's mass estimate): the FIXED concentration of mass on the diagonal of
`X × X` is pulled back along `ν = μ × id : Y × W → X × W` for a blowup sequence `μ : Y → X`, and the
lower bound `δ` must survive with the same constant.  Source: Xia, *Singularities in global
pluripotential theory*, Proposition 2.4.2 (invariance of non-pluripolar masses under
modifications), in the product form needed for Boucksom's Lemma 4.10 (`bou02-volume:4.10`).

* `globalMixedMeasure_prod_univ_eq_zero` — for an analytic subset `C` of `Y` with empty interior,
  `C × W` is not charged by any global mixed non-pluripolar measure on `Y × W` (it is analytic with
  empty interior, hence locally pluripolar).
* `le_globalMixedMeasure_preimage_prodMap_of_isBlowupAlong` — for one blowup `g : Z → Y` along `C`
  and semipositive backgrounds `θ` on `Y × W` (zero potentials):
  `μ_θ(S) ≤ μ_{ν^*θ}(ν⁻¹ S)` for EVERY set `S`, `ν = g × id`.  Over `(Y ∖ C) × W` the map `ν` is an
  isomorphism (`ProductMapIsomorphismOver.isIsomorphismOver_prodMap`) and the measures correspond
  (`ModificationMassInvariance.globalMixedMeasure_restrict_preimage_eq_map`); `C × W` carries no
  mass.
* `le_globalMixedMeasure_preimage_prodMap_of_isBlowupSequence` — the same for a blowup sequence, by
  induction (`(f ∘ g)^* = g^* f^*` up to geometric equality).
-/

noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Manifold ContDiff ENNReal

universe u

namespace SGPT.Foundations.Analysis.Pending.ProductMapMixedMeasure

open FirstPass FirstPass.HolomorphicMaps FirstPass.BlowupSequences GlobalNonPluripolar
  ModificationMassInvariance ProductMapIsomorphismOver ProductComplexManifold
open scoped ProductComplexManifold

variable {n m : ℕ} {W : Type u} [TopologicalSpace W] [ChartedSpace (ComplexModel m) W]
  [IsComplexManifold m W] [MeasurableSpace W] [BorelSpace W] [CompactSpace W]

/-- Zero is a `θ`-psh potential of a semipositive closed form. -/
theorem thetaPlurisubharmonic_zero_of_isSemipositive {N : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel N) M] [IsComplexManifold N M] {θ : ClosedRealOneOneForm N M}
    (hθ : θ.val.IsSemipositive) : ThetaPlurisubharmonic θ.val (fun _ => 0) :=
  (LocalPotentials.thetaPlurisubharmonic_zero_iff _).mpr hθ

/-- **`C × W` is not charged** when `C` is analytic with empty interior. -/
theorem globalMixedMeasure_prod_univ_eq_zero {Y : Type u} [TopologicalSpace Y]
    [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y] [MeasurableSpace Y] [BorelSpace Y]
    [CompactSpace Y] {C : Set Y} (hC : IsComplexAnalyticSubset (n := n) C) (hint : interior C = ∅)
    {θ : Fin (n + m) → ClosedRealOneOneForm (n + m) (Y × W)} {u : Fin (n + m) → Y × W → EReal}
    (hu : ∀ i, ThetaPlurisubharmonic (θ i).val (u i)) :
    globalMixedMeasure θ u hu (C ×ˢ (univ : Set W)) = 0 := by
  have hA : IsComplexAnalyticSubset (n := n + m) (Prod.fst ⁻¹' C : Set (Y × W)) :=
    AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage contMDiff_fst hC
  have hint' : interior (Prod.fst ⁻¹' C : Set (Y × W)) = ∅ := by
    rw [← Set.prod_univ, interior_prod_eq, hint, Set.empty_prod]
  rw [Set.prod_univ]
  exact globalMixedMeasure_doesNotChargeManifoldPluripolar hu _
    (manifoldLocallyPluripolar_of_isComplexAnalyticSubset hA hint')

/-- **One blowup**: pulling back along `g × id` does not lose mass on preimages. -/
theorem le_globalMixedMeasure_preimage_prodMap_of_isBlowupAlong {Y Z : Type u} [TopologicalSpace Y]
    [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y] [MeasurableSpace Y] [BorelSpace Y]
    [CompactSpace Y] [TopologicalSpace Z] [ChartedSpace (ComplexModel n) Z]
    [IsComplexManifold n Z] [MeasurableSpace Z] [BorelSpace Z] [CompactSpace Z]
    {C : Set Y} {g : Z → Y} (hg : IsBlowupAlong n C g)
    (θ : Fin (n + m) → ClosedRealOneOneForm (n + m) (Y × W))
    (hu : ∀ i, ThetaPlurisubharmonic (θ i).val (fun _ => 0))
    (hu' : ∀ i, ThetaPlurisubharmonic (pullbackTuple
      (contMDiff_prodMap hg.contMDiff (contMDiff_id (I := 𝓘(ℂ, ComplexModel m)) (n := ∞))) θ i).val
      (fun _ => 0))
    (S : Set (Y × W)) :
    globalMixedMeasure θ (fun _ _ => 0) hu S ≤
      globalMixedMeasure (pullbackTuple
        (contMDiff_prodMap hg.contMDiff (contMDiff_id (I := 𝓘(ℂ, ComplexModel m)) (n := ∞))) θ)
        (fun _ _ => 0) hu' (Prod.map g (id : W → W) ⁻¹' S) := by
  classical
  set ν : Z × W → Y × W := Prod.map g (id : W → W) with hνdef
  have hν : ContMDiff 𝓘(ℂ, ComplexModel (n + m)) 𝓘(ℂ, ComplexModel (n + m)) ∞ ν :=
    contMDiff_prodMap hg.contMDiff contMDiff_id
  have hseq : IsBlowupSequence n Y Z (id ∘ g) :=
    IsBlowupSequence.step id C g IsBlowupSequence.refl hg
  have hsurj : Function.Surjective g :=
    (StrictTransformComposition.IsBlowupSequence.compactSpace_surjective hseq).2
  rcases isEmpty_or_nonempty (Z × W) with hE | hNe
  · -- then `Y × W` is empty as well
    have hYW : IsEmpty (Y × W) := ⟨fun p => by
      obtain ⟨z, hz⟩ := hsurj p.1
      exact hE.false (z, p.2)⟩
    rw [Set.eq_empty_of_isEmpty S, measure_empty]
    exact bot_le
  set N : Set (Y × W) := Cᶜ ×ˢ (univ : Set W) with hNdef
  have hN : IsOpen N := hg.1.1.isOpen_compl.prod isOpen_univ
  have hiso : IsIsomorphismOver (n + m) ν N :=
    isIsomorphismOver_prodMap hg.contMDiff
      (BlowupIsomorphismOff.isIsomorphismOver_compl_of_isBlowupAlong hg)
  set μY := globalMixedMeasure θ (fun _ _ => 0) hu with hμY
  set μZ := globalMixedMeasure (pullbackTuple hν θ) (fun _ _ => 0) hu' with hμZ
  have hnat := globalMixedMeasure_restrict_preimage_eq_map hν hN hiso hu hu'
  have hCan : IsComplexAnalyticSubset (n := n) C :=
    AnalyticSubsetPreimage.isComplexAnalyticSubset_of_isClosedSubmanifold hg.1
  have hC0 : μY (C ×ˢ (univ : Set W)) = 0 := globalMixedMeasure_prod_univ_eq_zero hCan hg.2.1 hu
  have hs'm : AEMeasurable (invOver ν N) (μY.restrict N) :=
    (continuousOn_invOver hν hN hiso).aemeasurable hN.measurableSet
  have hsub : S ∩ N ⊆ invOver ν N ⁻¹' (ν ⁻¹' S) ∩ N := by
    rintro x ⟨hxS, hxN⟩
    refine ⟨?_, hxN⟩
    show ν (invOver ν N x) ∈ S
    rw [(invOver_mem hiso hxN).2]
    exact hxS
  calc μY S ≤ μY (S ∩ N) + μY (C ×ˢ (univ : Set W)) := by
          refine (measure_mono fun x hx => ?_).trans (measure_union_le _ _)
          by_cases hxC : x.1 ∈ C
          · exact Or.inr ⟨hxC, mem_univ _⟩
          · exact Or.inl ⟨hx, hxC, mem_univ _⟩
    _ = μY (S ∩ N) := by rw [hC0, add_zero]
    _ ≤ (μY.restrict N) (invOver ν N ⁻¹' (ν ⁻¹' S)) := by
          rw [Measure.restrict_apply' hN.measurableSet]
          exact measure_mono hsub
    _ ≤ ((μY.restrict N).map (invOver ν N)) (ν ⁻¹' S) := Measure.le_map_apply hs'm _
    _ = (μZ.restrict (ν ⁻¹' N)) (ν ⁻¹' S) := by rw [hνdef, ← hnat]
    _ ≤ μZ (ν ⁻¹' S) := Measure.restrict_le_self _

/-- **A blowup sequence**: for a blowup sequence `μ : Y → X` and semipositive backgrounds `θ` on
`X × W` (zero potentials), pulling back along `μ × id` does not lose mass on preimages:
`μ_θ(S) ≤ μ_{(μ × id)^*θ}((μ × id)⁻¹ S)` for every set `S`. -/
theorem le_globalMixedMeasure_preimage_prodMap_of_isBlowupSequence {X : Type u}
    [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
    [mX : MeasurableSpace X] [bX : BorelSpace X] [CompactSpace X] {Y : Type u}
    [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y] {μ : Y → X}
    (hμ : IsBlowupSequence n X Y μ) :
    ∀ [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y]
      (θ : Fin (n + m) → ClosedRealOneOneForm (n + m) (X × W))
      (_hθ : ∀ i, (θ i).val.IsSemipositive)
      (hu : ∀ i, ThetaPlurisubharmonic (θ i).val (fun _ => 0))
      (hu' : ∀ i, ThetaPlurisubharmonic (pullbackTuple
        (contMDiff_prodMap hμ.contMDiff (contMDiff_id (I := 𝓘(ℂ, ComplexModel m)) (n := ∞))) θ i).val
        (fun _ => 0))
      (S : Set (X × W)),
      globalMixedMeasure θ (fun _ _ => 0) hu S ≤
        globalMixedMeasure (pullbackTuple
          (contMDiff_prodMap hμ.contMDiff (contMDiff_id (I := 𝓘(ℂ, ComplexModel m)) (n := ∞))) θ)
          (fun _ _ => 0) hu' (Prod.map μ (id : W → W) ⁻¹' S) := by
  induction hμ with
  | refl =>
      intro mY bY cY θ _ hu hu' S
      have hm : mY = mX := bY.measurable_eq.trans bX.measurable_eq.symm
      subst hm
      have hgeom : ∀ i, (θ i).val.GeometricallyEq (pullbackTuple
          (contMDiff_prodMap (contMDiff_id (I := 𝓘(ℂ, ComplexModel n)) (n := ∞))
            (contMDiff_id (I := 𝓘(ℂ, ComplexModel m)) (n := ∞))) θ i).val := fun i =>
        (SmoothRealForm.pullback_id_geometricallyEq (θ i).val).symm
      rw [globalMixedMeasure_congr_geometricallyEq hgeom hu hu']
      exact le_of_eq rfl
  | @step Y' Z' _ _ _ _ _ _ f C g hf hg ih =>
      intro mZ bZ cZ θ hθ hu hu' S
      let : MeasurableSpace Y' := borel Y'
      have : BorelSpace Y' := ⟨rfl⟩
      have hYc := StrictTransformComposition.IsBlowupSequence.compactSpace_surjective hf
      have : CompactSpace Y' := hYc.1
      have hνf : ContMDiff 𝓘(ℂ, ComplexModel (n + m)) 𝓘(ℂ, ComplexModel (n + m)) ∞
          (Prod.map f (id : W → W)) := contMDiff_prodMap hf.contMDiff contMDiff_id
      have hνg : ContMDiff 𝓘(ℂ, ComplexModel (n + m)) 𝓘(ℂ, ComplexModel (n + m)) ∞
          (Prod.map g (id : W → W)) := contMDiff_prodMap hg.contMDiff contMDiff_id
      have hθf : ∀ i, (pullbackTuple hνf θ i).val.IsSemipositive := fun i =>
        ClosedRealOneOneForm.pullback_isSemipositive hνf (hθ i)
      have hvf : ∀ i, ThetaPlurisubharmonic (pullbackTuple hνf θ i).val (fun _ => 0) := fun i =>
        thetaPlurisubharmonic_zero_of_isSemipositive (hθf i)
      have hvg : ∀ i, ThetaPlurisubharmonic (pullbackTuple hνg (pullbackTuple hνf θ) i).val
          (fun _ => 0) := fun i =>
        thetaPlurisubharmonic_zero_of_isSemipositive
          (ClosedRealOneOneForm.pullback_isSemipositive hνg (hθf i))
      have hgeom : ∀ i, (pullbackTuple
          (contMDiff_prodMap (hf.contMDiff.comp hg.contMDiff)
            (contMDiff_id (I := 𝓘(ℂ, ComplexModel m)) (n := ∞))) θ i).val.GeometricallyEq
          (pullbackTuple hνg (pullbackTuple hνf θ) i).val := fun i =>
        SmoothRealForm.pullback_comp_geometricallyEq hνf hνg (θ i).val
      calc globalMixedMeasure θ (fun _ _ => 0) hu S
          ≤ globalMixedMeasure (pullbackTuple hνf θ) (fun _ _ => 0) hvf
              (Prod.map f (id : W → W) ⁻¹' S) := ih θ hθ hu hvf S
        _ ≤ globalMixedMeasure (pullbackTuple hνg (pullbackTuple hνf θ)) (fun _ _ => 0) hvg
              (Prod.map g (id : W → W) ⁻¹' (Prod.map f (id : W → W) ⁻¹' S)) :=
            le_globalMixedMeasure_preimage_prodMap_of_isBlowupAlong hg _ hvf hvg _
        _ = globalMixedMeasure (pullbackTuple
              (contMDiff_prodMap (hf.contMDiff.comp hg.contMDiff)
                (contMDiff_id (I := 𝓘(ℂ, ComplexModel m)) (n := ∞))) θ) (fun _ _ => 0) hu'
              (Prod.map (f ∘ g) (id : W → W) ⁻¹' S) := by
            rw [globalMixedMeasure_congr_geometricallyEq hgeom hu' hvg]
            rfl

end SGPT.Foundations.Analysis.Pending.ProductMapMixedMeasure
