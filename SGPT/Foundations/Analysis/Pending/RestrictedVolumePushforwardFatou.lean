import SGPT.Foundations.Analysis.Pending.RestrictedVolumePushforwardMass
import SGPT.Foundations.Analysis.Pending.PatchDensityMeasurability

set_option autoImplicit false

/-!
# The mass identity across the centre in its Fatou form

`Pending.RestrictedVolumePushforwardMass.acTopMass_le_of_patchDensity_le` compares the
restricted mass of the strict transform with that of ONE downstairs presentation, from a
POINTWISE density comparison.  That is not the shape CT22's Lemma 4.3 supplies:
the pushed-forward current `g_*(T' − ε₀Θ_E)` has no analytic singularities, CT22
regularizes it and applies **Fatou**, and no fixed Demailly regularization dominates the
absolutely continuous part pointwise.

The honest reduction therefore compares the upstairs density with the `liminf` of the
densities of a SEQUENCE of downstairs presentations.  All of the geometry is already
abstracted in
`RestrictedVolumePushforwardMass.acTopMass_le_of_patchDensity_le_general`; what this file
adds is the two measure-theoretic facts that turn a `liminf` weight into a `liminf` of
masses:

* Fatou's lemma on each parameter piece, which needs the density to be a genuine
  measurable integrand — `Pending.PatchDensityMeasurability`;
* superadditivity of `liminf` along a finite sum, `finsetSum_liminf_le`.

The bad set to avoid is now the union of the pole sets of the whole sequence, which is
exactly what `hpoles` supplies term by term.
-/

open Set Filter MeasureTheory
open scoped Topology Manifold ContDiff ENNReal

universe u

namespace SGPT.Foundations.Analysis.Pending.RestrictedVolumePushforwardFatou

open FirstPass FirstPass.PositiveClasses FirstPass.BlowupSequences
  FirstPass.NumericalRestrictedVolumeScaffold FirstPass.NumericalRestrictedVolume
  FirstPass.ClosedIrreducibleAnalyticSubvariety

noncomputable section

/-- **`liminf` is superadditive along a finite sum** in `ℝ≥0∞`.  Mathlib's `le_liminf_add`
needs an additive group, which `ℝ≥0∞` is not; the tail infima are monotone, so the finite
sum commutes with the supremum defining the `liminf`. -/
theorem finsetSum_liminf_le {ι : Type*} (s : Finset ι) (a : ι → ℕ → ℝ≥0∞) :
    ∑ i ∈ s, liminf (fun m => a i m) atTop ≤ liminf (fun m => ∑ i ∈ s, a i m) atTop := by
  classical
  calc ∑ i ∈ s, liminf (fun m => a i m) atTop
      = ∑ i ∈ s, ⨆ n : ℕ, ⨅ m ≥ n, a i m :=
        Finset.sum_congr rfl fun i _ => liminf_eq_iSup_iInf_of_nat
    _ = ⨆ n : ℕ, ∑ i ∈ s, ⨅ m ≥ n, a i m :=
        ENNReal.finsetSum_iSup_of_monotone fun i n n' hnn' =>
          le_iInf₂ fun m hm => iInf₂_le m (le_trans hnn' hm)
    _ ≤ ⨆ n : ℕ, ⨅ m ≥ n, ∑ i ∈ s, a i m :=
        iSup_mono fun n => le_iInf₂ fun m hm =>
          Finset.sum_le_sum fun i _ => iInf₂_le m hm
    _ = liminf (fun m => ∑ i ∈ s, a i m) atTop := liminf_eq_iSup_iInf_of_nat.symm

variable {n : ℕ}
  {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
  {Z : Type u} [TopologicalSpace Z] [ChartedSpace (ComplexModel n) Z] [IsComplexManifold n Z]

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- A regular-piece family avoiding a set avoids every subset of it. -/
def _root_.SGPT.Foundations.Analysis.FirstPass.NumericalRestrictedVolume.RegularPieceFamily.monoAvoid
    {V : ClosedIrreducibleAnalyticSubvariety n M} {avoid avoid' : Set M}
    (F : RegularPieceFamily V avoid) (h : avoid' ⊆ avoid) :
    RegularPieceFamily V avoid' where
  size := F.size
  patch := F.patch
  piece := F.piece
  measurableSet_piece := F.measurableSet_piece
  piece_subset := F.piece_subset
  image_subset_regularLocus := F.image_subset_regularLocus
  image_disjoint_avoid := fun i => (F.image_disjoint_avoid i).mono_right h
  pairwise_disjoint_image := F.pairwise_disjoint_image

/-- **The mass identity across the centre, Fatou form.**  The upstairs restricted mass is
bounded by the `liminf` of the masses of a sequence of downstairs presentations as soon as
the upstairs parameter density is bounded by the `liminf` of their parameter densities,
whenever the two patches are related by the chain-rule identities of
`RegularPatchPushforward`. -/
theorem acTopMass_le_liminf_of_patchDensity_liminf_le {g : Z → Y}
    (hg : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ g)
    {omegaY : KahlerBackground n Y} {alphaY : RealBottChern n Y} {epsY : PositiveError}
    {omegaZ : KahlerBackground n Z} {alphaZ : RealBottChern n Z} {epsZ : PositiveError}
    {W : ClosedIrreducibleAnalyticSubvariety n Y}
    {Wt : ClosedIrreducibleAnalyticSubvariety n Z} (hdim : Wt.dim = W.dim)
    {A : Set Z} (hAa : IsComplexAnalyticSubset (n := n) A)
    (hAexc : exceptionalLocus n g ⊆ A) (hAinj : InjOn g Aᶜ)
    (hWtA : ¬ (Wt.withDim W.dim hdim).carrier ⊆ A)
    (hWO : ∀ x ∈ Aᶜ, x ∈ (Wt.withDim W.dim hdim).carrier ↔ g x ∈ W.carrier)
    (p : ℕ → AdmissibleRestrictedCurrentPresentation omegaY alphaY W epsY)
    (q : AdmissibleRestrictedCurrentPresentation omegaZ alphaZ
      (Wt.withDim W.dim hdim) epsZ)
    (hpoles : ∀ z ∈ Aᶜ, z ∉ poleSet q.potential → ∀ m, g z ∉ poleSet (p m).potential)
    (hdens : ∀ (P : RegularPatch W) (Q : RegularPatch (Wt.withDim W.dim hdim))
      (v v' : ComplexModel W.dim), v ∈ P.parameterDomain → v' ∈ Q.parameterDomain →
      Q.toManifold v' ∉ A → g (Q.toManifold v') = P.toManifold v →
      Q.toManifold v' ∉ poleSet q.potential →
      (∀ β : ClosedRealOneOneForm n Y,
        ((ClosedRealOneOneForm.pullback hg β).val.coeff (complexChartAt (n := n) Q.center)
            (Q.coordinateParametrization v')).compContinuousLinearMap
          (fderiv ℝ Q.coordinateParametrization v') =
        (β.val.coeff (complexChartAt (n := n) P.center)
            (P.coordinateParametrization v)).compContinuousLinearMap
          (fderiv ℝ P.coordinateParametrization v)) →
      (∀ u : Y → ℝ,
        (∀ᶠ y in 𝓝 (P.coordinateParametrization v),
          ContDiffAt ℝ ∞ (fun y => u ((complexChartAt (n := n) P.center).val.symm y)) y) →
        (smoothDDC (fun y => u (g ((complexChartAt (n := n) Q.center).val.symm y)))
            (Q.coordinateParametrization v')).compContinuousLinearMap
          (fderiv ℝ Q.coordinateParametrization v') =
        (smoothDDC (fun y => u ((complexChartAt (n := n) P.center).val.symm y))
            (P.coordinateParametrization v)).compContinuousLinearMap
          (fderiv ℝ P.coordinateParametrization v)) →
      ENNReal.ofReal (patchDensity q Q v') ≤
        liminf (fun m => ENNReal.ofReal (patchDensity (p m) P v)) atTop) :
    acTopMass q ≤ liminf (fun m => acTopMass (p m)) atTop := by
  classical
  refine RestrictedVolumePushforwardMass.acTopMass_le_of_patchDensity_le_general hg hdim
    hAa hAexc hAinj hWtA hWO q (avoid := ⋃ m, poleSet (p m).potential)
    (Φ := fun P v => liminf (fun m => ENNReal.ofReal (patchDensity (p m) P v)) atTop)
    (B := liminf (fun m => acTopMass (p m)) atTop)
    (fun z hz hzq hmem => ?_) hdens (fun F => ?_)
  · obtain ⟨m, hm⟩ := mem_iUnion.mp hmem
    exact hpoles z hz hzq m hm
  · have hsub : ∀ m, poleSet (p m).potential ⊆ ⋃ m, poleSet (p m).potential :=
      fun m => subset_iUnion (fun m => poleSet (p m).potential) m
    have hpiece : ∀ (k : Fin F.size),
        ∫⁻ v in F.piece k,
            liminf (fun m => ENNReal.ofReal (patchDensity (p m) (F.patch k) v)) atTop ≤
          liminf (fun m => ∫⁻ v in F.piece k,
            ENNReal.ofReal (patchDensity (p m) (F.patch k) v)) atTop := by
      intro k
      refine lintegral_liminf_le' fun m => ?_
      refine PatchDensityMeasurability.aemeasurable_ofReal_patchDensity (p m) (F.patch k)
        (F.measurableSet_piece k) (F.piece_subset k) fun w hw hpole => ?_
      exact (F.image_disjoint_avoid k).le_bot
        ⟨mem_image_of_mem _ hw, hsub m hpole⟩
    calc ∑ k, ∫⁻ v in F.piece k,
            liminf (fun m => ENNReal.ofReal (patchDensity (p m) (F.patch k) v)) atTop
        ≤ ∑ k, liminf (fun m => ∫⁻ v in F.piece k,
            ENNReal.ofReal (patchDensity (p m) (F.patch k) v)) atTop :=
          Finset.sum_le_sum fun k _ => hpiece k
      _ ≤ liminf (fun m => ∑ k, ∫⁻ v in F.piece k,
            ENNReal.ofReal (patchDensity (p m) (F.patch k) v)) atTop :=
          finsetSum_liminf_le _ _
      _ ≤ liminf (fun m => acTopMass (p m)) atTop := by
          refine liminf_le_liminf (Eventually.of_forall fun m => ?_)
          refine le_trans (le_of_eq rfl) (le_iSup
            (fun F : RegularPieceFamily W (poleSet (p m).potential) =>
              ∑ i, ∫⁻ w in F.piece i,
                ENNReal.ofReal (patchDensity (p m) (F.patch i) w)) (F.monoAvoid (hsub m)))

/-- **The Fatou form for an actual blowup**, with the bad set taken to be the exceptional
locus.  Its hypotheses are exactly those of CT22's Lemma 4.3: `W` is not contained in
`g(\operatorname{Exc} g)`, and nothing further is asked of the centre. -/
theorem acTopMass_le_liminf_of_patchDensity_liminf_le_of_isBlowupAlong [CompactSpace Y]
    {C : Set Y} {g : Z → Y} (hg : IsBlowupAlong n C g)
    {omegaY : KahlerBackground n Y} {alphaY : RealBottChern n Y} {epsY : PositiveError}
    {omegaZ : KahlerBackground n Z} {alphaZ : RealBottChern n Z} {epsZ : PositiveError}
    (W : ClosedIrreducibleAnalyticSubvariety n Y)
    (hW : ¬ W.carrier ⊆ g '' exceptionalLocus n g)
    (Wt : ClosedIrreducibleAnalyticSubvariety n Z)
    (hWt : Wt.carrier = strictTransform n g W.carrier) (hdim : Wt.dim = W.dim)
    (p : ℕ → AdmissibleRestrictedCurrentPresentation omegaY alphaY W epsY)
    (q : AdmissibleRestrictedCurrentPresentation omegaZ alphaZ
      (Wt.withDim W.dim hdim) epsZ)
    (hpoles : ∀ z ∈ (exceptionalLocus n g)ᶜ, z ∉ poleSet q.potential →
      ∀ m, g z ∉ poleSet (p m).potential)
    (hdens : ∀ (P : RegularPatch W) (Q : RegularPatch (Wt.withDim W.dim hdim))
      (v v' : ComplexModel W.dim), v ∈ P.parameterDomain → v' ∈ Q.parameterDomain →
      Q.toManifold v' ∉ exceptionalLocus n g → g (Q.toManifold v') = P.toManifold v →
      Q.toManifold v' ∉ poleSet q.potential →
      (∀ β : ClosedRealOneOneForm n Y,
        ((ClosedRealOneOneForm.pullback hg.contMDiff β).val.coeff
            (complexChartAt (n := n) Q.center)
            (Q.coordinateParametrization v')).compContinuousLinearMap
          (fderiv ℝ Q.coordinateParametrization v') =
        (β.val.coeff (complexChartAt (n := n) P.center)
            (P.coordinateParametrization v)).compContinuousLinearMap
          (fderiv ℝ P.coordinateParametrization v)) →
      (∀ u : Y → ℝ,
        (∀ᶠ y in 𝓝 (P.coordinateParametrization v),
          ContDiffAt ℝ ∞ (fun y => u ((complexChartAt (n := n) P.center).val.symm y)) y) →
        (smoothDDC (fun y => u (g ((complexChartAt (n := n) Q.center).val.symm y)))
            (Q.coordinateParametrization v')).compContinuousLinearMap
          (fderiv ℝ Q.coordinateParametrization v') =
        (smoothDDC (fun y => u ((complexChartAt (n := n) P.center).val.symm y))
            (P.coordinateParametrization v)).compContinuousLinearMap
          (fderiv ℝ P.coordinateParametrization v)) →
      ENNReal.ofReal (patchDensity q Q v') ≤
        liminf (fun m => ENNReal.ofReal (patchDensity (p m) P v)) atTop) :
    acTopMass q ≤ liminf (fun m => acTopMass (p m)) atTop := by
  have hAa : IsComplexAnalyticSubset (n := n) (exceptionalLocus n g) :=
    RestrictedVolumePushforwardMass.isComplexAnalyticSubset_exceptionalLocus hg
  have hWtA : ¬ (Wt.withDim W.dim hdim).carrier ⊆ exceptionalLocus n g := by
    rw [ClosedIrreducibleAnalyticSubvariety.withDim_carrier, hWt,
      ← ExceptionalFibres.preimage_image_exceptionalLocus hg]
    exact StrictTransformLocus.not_strictTransform_subset_preimage hg W hW
      (ExceptionalImageAnalytic.isComplexAnalyticSubset_image_exceptionalLocus hg) hW
  have hWO : ∀ x ∈ (exceptionalLocus n g)ᶜ,
      x ∈ (Wt.withDim W.dim hdim).carrier ↔ g x ∈ W.carrier := by
    intro x hx
    rw [ClosedIrreducibleAnalyticSubvariety.withDim_carrier, hWt]
    exact RestrictedVolumePullbackLower.mem_strictTransform_iff hg.contMDiff.continuous
      W.isClosed_carrier hx
  exact acTopMass_le_liminf_of_patchDensity_liminf_le hg.contMDiff hdim hAa Subset.rfl
    (RestrictedVolumePushforwardMass.injOn_compl_exceptionalLocus hg) hWtA hWO p q hpoles hdens

end

end SGPT.Foundations.Analysis.Pending.RestrictedVolumePushforwardFatou
