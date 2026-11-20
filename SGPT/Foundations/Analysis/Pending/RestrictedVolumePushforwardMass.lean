import SGPT.Foundations.Analysis.Pending.RegularPatchPushforward
import SGPT.Foundations.Analysis.Pending.RestrictedVolumePullbackLower
import SGPT.Foundations.Analysis.Pending.BlowupIsomorphismOff
import SGPT.Foundations.Analysis.Pending.AnalyticSubsetPreimage
import SGPT.Foundations.Analysis.Pending.ExceptionalImageAnalytic

set_option autoImplicit false

/-!
# The restricted mass of the strict transform, measured downstairs

Source: CT22, Lemma 4.3 (the second inequality, the step "`g` restricts to a biholomorphism
from `W̃ ∖ E` onto `W ∖ g(E)`, and the parameters of `W̃` lying over the centre form a null
set, so the two restricted masses agree"); blueprint `ana:rv-pushforward-envelope`.

`Pending.RestrictedVolumePullbackLower.acTopMass_le_pullbackPresentation` does this in the
easy direction (a downstairs family is transported upstairs).  Here is the converse
reduction, which is the one the pushforward across the centre needs:

> **all** of the measure theory in `acTopMass q ≤ acTopMass p` — covering each upstairs
> piece by countably many parameter balls, discarding the null set of parameters over the
> bad set, disjointifying, translating each ball to the origin and passing to the limit —
> is discharged from a POINTWISE density comparison between an upstairs patch and the
> patch it pushes to.

The bad set `A` is abstract: any closed analytic subset of `Z` that contains the
exceptional locus, off which `g` is injective, and which does not swallow `W̃`.  For a
blowup along `C` one takes `A = g⁻¹ C` (`Pending.BlowupIsomorphismOff`).

What is deliberately NOT proved here is the density comparison itself: that is the
analytic heart of CT22's pushforward (the class of `Θ_E` pushes forward to zero, and the
regularizations of `g_*S` converge), and it is the named input
`Pending.ExceptionalPushforwardMass.acTopMass_le_restrictedMassEnvelope_of_exceptionalCorrection`.
The hypothesis `hdens` below is stated in exactly the shape of
`RestrictedVolumePullbackLower.patchDensity_le_pullback`, with the two patches exchanged.
-/

open Set Filter MeasureTheory
open scoped Topology Manifold ContDiff ENNReal

universe u

namespace SGPT.Foundations.Analysis.Pending.RestrictedVolumePushforwardMass

open FirstPass FirstPass.PositiveClasses FirstPass.BlowupSequences
  FirstPass.NumericalRestrictedVolumeScaffold FirstPass.NumericalRestrictedVolume
  FirstPass.ClosedIrreducibleAnalyticSubvariety

noncomputable section

variable {n : ℕ}
  {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
  {Z : Type u} [TopologicalSpace Z] [ChartedSpace (ComplexModel n) Z] [IsComplexManifold n Z]

/-- **The measure-theoretic half of the mass identity across the centre, with the
downstairs weight left abstract.**

`g` holomorphic, `W̃ ⊆ Z` and `W ⊆ Y` of the same dimension, `A ⊆ Z` a closed analytic set
containing the exceptional locus, off which `g` is injective and on which `W̃` does not
concentrate, and `W̃ ∩ Aᶜ = g⁻¹ W ∩ Aᶜ`.  Then **all** the measure theory of the
comparison — covering each upstairs piece by countably many parameter balls, discarding
the null set of parameters over `A`, disjointifying, translating each ball to the origin
and passing to the limit — is discharged from

* a set `avoid ⊆ Y` that the pushed-forward good points miss (`hpoles`);
* a weight `Φ` on downstairs patch parameters dominating the upstairs density at every
  pair of patches related by the chain-rule identities of `RegularPatchPushforward`
  (`hdens`); and
* a bound `B` on the `Φ`-mass of every regular-piece family of `W` avoiding `avoid`
  (`hsup`).

Taking `Φ = ofReal ∘ patchDensity p`, `avoid = poleSet p.potential` and `B = acTopMass p`
gives `acTopMass_le_of_patchDensity_le`; taking `Φ` a `liminf` over a sequence of
presentations gives the Fatou form of
`Pending.RestrictedVolumePushforwardFatou`, which is the shape CT22's regularization
argument actually supplies. -/
theorem acTopMass_le_of_patchDensity_le_general {g : Z → Y}
    (hg : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ g)
    {omegaZ : KahlerBackground n Z} {alphaZ : RealBottChern n Z} {epsZ : PositiveError}
    {W : ClosedIrreducibleAnalyticSubvariety n Y}
    {Wt : ClosedIrreducibleAnalyticSubvariety n Z} (hdim : Wt.dim = W.dim)
    {A : Set Z} (hAa : IsComplexAnalyticSubset (n := n) A)
    (hAexc : exceptionalLocus n g ⊆ A) (hAinj : InjOn g Aᶜ)
    (hWtA : ¬ (Wt.withDim W.dim hdim).carrier ⊆ A)
    (hWO : ∀ x ∈ Aᶜ, x ∈ (Wt.withDim W.dim hdim).carrier ↔ g x ∈ W.carrier)
    (q : AdmissibleRestrictedCurrentPresentation omegaZ alphaZ
      (Wt.withDim W.dim hdim) epsZ)
    {avoid : Set Y} {Φ : RegularPatch W → ComplexModel W.dim → ℝ≥0∞} {B : ℝ≥0∞}
    (hpoles : ∀ z ∈ Aᶜ, z ∉ poleSet q.potential → g z ∉ avoid)
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
      ENNReal.ofReal (patchDensity q Q v') ≤ Φ P v)
    (hsup : ∀ F : RegularPieceFamily W avoid,
      ∑ k, ∫⁻ v in F.piece k, Φ (F.patch k) v ≤ B) :
    acTopMass q ≤ B := by
  classical
  have hAo : IsOpen Aᶜ := hAa.isClosed.isOpen_compl
  have hWA : ∀ U : Set Z, IsOpen U → ((Wt.withDim W.dim hdim).carrier ∩ U).Nonempty →
      ¬ (Wt.withDim W.dim hdim).carrier ∩ U ⊆ A := fun U hU hne hsub =>
    hWtA (StrictTransformLocus.subset_of_inter_isOpen_subset (Wt.withDim W.dim hdim) hAa hU hne
      hsub)
  -- local pushforward data at every good parameter
  have hloc : ∀ (Q : RegularPatch (Wt.withDim W.dim hdim)) (v₀ : ComplexModel W.dim), v₀ ∈ Q.parameterDomain →
      Q.toManifold v₀ ∉ A → ∃ (P : RegularPatch W) (r : ℝ), 0 < r ∧
        ∀ v ∈ Metric.ball v₀ r, v ∈ Q.parameterDomain ∧ v - v₀ ∈ P.parameterDomain ∧
          g (Q.toManifold v) = P.toManifold (v - v₀) ∧
          (Q.toManifold v ∉ poleSet q.potential →
            ENNReal.ofReal (patchDensity q Q v) ≤ Φ P (v - v₀)) := by
    intro Q v₀ hv₀ hA
    obtain ⟨P, r, hr, hQ⟩ := RegularPatchPushforward.exists_regularPatch_pushforward hg hdim
      hAo hWO Q hv₀ hA (fun h => hA (hAexc h))
    refine ⟨P, r, hr, fun v hv => ?_⟩
    obtain ⟨hvQ, hvP, hvO, -, hgv, hβ, hu⟩ := hQ v hv
    exact ⟨hvQ, hvP, hgv, fun hnp => hdens P Q (v - v₀) v hvP hvQ hvO hgv hnp hβ hu⟩
  have : Nonempty (RegularPatch W) := RestrictedVolumePullbackLower.nonempty_regularPatch W
  choose! Pf rf hrf hPf using hloc
  refine iSup_le fun F => ?_
  set Qp : Fin F.size → RegularPatch (Wt.withDim W.dim hdim) := F.patch with hQp
  set G : Fin F.size → Set (ComplexModel W.dim) := fun i =>
    F.piece i ∩ ((Qp i).parameterDomain ∩ (Qp i).toManifold ⁻¹' Aᶜ) with hGdef
  set R : Fin F.size → ComplexModel W.dim → ℝ := fun i v₀ => if v₀ ∈ G i then rf (Qp i) v₀ else 0
    with hRdef
  have hGmeas : ∀ i, MeasurableSet (G i) := fun i =>
    (F.measurableSet_piece i).inter
      ((RegularPatchNeighborhood.RegularPatch.continuousOn_toManifold (Qp i)).isOpen_inter_preimage
        (AdmissibleCurrentFormPositivity.RegularPatchDerivative.isOpen_parameterDomain (Qp i))
        hAo).measurableSet
  have hcover : ∀ i, ∃ c : ℕ → ComplexModel W.dim, G i ⊆ ⋃ j, Metric.ball (c j) (R i (c j)) := by
    intro i
    obtain ⟨T, hTc, hT⟩ := TopologicalSpace.isOpen_iUnion_countable
      (fun v₀ => Metric.ball v₀ (R i v₀)) (fun _ => Metric.isOpen_ball)
    obtain ⟨c, hc⟩ := (hTc.insert 0).exists_eq_range (insert_nonempty _ _)
    refine ⟨c, fun v hv => ?_⟩
    have hmem : v ∈ ⋃ v₀, Metric.ball v₀ (R i v₀) := by
      refine mem_iUnion.mpr ⟨v, Metric.mem_ball_self ?_⟩
      simp only [hRdef, if_pos hv]
      exact hrf (Qp i) v (F.piece_subset i hv.1) hv.2.2
    rw [← hT] at hmem
    obtain ⟨v₀, hv₀T, hv⟩ := mem_iUnion₂.mp hmem
    have : v₀ ∈ range c := hc ▸ mem_insert_of_mem _ hv₀T
    obtain ⟨j, rfl⟩ := this
    exact mem_iUnion.mpr ⟨j, hv⟩
  choose c hc using hcover
  set D : Fin F.size → ℕ → Set (ComplexModel W.dim) := fun i j =>
    G i ∩ disjointed (fun j => Metric.ball (c i j) (R i (c i j))) j with hDdef
  have hDmeas : ∀ i j, MeasurableSet (D i j) := fun i j =>
    (hGmeas i).inter (MeasurableSet.disjointed (fun _ => Metric.isOpen_ball.measurableSet) j)
  have hDdisj : ∀ i, Pairwise (Function.onFun Disjoint (D i)) := fun i j j' hjj' =>
    ((disjoint_disjointed _ hjj').mono inter_subset_right inter_subset_right)
  have hDgood : ∀ i j, ∀ v ∈ D i j, c i j ∈ G i ∧ v ∈ G i ∧
      v ∈ Metric.ball (c i j) (rf (Qp i) (c i j)) := by
    intro i j v hv
    have hvb : v ∈ Metric.ball (c i j) (R i (c i j)) :=
      disjointed_le (fun j => Metric.ball (c i j) (R i (c i j))) j hv.2
    by_cases hcG : c i j ∈ G i
    · refine ⟨hcG, hv.1, ?_⟩
      simpa only [hRdef, if_pos hcG] using hvb
    · simp only [hRdef, if_neg hcG, Metric.ball_zero, mem_empty_iff_false] at hvb
  set f : Fin F.size → ComplexModel W.dim → ℝ≥0∞ := fun i v =>
    ENNReal.ofReal (patchDensity q (Qp i) v) with hfdef
  set a : Fin F.size → ℕ → ℝ≥0∞ := fun i j => ∫⁻ v in D i j, f i v with hadef
  have hpiece : ∀ i, ∫⁻ v in F.piece i, f i v ≤ ⨆ N, ∑ j ∈ Finset.range N, a i j := by
    intro i
    have hnull : volume ((Qp i).parameterDomain ∩ (Qp i).toManifold ⁻¹' A) = 0 :=
      PatchParameterNull.volume_parameterDomain_inter_preimage_eq_zero (Qp i) hAa hWA
    have hsub : F.piece i ⊆ (⋃ j, D i j) ∪ ((Qp i).parameterDomain ∩ (Qp i).toManifold ⁻¹' A) := by
      intro v hv
      by_cases hvA : (Qp i).toManifold v ∈ A
      · exact Or.inr ⟨F.piece_subset i hv, hvA⟩
      · have hvG : v ∈ G i := ⟨hv, F.piece_subset i hv, hvA⟩
        refine Or.inl ?_
        have : v ∈ ⋃ j, disjointed (fun j => Metric.ball (c i j) (R i (c i j))) j := by
          rw [iUnion_disjointed]
          exact hc i hvG
        obtain ⟨j, hj⟩ := mem_iUnion.mp this
        exact mem_iUnion.mpr ⟨j, hvG, hj⟩
    calc ∫⁻ v in F.piece i, f i v
        ≤ ∫⁻ v in (⋃ j, D i j) ∪ ((Qp i).parameterDomain ∩ (Qp i).toManifold ⁻¹' A), f i v :=
          lintegral_mono_set hsub
      _ ≤ (∫⁻ v in ⋃ j, D i j, f i v) +
            ∫⁻ v in (Qp i).parameterDomain ∩ (Qp i).toManifold ⁻¹' A, f i v :=
          lintegral_union_le _ _ _
      _ = ∑' j, a i j := by
          rw [setLIntegral_measure_zero _ _ hnull, add_zero, lintegral_iUnion (hDmeas i) (hDdisj i)]
      _ = ⨆ N, ∑ j ∈ Finset.range N, a i j := ENNReal.tsum_eq_iSup_nat
  refine (Finset.sum_le_sum fun i _ => hpiece i).trans ?_
  rw [ENNReal.finsetSum_iSup_of_monotone fun i N N' hNN' =>
    Finset.sum_le_sum_of_subset (Finset.range_mono hNN')]
  refine iSup_le fun N => ?_
  set e : Fin F.size × Fin N ≃ Fin (F.size * N) := finProdFinEquiv with he
  have hmapsP : ∀ i (j : ℕ), ∀ v ∈ D i j, v - c i j ∈ (Pf (Qp i) (c i j)).parameterDomain ∧
      g ((Qp i).toManifold v) = (Pf (Qp i) (c i j)).toManifold (v - c i j) ∧
      ENNReal.ofReal (patchDensity q (Qp i) v) ≤ Φ (Pf (Qp i) (c i j)) (v - c i j) := by
    intro i j v hv
    obtain ⟨hcG, hvG, hvb⟩ := hDgood i j v hv
    obtain ⟨-, h1, h2, h3⟩ := hPf (Qp i) (c i j) (F.piece_subset i hcG.1) hcG.2.2 v hvb
    refine ⟨h1, h2, h3 fun hpv => ?_⟩
    exact disjoint_left.mp (F.image_disjoint_avoid i) ⟨v, hvG.1, rfl⟩ hpv
  have hmapsP' : ∀ i (j : ℕ) (v' : ComplexModel W.dim), v' + c i j ∈ D i j →
      v' ∈ (Pf (Qp i) (c i j)).parameterDomain ∧
      g ((Qp i).toManifold (v' + c i j)) = (Pf (Qp i) (c i j)).toManifold v' := by
    intro i j v' hv'
    have h := hmapsP i j _ hv'
    rw [add_sub_cancel_right] at h
    exact ⟨h.1, h.2.1⟩
  let Fy : RegularPieceFamily W avoid :=
    { size := F.size * N
      patch := fun k => Pf (Qp (e.symm k).1) (c (e.symm k).1 (e.symm k).2)
      piece := fun k => (fun v' : ComplexModel W.dim => v' + c (e.symm k).1 (e.symm k).2) ⁻¹'
        D (e.symm k).1 (e.symm k).2
      measurableSet_piece := fun k => (hDmeas _ _).preimage
        ((continuous_add_const (c (e.symm k).1 (e.symm k).2)).measurable :
          Measurable fun v' : ComplexModel W.dim => v' + c (e.symm k).1 (e.symm k).2)
      piece_subset := fun k v' hv' => (hmapsP' _ _ v' hv').1
      image_subset_regularLocus := fun k => by
        rintro _ ⟨v', hv', rfl⟩
        exact RegularPatchNeighborhood.RegularPatch.toManifold_mem_regularLocus _
          (hmapsP' _ _ v' hv').1
      image_disjoint_avoid := fun k => by
        refine disjoint_left.mpr ?_
        rintro _ ⟨v', hv', rfl⟩ hpole'
        obtain ⟨-, hvG, -⟩ := hDgood _ _ _ hv'
        rw [← (hmapsP' _ _ v' hv').2] at hpole'
        exact hpoles _ hvG.2.2 (fun hq' =>
          disjoint_left.mp (F.image_disjoint_avoid _) ⟨_, hvG.1, rfl⟩ hq') hpole'
      pairwise_disjoint_image := fun k k' hkk' => by
        obtain ⟨⟨i, j⟩, rfl⟩ := e.surjective k
        obtain ⟨⟨i', j'⟩, rfl⟩ := e.surjective k'
        have hne : (i, j) ≠ (i', j') := fun h => hkk' (congrArg e h)
        simp only [Equiv.symm_apply_apply]
        refine disjoint_left.mpr ?_
        rintro _ ⟨(v₁ : ComplexModel W.dim), hv₁, rfl⟩ ⟨(v₂ : ComplexModel W.dim), hv₂, heq⟩
        have hv₁' : v₁ + c i j ∈ D i j := hv₁
        have hv₂' : v₂ + c i' j' ∈ D i' j' := hv₂
        obtain ⟨-, hG₁, -⟩ := hDgood i j _ hv₁'
        obtain ⟨-, hG₂, -⟩ := hDgood i' j' _ hv₂'
        have g₁ := (hmapsP' i j v₁ hv₁').2
        have g₂ := (hmapsP' i' j' v₂ hv₂').2
        have hgeq : g ((Qp i').toManifold (v₂ + c i' j')) = g ((Qp i).toManifold (v₁ + c i j)) := by
          rw [g₁, g₂]; exact heq
        have hup : (Qp i').toManifold (v₂ + c i' j') = (Qp i).toManifold (v₁ + c i j) :=
          hAinj hG₂.2.2 hG₁.2.2 hgeq
        by_cases hi : i' = i
        · subst hi
          have hjj : (j : ℕ) ≠ j' := fun h => hne (Prod.ext rfl (Fin.ext h))
          have hw := RestrictedVolumePullbackLower.toManifold_injOn (Qp i') hG₂.2.1 hG₁.2.1 hup
          have h₂ : v₁ + c i' j ∈ D i' j' := by rw [← hw]; exact hv₂'
          exact disjoint_left.mp (hDdisj i' hjj) hv₁' h₂
        · exact disjoint_left.mp (F.pairwise_disjoint_image hi) ⟨_, hG₂.1, hup⟩ ⟨_, hG₁.1, rfl⟩ }
  refine le_trans ?_ (hsup Fy)
  calc ∑ i, ∑ j ∈ Finset.range N, a i j
      = ∑ x : Fin F.size × Fin N, a x.1 x.2 := by
        rw [Fintype.sum_prod_type]
        exact Finset.sum_congr rfl fun i _ => (Fin.sum_univ_eq_sum_range (a i) N).symm
    _ = ∑ k : Fin (F.size * N), a (e.symm k).1 (e.symm k).2 :=
        (e.symm.sum_comp fun x => a x.1 x.2).symm
    _ ≤ ∑ k : Fin (F.size * N), ∫⁻ v' in Fy.piece k, Φ (Fy.patch k) v' := by
        refine Finset.sum_le_sum fun k _ => ?_
        set i := (e.symm k).1
        set j : ℕ := ((e.symm k).2 : ℕ)
        have htr := (measurePreserving_add_right (volume : Measure (ComplexModel W.dim))
          (c i j)).setLIntegral_comp_preimage_emb
          (Homeomorph.addRight (c i j)).measurableEmbedding
          (fun v => Φ (Pf (Qp i) (c i j)) (v - c i j)) (D i j)
        simp only [add_sub_cancel_right] at htr
        change ∫⁻ v in D i j, f i v ≤ ∫⁻ v' in (fun v' => v' + c i j) ⁻¹' D i j,
          Φ (Pf (Qp i) (c i j)) v'
        rw [htr]
        refine lintegral_mono_ae ((ae_restrict_iff' (hDmeas i j)).mpr (Eventually.of_forall ?_))
        intro v hv
        exact (hmapsP i j v hv).2.2

/-- **The measure-theoretic half of the mass identity across the centre.**

`g` holomorphic, `W̃ ⊆ Z` and `W ⊆ Y` of the same dimension, `A ⊆ Z` a closed analytic set
containing the exceptional locus, off which `g` is injective and on which `W̃` does not
concentrate, and `W̃ ∩ Aᶜ = g⁻¹ W ∩ Aᶜ`.  If the potential of the downstairs presentation
is finite wherever the upstairs one is (off `A`), and if the upstairs parameter density is
pointwise dominated by the downstairs one whenever the two patches are related by the
chain-rule identities of `RegularPatchPushforward`, then the upstairs restricted mass is at
most the downstairs one. -/
theorem acTopMass_le_of_patchDensity_le {g : Z → Y}
    (hg : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ g)
    {omegaY : KahlerBackground n Y} {alphaY : RealBottChern n Y} {epsY : PositiveError}
    {omegaZ : KahlerBackground n Z} {alphaZ : RealBottChern n Z} {epsZ : PositiveError}
    {W : ClosedIrreducibleAnalyticSubvariety n Y}
    {Wt : ClosedIrreducibleAnalyticSubvariety n Z} (hdim : Wt.dim = W.dim)
    {A : Set Z} (hAa : IsComplexAnalyticSubset (n := n) A)
    (hAexc : exceptionalLocus n g ⊆ A) (hAinj : InjOn g Aᶜ)
    (hWtA : ¬ (Wt.withDim W.dim hdim).carrier ⊆ A)
    (hWO : ∀ x ∈ Aᶜ, x ∈ (Wt.withDim W.dim hdim).carrier ↔ g x ∈ W.carrier)
    (p : AdmissibleRestrictedCurrentPresentation omegaY alphaY W epsY)
    (q : AdmissibleRestrictedCurrentPresentation omegaZ alphaZ
      (Wt.withDim W.dim hdim) epsZ)
    (hpoles : ∀ z ∈ Aᶜ, z ∉ poleSet q.potential → g z ∉ poleSet p.potential)
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
      patchDensity q Q v' ≤ patchDensity p P v) :
    acTopMass q ≤ acTopMass p := by
  refine acTopMass_le_of_patchDensity_le_general hg hdim hAa hAexc hAinj hWtA hWO q
    hpoles (fun P Q v v' hv hv' hA hgv hnp hβ hu =>
      ENNReal.ofReal_le_ofReal (hdens P Q v v' hv hv' hA hgv hnp hβ hu))
    fun F => by
      refine le_trans (le_of_eq rfl) (le_iSup
        (fun F : RegularPieceFamily W (poleSet p.potential) =>
          ∑ i, ∫⁻ w in F.piece i, ENNReal.ofReal (patchDensity p (F.patch i) w)) F)


/-- **A blowup is injective off its exceptional locus.**  A fibre through a
non-exceptional point is a singleton (`ExceptionalFibres`), so two non-exceptional points
with the same image coincide. -/
theorem injOn_compl_exceptionalLocus {C : Set Y} {g : Z → Y} (hg : IsBlowupAlong n C g) :
    InjOn g (exceptionalLocus n g)ᶜ := fun _ h₁ _ _ h =>
  (ExceptionalFibres.eq_of_apply_eq_of_not_mem_exceptionalLocus hg h₁ h.symm).symm

/-- **The exceptional locus of a blowup of a compact manifold is analytic.**  It is the
full preimage of its image (`ExceptionalFibres.preimage_image_exceptionalLocus`), and that
image is analytic. -/
theorem isComplexAnalyticSubset_exceptionalLocus [CompactSpace Y] {C : Set Y} {g : Z → Y}
    (hg : IsBlowupAlong n C g) :
    IsComplexAnalyticSubset (n := n) (exceptionalLocus n g) := by
  rw [← ExceptionalFibres.preimage_image_exceptionalLocus hg]
  exact AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage hg.contMDiff
    (ExceptionalImageAnalytic.isComplexAnalyticSubset_image_exceptionalLocus hg)

/-- **The same reduction for an actual blowup, with the bad set taken to be the
exceptional locus itself.**  This is the form CT22's Lemma 4.3 needs: its hypotheses are
exactly those of the consumer, with no extra condition on the centre.  A blowup is
injective off its exceptional locus, that locus is analytic and is the full preimage of
its image, and the strict transform of a `W` not contained in `g(\operatorname{Exc} g)` is
not contained in it. -/
theorem acTopMass_le_of_patchDensity_le_of_exceptionalLocus [CompactSpace Y] {C : Set Y}
    {g : Z → Y} (hg : IsBlowupAlong n C g)
    {omegaY : KahlerBackground n Y} {alphaY : RealBottChern n Y} {epsY : PositiveError}
    {omegaZ : KahlerBackground n Z} {alphaZ : RealBottChern n Z} {epsZ : PositiveError}
    (W : ClosedIrreducibleAnalyticSubvariety n Y)
    (hW : ¬ W.carrier ⊆ g '' exceptionalLocus n g)
    (Wt : ClosedIrreducibleAnalyticSubvariety n Z)
    (hWt : Wt.carrier = strictTransform n g W.carrier) (hdim : Wt.dim = W.dim)
    (p : AdmissibleRestrictedCurrentPresentation omegaY alphaY W epsY)
    (q : AdmissibleRestrictedCurrentPresentation omegaZ alphaZ
      (Wt.withDim W.dim hdim) epsZ)
    (hpoles : ∀ z ∈ (exceptionalLocus n g)ᶜ, z ∉ poleSet q.potential → g z ∉ poleSet p.potential)
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
      patchDensity q Q v' ≤ patchDensity p P v) :
    acTopMass q ≤ acTopMass p := by
  have hAa : IsComplexAnalyticSubset (n := n) (exceptionalLocus n g) :=
    isComplexAnalyticSubset_exceptionalLocus hg
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
  exact acTopMass_le_of_patchDensity_le hg.contMDiff hdim hAa Subset.rfl
    (injOn_compl_exceptionalLocus hg) hWtA hWO p q hpoles hdens


/-- **The same reduction for an actual blowup**, with the bad set taken to be the preimage
`g⁻¹ C` of the centre.  All five geometric hypotheses of
`acTopMass_le_of_patchDensity_le` are discharged: `C` is a closed submanifold hence
analytic (`AnalyticSubsetPreimage`), the exceptional locus lies over the centre and `g` is
injective off it (`BlowupIsomorphismOff`), the strict transform is the preimage off the
exceptional locus (`RestrictedVolumePullbackLower.mem_strictTransform_iff`), and it is not
swallowed by `g⁻¹ C` (`StrictTransformLocus`).

Beyond CT22's hypothesis `W ⊄ g(Exc)` this asks `W ⊄ C`.  The two hypotheses agree
whenever `g(Exc g) = C`, which is the case for a centre of codimension at least two; that
inclusion is not among the facts the project proves about `IsBlowupAlong`, so a consumer
of CT22's Lemma 4.3 should use `acTopMass_le_of_patchDensity_le_of_exceptionalLocus`
instead, whose hypotheses are exactly the consumer's.  This variant remains available for
a consumer that does have `W ⊄ C` and prefers the centre as its bad set. -/
theorem acTopMass_le_of_patchDensity_le_of_isBlowupAlong [CompactSpace Y] {C : Set Y}
    {g : Z → Y} (hg : IsBlowupAlong n C g)
    {omegaY : KahlerBackground n Y} {alphaY : RealBottChern n Y} {epsY : PositiveError}
    {omegaZ : KahlerBackground n Z} {alphaZ : RealBottChern n Z} {epsZ : PositiveError}
    (W : ClosedIrreducibleAnalyticSubvariety n Y)
    (hW : ¬ W.carrier ⊆ g '' exceptionalLocus n g) (hWC : ¬ W.carrier ⊆ C)
    (Wt : ClosedIrreducibleAnalyticSubvariety n Z)
    (hWt : Wt.carrier = strictTransform n g W.carrier) (hdim : Wt.dim = W.dim)
    (p : AdmissibleRestrictedCurrentPresentation omegaY alphaY W epsY)
    (q : AdmissibleRestrictedCurrentPresentation omegaZ alphaZ
      (Wt.withDim W.dim hdim) epsZ)
    (hpoles : ∀ z ∈ (g ⁻¹' C)ᶜ, z ∉ poleSet q.potential → g z ∉ poleSet p.potential)
    (hdens : ∀ (P : RegularPatch W) (Q : RegularPatch (Wt.withDim W.dim hdim))
      (v v' : ComplexModel W.dim), v ∈ P.parameterDomain → v' ∈ Q.parameterDomain →
      Q.toManifold v' ∉ g ⁻¹' C → g (Q.toManifold v') = P.toManifold v →
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
      patchDensity q Q v' ≤ patchDensity p P v) :
    acTopMass q ≤ acTopMass p := by
  have hCa : IsComplexAnalyticSubset (n := n) C :=
    AnalyticSubsetPreimage.isComplexAnalyticSubset_of_isClosedSubmanifold hg.1
  have hAa : IsComplexAnalyticSubset (n := n) (g ⁻¹' C) :=
    AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage hg.contMDiff hCa
  have hAexc : exceptionalLocus n g ⊆ g ⁻¹' C :=
    BlowupIsomorphismOff.exceptionalLocus_subset_preimage hg
  have hAinj : InjOn g (g ⁻¹' C)ᶜ := by
    rw [← preimage_compl]
    exact (BlowupIsomorphismOff.isIsomorphismOver_compl_of_isBlowupAlong hg).1.2.1
  have hWtA : ¬ (Wt.withDim W.dim hdim).carrier ⊆ g ⁻¹' C := by
    rw [ClosedIrreducibleAnalyticSubvariety.withDim_carrier, hWt]
    exact StrictTransformLocus.not_strictTransform_subset_preimage hg W hW hCa hWC
  have hWO : ∀ x ∈ (g ⁻¹' C)ᶜ, x ∈ (Wt.withDim W.dim hdim).carrier ↔ g x ∈ W.carrier := by
    intro x hx
    rw [ClosedIrreducibleAnalyticSubvariety.withDim_carrier, hWt]
    exact RestrictedVolumePullbackLower.mem_strictTransform_iff hg.contMDiff.continuous
      W.isClosed_carrier (fun h => hx (hAexc h))
  exact acTopMass_le_of_patchDensity_le hg.contMDiff hdim hAa hAexc hAinj hWtA hWO p q hpoles hdens

end

end SGPT.Foundations.Analysis.Pending.RestrictedVolumePushforwardMass
