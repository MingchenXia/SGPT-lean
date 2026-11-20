import SGPT.Foundations.Analysis.Pending.StrictTransformLocus
import SGPT.Foundations.Analysis.Pending.AdmissiblePresentationPullback
import SGPT.Foundations.Analysis.Pending.RegularPatchPullback
import SGPT.Foundations.Analysis.Pending.PatchParameterNull
import SGPT.Foundations.Analysis.Pending.RestrictedVolumePositivity
import SGPT.Foundations.Analysis.Pending.KahlerDomination
import SGPT.Foundations.Analysis.Pending.BlowupCompact
import SGPT.Foundations.Analysis.Pending.ExceptionalImageAnalytic

set_option autoImplicit false

/-!
# Restricted volumes do not decrease under pullback to the strict transform

Source: CT22, Lemma 4.3 (first inequality), analogous to ELMNP, Lemma 2.4; blueprint
`ana:rv-birational-blowup`.

Let `g : Z → Y` be the blowup of a compact Kähler manifold along a smooth centre, `α = {θ}`
big, and `W ⊄ g(Exc g)` with strict transform `W̃`.  Then `⟨α^k⟩_{Y|W} ≤ ⟨(g^*α)^k⟩_{Z|W̃}`.

* If `W ⊆ E_nn(α)` the left side is `0`.  Otherwise `W̃ ⊄ E_nn(g^*α)`
  (`StrictTransformLocus`), and both sides are infima of admissible mass envelopes.
* Pick `c > 0` with `-g^*ω + cω_Z ≥ 0`.  An `ε`-admissible presentation `T` along `W`
  pulls back to a `cε`-admissible presentation `g^*T` along `W̃`
  (`AdmissiblePresentationPullback`; `W̃ ⊄ g⁻¹ P(T)` by `StrictTransformLocus`).
* `acTopMass T ≤ acTopMass (g^*T)`.  Take a regular piece family for `W`.  Remove from each
  piece the parameters over `g(Exc g)`, a null set (`PatchParameterNull`).  Every other
  parameter `w₀` lies over a unique non-exceptional `z`, and a regular patch `Q` of `W̃`
  at `z` transports a ball around `w₀` (`RegularPatchPullback`).  Countably many such
  balls cover the piece; disjointify them.  Each finite stage gives a regular piece family
  for `W̃` avoiding `g⁻¹ P(T)`, with pairwise disjoint images because `g` is injective off
  `Exc g` and patch parametrizations are injective.  By translation invariance of Lebesgue
  measure and `(g^*T + cεω_Z)|_{Q} = (T + εω)|_{P} + ε(-g^*ω + cω_Z)|_{Q}`, whose top
  power dominates, each stage bounds the corresponding part of the mass of `T`; monotone
  convergence finishes.
* Hence `env_Y(ε) ≤ env_Z(cε)` for all `ε`, and the infima compare.
-/

open Set Filter MeasureTheory
open scoped Topology Manifold ContDiff ENNReal

universe u

namespace SGPT.Foundations.Analysis.Pending.RestrictedVolumePullbackLower

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus FirstPass.BlowupSequences
  FirstPass.NumericalRestrictedVolumeScaffold FirstPass.NumericalRestrictedVolume
  AdmissiblePresentationPullback

noncomputable section

variable {n : ℕ}
  {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
  {Z : Type u} [TopologicalSpace Z] [ChartedSpace (ComplexModel n) Z] [IsComplexManifold n Z]

omit [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
  [TopologicalSpace Z] [ChartedSpace (ComplexModel n) Z] [IsComplexManifold n Z] in
theorem add_comp {k m : ℕ} (A B : MongeAmpere.CoordinateRealTwoForm m)
    (L : ComplexModel k →L[ℝ] ComplexModel m) :
    (A + B).compContinuousLinearMap L = A.compContinuousLinearMap L + B.compContinuousLinearMap L := by
  ext v
  simp

omit [IsComplexManifold n Y] [IsComplexManifold n Z] in
/-- Off the exceptional locus, the strict transform is the preimage. -/
theorem mem_strictTransform_iff {g : Z → Y} (hgc : Continuous g) {A : Set Y} (hA : IsClosed A)
    {x : Z} (hx : x ∉ exceptionalLocus n g) :
    x ∈ strictTransform n g A ↔ g x ∈ A := by
  constructor
  · intro h
    exact (closure_minimal sdiff_subset (hA.preimage hgc)) h
  · intro h
    exact subset_closure ⟨h, hx⟩

/-- Every closed irreducible subvariety has a regular patch. -/
theorem nonempty_regularPatch (V : ClosedIrreducibleAnalyticSubvariety n Y) :
    Nonempty (RegularPatch V) := by
  obtain ⟨x, -, hx, Φ, h1, h2, h3⟩ := V.regularLocus_nonempty
  exact ⟨⟨x, hx, Φ, h1, h2, h3⟩⟩

/-- Patch parametrizations are injective on the parameter domain. -/
theorem toManifold_injOn {V : ClosedIrreducibleAnalyticSubvariety n Y} (P : RegularPatch V) :
    InjOn P.toManifold P.parameterDomain := by
  intro a ha b hb hab
  have hsa := P.source_subset (P.flattening.mapsTo_invFun ha)
  have hsb := P.source_subset (P.flattening.mapsTo_invFun hb)
  have h1 : P.coordinateParametrization a = P.coordinateParametrization b := by
    rw [← RegularPatchNeighborhood.RegularPatch.chart_toManifold P ha,
      ← RegularPatchNeighborhood.RegularPatch.chart_toManifold P hb, hab]
  have h2 : planeInclusion V.dim n a = planeInclusion V.dim n b := by
    have := congrArg P.flattening.toFun h1
    simpa only [RegularPatch.coordinateParametrization, P.flattening.right_inv _ ha,
      P.flattening.right_inv _ hb] using this
  exact AdmissibleCurrentFormPositivity.planeInclusion_injective V.dim_le h2

/-- **Pointwise density comparison.**  If restrictions along `Q` of pulled-back forms and
`ddᶜ` of composed smooth functions agree with the restrictions along `P`, the top-power
density of the pulled-back presentation along `Q` dominates that of `T` along `P`. -/
theorem patchDensity_le_pullback [CompactSpace Y] {C : Set Y} {g : Z → Y}
    (hg : IsBlowupAlong n C g) {omega : KahlerBackground n Y} {omegaZ : KahlerBackground n Z}
    {θ : ClosedRealOneOneForm n Y} {W : ClosedIrreducibleAnalyticSubvariety n Y}
    {Wt : ClosedIrreducibleAnalyticSubvariety n Z} (hdim : Wt.dim = W.dim)
    {ε : PositiveError} {c : ℝ} (hc : 0 < c)
    (hD : (-(ClosedRealOneOneForm.pullback hg.contMDiff omega.form) +
      c • omegaZ.form).val.IsSemipositive)
    (p : AdmissibleRestrictedCurrentPresentation omega (RealBottChern.ofRepresentative θ) W ε)
    (hpole : ¬ (Wt.withDim W.dim hdim).carrier ⊆ g ⁻¹' poleSet p.potential)
    (P : RegularPatch W) (Q : RegularPatch (Wt.withDim W.dim hdim))
    {w w' : ComplexModel W.dim} (hw : w ∈ P.parameterDomain) (hw' : w' ∈ Q.parameterDomain)
    (hnp : P.toManifold w ∉ poleSet p.potential)
    (hβ : ∀ β : ClosedRealOneOneForm n Y,
      ((ClosedRealOneOneForm.pullback hg.contMDiff β).val.coeff
          (complexChartAt (n := n) Q.center)
          (Q.coordinateParametrization w')).compContinuousLinearMap
        (fderiv ℝ Q.coordinateParametrization w') =
      (β.val.coeff (complexChartAt (n := n) P.center)
          (P.coordinateParametrization w)).compContinuousLinearMap
        (fderiv ℝ P.coordinateParametrization w))
    (hv : ∀ v : Y → ℝ,
      (∀ᶠ y in 𝓝 (P.coordinateParametrization w),
        ContDiffAt ℝ ∞ (fun y => v ((complexChartAt (n := n) P.center).val.symm y)) y) →
      (smoothDDC (fun y => v (g ((complexChartAt (n := n) Q.center).val.symm y)))
          (Q.coordinateParametrization w')).compContinuousLinearMap
        (fderiv ℝ Q.coordinateParametrization w') =
      (smoothDDC (fun y => v ((complexChartAt (n := n) P.center).val.symm y))
          (P.coordinateParametrization w)).compContinuousLinearMap
        (fderiv ℝ P.coordinateParametrization w)) :
    patchDensity p P w ≤ patchDensity (pullbackPresentation hg hc hD p _ hpole) Q w' := by
  have hzP : P.coordinateParametrization w ∈ (complexChartAt (n := n) P.center).val.target :=
    P.source_subset (P.flattening.mapsTo_invFun hw)
  have hzQ : Q.coordinateParametrization w' ∈ (complexChartAt (n := n) Q.center).val.target :=
    Q.source_subset (Q.flattening.mapsTo_invFun hw')
  obtain ⟨g₀, hg₀, heq⟩ :=
    AdmissibleCurrentFormPositivity.exists_smooth_eventuallyEq_of_hasAnalyticSingularitiesSmoothOffPoleAt
      (p.smoothAnalyticSingularities (complexChartAt (n := n) P.center) _ hzP) hnp
  have hsmooth : ∀ᶠ y in 𝓝 (P.coordinateParametrization w),
      ContDiffAt ℝ ∞
        (fun y => (p.potential ((complexChartAt (n := n) P.center).val.symm y)).toReal) y := by
    filter_upwards [hg₀, heq.eventually_nhds] with y hy hy'
    refine hy.congr_of_eventuallyEq ?_
    filter_upwards [hy'] with x hx
    change (chartFunction p.potential (complexChartAt (n := n) P.center) x).toReal = g₀ x
    rw [hx, EReal.toReal_coe]
  have key1 := hβ (perturbedRepresentative p)
  have key2 := hv (fun y => (p.potential y).toReal) hsmooth
  obtain ⟨hA1, hA2⟩ :=
    AdmissibleCurrentFormPositivity.coordinateCurrentForm_isOneOne_and_semipositive
      p (complexChartAt (n := n) P.center) hzP hnp
  have hLP := AdmissibleCurrentFormPositivity.RegularPatchDerivative.fderiv_coordinateParametrization_I_smul P hw
  have hLQ := AdmissibleCurrentFormPositivity.RegularPatchDerivative.fderiv_coordinateParametrization_I_smul Q hw'
  have hB1 : IsOneOne ((ε : ℝ) • (-(ClosedRealOneOneForm.pullback hg.contMDiff omega.form) +
      c • omegaZ.form).val.coeff (complexChartAt (n := n) Q.center)
        (Q.coordinateParametrization w')) := by
    intro a b
    simp only [ContinuousAlternatingMap.smul_apply,
      (-(ClosedRealOneOneForm.pullback hg.contMDiff omega.form) + c • omegaZ.form).2.2 _ _ hzQ a b]
  have hB2 : CoefficientSemipositive ((ε : ℝ) •
      (-(ClosedRealOneOneForm.pullback hg.contMDiff omega.form) +
        c • omegaZ.form).val.coeff (complexChartAt (n := n) Q.center)
          (Q.coordinateParametrization w')) := by
    intro v
    simp only [ContinuousAlternatingMap.smul_apply, smul_eq_mul]
    exact mul_nonneg ε.2.le (hD _ _ hzQ v)
  have key := MongeAmpere.actualTopPowerDensity_le_add
    (RestrictedMassEnvelopeMonotone.isOneOne_compContinuousLinearMap hA1 _ hLP)
    (RestrictedMassEnvelopeMonotone.coefficientSemipositive_compContinuousLinearMap hA2 _ hLP)
    (RestrictedMassEnvelopeMonotone.isOneOne_compContinuousLinearMap hB1 _ hLQ)
    (RestrictedMassEnvelopeMonotone.coefficientSemipositive_compContinuousLinearMap hB2 _ hLQ)
  refine key.trans_eq (congrArg MongeAmpere.actualTopPowerDensity ?_)
  rw [coordinateCurrentForm_pullbackPresentation hg hc hD p _ hpole _ hzQ, add_comp, add_comp,
    key1, key2, coordinateCurrentForm, add_comp]
  rfl

/-- The restricted mass does not decrease under pullback of the presentation. -/
theorem acTopMass_le_pullbackPresentation [CompactSpace Y] {C : Set Y} {g : Z → Y}
    (hg : IsBlowupAlong n C g) {omega : KahlerBackground n Y} {omegaZ : KahlerBackground n Z}
    {θ : ClosedRealOneOneForm n Y} (W : ClosedIrreducibleAnalyticSubvariety n Y)
    (hW : ¬ W.carrier ⊆ g '' exceptionalLocus n g)
    (Wt : ClosedIrreducibleAnalyticSubvariety n Z)
    (hWt : Wt.carrier = strictTransform n g W.carrier) (hdim : Wt.dim = W.dim)
    {ε : PositiveError} {c : ℝ} (hc : 0 < c)
    (hD : (-(ClosedRealOneOneForm.pullback hg.contMDiff omega.form) +
      c • omegaZ.form).val.IsSemipositive)
    (p : AdmissibleRestrictedCurrentPresentation omega (RealBottChern.ofRepresentative θ) W ε)
    (hpole : ¬ (Wt.withDim W.dim hdim).carrier ⊆ g ⁻¹' poleSet p.potential) :
    acTopMass p ≤ acTopMass (pullbackPresentation hg hc hD p (Wt.withDim W.dim hdim) hpole) := by
  classical
  set Wt' := Wt.withDim W.dim hdim with hWt'
  set q := pullbackPresentation hg hc hD p Wt' hpole with hq
  set E : Set Y := g '' exceptionalLocus n g with hEdef
  have hEa : IsComplexAnalyticSubset (n := n) E :=
    ExceptionalImageAnalytic.isComplexAnalyticSubset_image_exceptionalLocus hg
  have hEc : IsClosed E := ExceptionalFibres.isClosed_image_exceptionalLocus hg
  have hWE : ∀ U : Set Y, IsOpen U → (W.carrier ∩ U).Nonempty → ¬ W.carrier ∩ U ⊆ E :=
    fun U hU hne hsub => hW (StrictTransformLocus.subset_of_inter_isOpen_subset W hEa hU hne hsub)
  have hO : IsOpen (exceptionalLocus n g)ᶜ :=
    StrictTransformComposition.isOpen_compl_exceptionalLocus hg.contMDiff
  have hWO : ∀ x ∈ (exceptionalLocus n g)ᶜ, x ∈ Wt'.carrier ↔ g x ∈ W.carrier := fun x hx => by
    rw [hWt', ClosedIrreducibleAnalyticSubvariety.withDim_carrier, hWt]
    exact mem_strictTransform_iff hg.contMDiff.continuous W.isClosed_carrier hx
  have hsurj := StrictTransformComposition.surjective_of_isBlowupAlong hg
  -- local transport data at every good parameter
  have hloc : ∀ (P : RegularPatch W) (w₀ : ComplexModel W.dim), w₀ ∈ P.parameterDomain →
      P.toManifold w₀ ∉ E → ∃ (Q : RegularPatch Wt') (r : ℝ), 0 < r ∧
        ∀ w ∈ Metric.ball w₀ r, w - w₀ ∈ Q.parameterDomain ∧
          g (Q.toManifold (w - w₀)) = P.toManifold w ∧
          (P.toManifold w ∉ poleSet p.potential →
            patchDensity p P w ≤ patchDensity q Q (w - w₀)) := by
    intro P w₀ hw₀ hE
    obtain ⟨z, hz⟩ := hsurj (P.toManifold w₀)
    have hzE : z ∉ exceptionalLocus n g := fun h => hE ⟨z, h, hz⟩
    obtain ⟨Q, r, hr, hQ⟩ := RegularPatchPullback.exists_regularPatch_pullback hg.contMDiff hdim
      hO hWO P hw₀ hzE hzE hz
    refine ⟨Q, r, hr, fun w hw => ?_⟩
    obtain ⟨hwP, hwQ, -, -, hgQ, hβ, hv⟩ := hQ w hw
    exact ⟨hwQ, hgQ, fun hnp => patchDensity_le_pullback hg hdim hc hD p hpole P Q hwP hwQ hnp
      hβ hv⟩
  obtain ⟨x₀, -, hx₀, Φ₀, h₁, h₂, h₃⟩ := Wt'.regularLocus_nonempty
  have : Nonempty (RegularPatch Wt') := ⟨⟨x₀, hx₀, Φ₀, h₁, h₂, h₃⟩⟩
  choose! Q r hr hQ using hloc
  refine iSup_le fun F => ?_
  -- good parts of the pieces and their countable ball covers
  set P : Fin F.size → RegularPatch W := F.patch with hPdef
  set G : Fin F.size → Set (ComplexModel W.dim) := fun i =>
    F.piece i ∩ ((P i).parameterDomain ∩ (P i).toManifold ⁻¹' Eᶜ) with hGdef
  set R : Fin F.size → ComplexModel W.dim → ℝ := fun i w₀ => if w₀ ∈ G i then r (P i) w₀ else 0
    with hRdef
  have hGmeas : ∀ i, MeasurableSet (G i) := fun i =>
    (F.measurableSet_piece i).inter
      ((RegularPatchNeighborhood.RegularPatch.continuousOn_toManifold (P i)).isOpen_inter_preimage
        (AdmissibleCurrentFormPositivity.RegularPatchDerivative.isOpen_parameterDomain (P i))
        hEc.isOpen_compl).measurableSet
  have hcover : ∀ i, ∃ c : ℕ → ComplexModel W.dim, G i ⊆ ⋃ j, Metric.ball (c j) (R i (c j)) := by
    intro i
    obtain ⟨T, hTc, hT⟩ := TopologicalSpace.isOpen_iUnion_countable
      (fun w₀ => Metric.ball w₀ (R i w₀)) (fun _ => Metric.isOpen_ball)
    obtain ⟨c, hc⟩ := (hTc.insert 0).exists_eq_range (insert_nonempty _ _)
    refine ⟨c, fun w hw => ?_⟩
    have hmem : w ∈ ⋃ w₀, Metric.ball w₀ (R i w₀) := by
      refine mem_iUnion.mpr ⟨w, Metric.mem_ball_self ?_⟩
      simp only [hRdef, if_pos hw]
      exact hr (P i) w (F.piece_subset i hw.1) hw.2.2
    rw [← hT] at hmem
    obtain ⟨w₀, hw₀T, hw⟩ := mem_iUnion₂.mp hmem
    have : w₀ ∈ range c := hc ▸ mem_insert_of_mem _ hw₀T
    obtain ⟨j, rfl⟩ := this
    exact mem_iUnion.mpr ⟨j, hw⟩
  choose c hc using hcover
  set D : Fin F.size → ℕ → Set (ComplexModel W.dim) := fun i j =>
    G i ∩ disjointed (fun j => Metric.ball (c i j) (R i (c i j))) j with hDdef
  have hDmeas : ∀ i j, MeasurableSet (D i j) := fun i j =>
    (hGmeas i).inter (MeasurableSet.disjointed (fun _ => Metric.isOpen_ball.measurableSet) j)
  have hDdisj : ∀ i, Pairwise (Function.onFun Disjoint (D i)) := fun i j j' hjj' =>
    ((disjoint_disjointed _ hjj').mono inter_subset_right inter_subset_right)
  have hDgood : ∀ i j, ∀ w ∈ D i j, c i j ∈ G i ∧ w ∈ G i ∧
      w ∈ Metric.ball (c i j) (r (P i) (c i j)) := by
    intro i j w hw
    have hwb : w ∈ Metric.ball (c i j) (R i (c i j)) :=
      disjointed_le (fun j => Metric.ball (c i j) (R i (c i j))) j hw.2
    by_cases hcG : c i j ∈ G i
    · refine ⟨hcG, hw.1, ?_⟩
      simpa only [hRdef, if_pos hcG] using hwb
    · simp only [hRdef, if_neg hcG, Metric.ball_zero, mem_empty_iff_false] at hwb
  set f : Fin F.size → ComplexModel W.dim → ℝ≥0∞ := fun i w =>
    ENNReal.ofReal (patchDensity p (P i) w) with hfdef
  set a : Fin F.size → ℕ → ℝ≥0∞ := fun i j => ∫⁻ w in D i j, f i w with hadef
  -- the mass of each piece is the sum over the disjointified cover
  have hpiece : ∀ i, ∫⁻ w in F.piece i, f i w ≤ ⨆ N, ∑ j ∈ Finset.range N, a i j := by
    intro i
    have hnull : volume ((P i).parameterDomain ∩ (P i).toManifold ⁻¹' E) = 0 :=
      PatchParameterNull.volume_parameterDomain_inter_preimage_eq_zero (P i) hEa hWE
    have hsub : F.piece i ⊆ (⋃ j, D i j) ∪ ((P i).parameterDomain ∩ (P i).toManifold ⁻¹' E) := by
      intro w hw
      by_cases hwE : (P i).toManifold w ∈ E
      · exact Or.inr ⟨F.piece_subset i hw, hwE⟩
      · have hwG : w ∈ G i := ⟨hw, F.piece_subset i hw, hwE⟩
        refine Or.inl ?_
        have : w ∈ ⋃ j, disjointed (fun j => Metric.ball (c i j) (R i (c i j))) j := by
          rw [iUnion_disjointed]
          exact hc i hwG
        obtain ⟨j, hj⟩ := mem_iUnion.mp this
        exact mem_iUnion.mpr ⟨j, hwG, hj⟩
    calc ∫⁻ w in F.piece i, f i w
        ≤ ∫⁻ w in (⋃ j, D i j) ∪ ((P i).parameterDomain ∩ (P i).toManifold ⁻¹' E), f i w :=
          lintegral_mono_set hsub
      _ ≤ (∫⁻ w in ⋃ j, D i j, f i w) +
            ∫⁻ w in (P i).parameterDomain ∩ (P i).toManifold ⁻¹' E, f i w :=
          lintegral_union_le _ _ _
      _ = ∑' j, a i j := by
          rw [setLIntegral_measure_zero _ _ hnull, add_zero, lintegral_iUnion (hDmeas i) (hDdisj i)]
      _ = ⨆ N, ∑ j ∈ Finset.range N, a i j := ENNReal.tsum_eq_iSup_nat
  refine (Finset.sum_le_sum fun i _ => hpiece i).trans ?_
  rw [ENNReal.finsetSum_iSup_of_monotone fun i N N' hNN' =>
    Finset.sum_le_sum_of_subset (Finset.range_mono hNN')]
  refine iSup_le fun N => ?_
  -- the stage-`N` family on the strict transform
  set e : Fin F.size × Fin N ≃ Fin (F.size * N) := finProdFinEquiv with he
  have hmapsQ : ∀ i (j : ℕ), ∀ w ∈ D i j, w - c i j ∈ (Q (P i) (c i j)).parameterDomain ∧
      g ((Q (P i) (c i j)).toManifold (w - c i j)) = (P i).toManifold w ∧
      patchDensity p (P i) w ≤ patchDensity q (Q (P i) (c i j)) (w - c i j) := by
    intro i j w hw
    obtain ⟨hcG, hwG, hwb⟩ := hDgood i j w hw
    obtain ⟨h1, h2, h3⟩ := hQ (P i) (c i j) (F.piece_subset i hcG.1) hcG.2.2 w hwb
    refine ⟨h1, h2, h3 fun hpw => ?_⟩
    exact disjoint_left.mp (F.image_disjoint_avoid i) ⟨w, hwG.1, rfl⟩ hpw
  have hmapsQ' : ∀ i (j : ℕ) (w' : ComplexModel W.dim), w' + c i j ∈ D i j →
      w' ∈ (Q (P i) (c i j)).parameterDomain ∧
      g ((Q (P i) (c i j)).toManifold w') = (P i).toManifold (w' + c i j) := by
    intro i j w' hw'
    have h := hmapsQ i j _ hw'
    rw [add_sub_cancel_right] at h
    exact ⟨h.1, h.2.1⟩
  let Fz : RegularPieceFamily Wt' (poleSet q.potential) :=
    { size := F.size * N
      patch := fun k => Q (P (e.symm k).1) (c (e.symm k).1 (e.symm k).2)
      piece := fun k => (fun w' : ComplexModel W.dim => w' + c (e.symm k).1 (e.symm k).2) ⁻¹'
        D (e.symm k).1 (e.symm k).2
      measurableSet_piece := fun k => (hDmeas _ _).preimage
        ((continuous_add_const (c (e.symm k).1 (e.symm k).2)).measurable :
          Measurable fun w' : ComplexModel W.dim => w' + c (e.symm k).1 (e.symm k).2)
      piece_subset := fun k w' hw' => (hmapsQ' _ _ w' hw').1
      image_subset_regularLocus := fun k => by
        rintro _ ⟨w', hw', rfl⟩
        exact RegularPatchNeighborhood.RegularPatch.toManifold_mem_regularLocus _
          (hmapsQ' _ _ w' hw').1
      image_disjoint_avoid := fun k => by
        refine disjoint_left.mpr ?_
        rintro _ ⟨w', hw', rfl⟩ hpole'
        have h := (hmapsQ' _ _ w' hw').2
        change p.potential (g _) = ⊥ at hpole'
        rw [h] at hpole'
        obtain ⟨-, hwG, -⟩ := hDgood _ _ _ hw'
        exact disjoint_left.mp (F.image_disjoint_avoid _) ⟨_, hwG.1, rfl⟩ hpole'
      pairwise_disjoint_image := fun k k' hkk' => by
        obtain ⟨⟨i, j⟩, rfl⟩ := e.surjective k
        obtain ⟨⟨i', j'⟩, rfl⟩ := e.surjective k'
        have hne : (i, j) ≠ (i', j') := fun h => hkk' (congrArg e h)
        simp only [Equiv.symm_apply_apply]
        refine disjoint_left.mpr ?_
        rintro _ ⟨(w₁ : ComplexModel W.dim), hw₁, rfl⟩ ⟨(w₂ : ComplexModel W.dim), hw₂, heq⟩
        have hw₁' : w₁ + c i j ∈ D i j := hw₁
        have hw₂' : w₂ + c i' j' ∈ D i' j' := hw₂
        have g₁ := (hmapsQ' i j w₁ hw₁').2
        have g₂ := (hmapsQ' i' j' w₂ hw₂').2
        have hgeq := congrArg g heq
        rw [g₁, g₂] at hgeq
        obtain ⟨-, hG₁, -⟩ := hDgood i j _ hw₁'
        obtain ⟨-, hG₂, -⟩ := hDgood i' j' _ hw₂'
        by_cases hi : i' = i
        · subst hi
          have hjj : (j : ℕ) ≠ j' := fun h => hne (Prod.ext rfl (Fin.ext h))
          have hw := toManifold_injOn (P i') hG₂.2.1 hG₁.2.1 hgeq
          have h₂ : w₁ + c i' j ∈ D i' j' := by rw [← hw]; exact hw₂'
          exact disjoint_left.mp (hDdisj i' hjj) hw₁' h₂
        · exact disjoint_left.mp (F.pairwise_disjoint_image hi) ⟨_, hG₂.1, hgeq⟩ ⟨_, hG₁.1, rfl⟩ }
  refine le_trans ?_ (le_iSup _ Fz)
  calc ∑ i, ∑ j ∈ Finset.range N, a i j
      = ∑ x : Fin F.size × Fin N, a x.1 x.2 := by
        rw [Fintype.sum_prod_type]
        exact Finset.sum_congr rfl fun i _ => (Fin.sum_univ_eq_sum_range (a i) N).symm
    _ = ∑ k : Fin (F.size * N), a (e.symm k).1 (e.symm k).2 :=
        (e.symm.sum_comp fun x => a x.1 x.2).symm
    _ ≤ ∑ k : Fin (F.size * N), ∫⁻ w' in Fz.piece k,
          ENNReal.ofReal (patchDensity q (Fz.patch k) w') := by
        refine Finset.sum_le_sum fun k _ => ?_
        set i := (e.symm k).1
        set j : ℕ := ((e.symm k).2 : ℕ)
        have htr := (measurePreserving_add_right (volume : Measure (ComplexModel W.dim))
          (c i j)).setLIntegral_comp_preimage_emb
          (Homeomorph.addRight (c i j)).measurableEmbedding
          (fun w => ENNReal.ofReal (patchDensity q (Q (P i) (c i j)) (w - c i j))) (D i j)
        simp only [add_sub_cancel_right] at htr
        change ∫⁻ w in D i j, f i w ≤ ∫⁻ w' in (fun w' => w' + c i j) ⁻¹' D i j,
          ENNReal.ofReal (patchDensity q (Q (P i) (c i j)) w')
        rw [htr]
        refine lintegral_mono_ae ((ae_restrict_iff' (hDmeas i j)).mpr (Eventually.of_forall ?_))
        intro w hw
        exact ENNReal.ofReal_le_ofReal (hmapsQ i j w hw).2.2

/-- **CT22, Lemma 4.3, first inequality, one blowup.** -/
theorem numericalRestrictedVolume_le_pullback [CompactSpace Y]
    (θ : ClosedRealOneOneForm n Y) (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    {C : Set Y} {g : Z → Y} (hg : IsBlowupAlong n C g)
    (W : ClosedIrreducibleAnalyticSubvariety n Y) (hdim_pos : 0 < W.dim)
    (hW : ¬ W.carrier ⊆ g '' exceptionalLocus n g)
    (Wt : ClosedIrreducibleAnalyticSubvariety n Z)
    (hWt : Wt.carrier = strictTransform n g W.carrier) (hdim : Wt.dim = W.dim)
    (omega : KahlerBackground n Y) (omegaZ : KahlerBackground n Z) :
    numericalRestrictedVolume omega (RealBottChern.ofRepresentative θ) W ≤
      numericalRestrictedVolume omegaZ (RealBottChern.ofRepresentative
        (ClosedRealOneOneForm.pullback hg.contMDiff θ)) Wt := by
  have hn : 0 < n := hdim_pos.trans_le W.dim_le
  have := BlowupCompact.compactSpace_of_isBlowupAlong hg
  rw [← Wt.withDim_eq W.dim hdim]
  by_cases hV : W.carrier ⊆ nonNefLocus omega (RealBottChern.ofRepresentative θ)
  · rw [numericalRestrictedVolume_eq_zero_of_subset_nonNefLocus _ _ _ hV]
    exact zero_le
  have hV' : ¬ (Wt.withDim W.dim hdim).carrier ⊆ nonNefLocus omegaZ
      (RealBottChern.ofRepresentative (ClosedRealOneOneForm.pullback hg.contMDiff θ)) := by
    rw [ClosedIrreducibleAnalyticSubvariety.withDim_carrier, hWt]
    exact StrictTransformLocus.not_strictTransform_subset_nonNefLocus hn omega omegaZ θ hbig hg
      W hW hV
  obtain ⟨c, hc, hD⟩ := KahlerDomination.exists_pos_isSemipositive_add_smul omegaZ
    (-(ClosedRealOneOneForm.pullback hg.contMDiff omega.form))
  rw [RestrictedVolumePositivity.numericalRestrictedVolume_eq_iInf omega _ W hV,
    RestrictedVolumePositivity.numericalRestrictedVolume_eq_iInf omegaZ _ _ hV']
  refine le_iInf fun ε' => ?_
  set ε : PositiveError := ⟨c⁻¹ * ε', mul_pos (inv_pos.mpr hc) ε'.2⟩ with hε
  refine (iInf_le _ ε).trans ?_
  refine iSup_le fun p => ?_
  have hpole : ¬ (Wt.withDim W.dim hdim).carrier ⊆ g ⁻¹' poleSet p.potential := by
    rw [ClosedIrreducibleAnalyticSubvariety.withDim_carrier, hWt]
    exact StrictTransformLocus.not_strictTransform_subset_preimage hg W hW
      (StrictTransformLocus.isComplexAnalyticSubset_poleSet_of_smoothOffPole
        p.smoothAnalyticSingularities)
      p.not_carrier_subset_poleSet
  have heq : (⟨c * ε, mul_pos hc ε.2⟩ : PositiveError) = ε' := by
    apply Subtype.ext
    simp only [hε]
    field_simp
  refine (acTopMass_le_pullbackPresentation hg W hW Wt hWt hdim hc hD p hpole).trans ?_
  rw [← heq]
  exact le_iSup (fun q : AdmissibleRestrictedCurrentPresentation omegaZ _ _ _ =>
    (acTopMassData omegaZ).topMass q) (pullbackPresentation hg hc hD p _ hpole)

end

end SGPT.Foundations.Analysis.Pending.RestrictedVolumePullbackLower
