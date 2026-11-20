import SGPT.BDivisor.BD7QEAEffectiveDifference
import SGPT.BDivisor.DFAlgComparison

/-! The checked dyadic approximation has decreasing differences witnessed by prime sums. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.BDivisor.BD7

open Set Filter
open scoped Topology ENNReal BigOperators Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses
  SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
  SGPT.Foundations.Analysis.FirstPass.GlobalAnalyticSingularities
  SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
  SGPT.Foundations.Analysis.FirstPass.IEnvelope
  SGPT.Foundations.Analysis.Pending NaturalThetaPshGeometricCurrent
  CurrentBottChernClass CanonicalCurrentFrame
  SGPT.BDivisor.DFAlg
  SGPT.Hodge.BDivChain SGPT.Hodge.BDivChain.NativeDraft
  SGPT.Hodge.BDivChain.NativeDraft.VolumeNetDraft
  SGPT.Hodge.BDivChain.SourceMixedOrderDraft
  SGPT.Hodge.BDivChain.SourceCartierSequenceDraft
  SGPT.Hodge.BDivChain.NativeDraft.GlobalDistributionTwo
  SGPT.Hodge.BDivChain.SourceNefProjectiveDraft
  SGPT.PSH.VariableComplexAtlas
  SGPT.Hodge.BDivChain.SourceCorrespondenceDraft
  SGPT.Hodge.BDivChain.SourceAugmentedDraft

attribute [local instance] blowup_model_connectedSpace

variable {m : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel (m + 1)) X]
  [IsComplexManifold (m + 1) X] [CompactSpace X] [ConnectedSpace X]
  [MeasurableSpace X] [BorelSpace X]

local notation "Sys" => ModelSystem.blowup (m + 1) X

def effectiveClosure {Y : Type} [TopologicalSpace Y]
    [ChartedSpace (ComplexModel (m + 1)) Y] [IsComplexManifold (m + 1) Y] [CompactSpace Y] :
    Set (RealBottChern (m + 1) Y) :=
  @closure _ (euclideanTopology _)
    (finiteEffectiveCone fun P : SGPT.PSH.GeometricPrimeCarrier (m + 1) Y =>
      cycleClass (SGPT.Siu.primeEffectiveDivisor P))

private theorem represented_difference_mem_effectiveClosure (π : (ModelSystem.blowup (m + 1) X).Model)
    (κ : KahlerBackground (m + 1) π.1.carrier)
    (θ : ClosedRealOneOneForm (m + 1) X) {u v : X → EReal}
    (hu : IsThetaPshPotential θ.val u) (hv : IsThetaPshPotential θ.val v)
    (hI : IOrderOnManifold (n := m + 1) u v) :
    (currentBDivisorAnyOn Sys (representedCurrent θ v hv)).val π -
      (currentBDivisorAnyOn Sys (representedCurrent θ u hu)).val π ∈ effectiveClosure := by
  let A := representedCurrent θ u hu
  let B := representedCurrent θ v hv
  have hp := (isPresentationAny_iff_book A θ u).mp (representedCurrent_isPresentation θ u hu)
  have hq := (isPresentationAny_iff_book B θ v).mp (representedCurrent_isPresentation θ v hv)
  let hA := SGPT.Siu.isClosedPositiveCurrent_bookCurrent (toBookCurrent A)
  let hB := SGPT.Siu.isClosedPositiveCurrent_bookCurrent (toBookCurrent B)
  change regPullClassAny π.1 B - regPullClassAny π.1 A ∈ effectiveClosure
  rw [regPullClassAny_eq_existing, regPullClassAny_eq_existing]
  have he : π.1.regPullClass (toBookCurrent B).current hB -
      π.1.regPullClass (toBookCurrent A).current hA =
        π.1.divPullClass (toBookCurrent A).current hA -
          π.1.divPullClass (toBookCurrent B).current hB := by
    rw [π.1.regPullClass_eq hB, π.1.regPullClass_eq hA]
    have hEq : SGPT.PSH.BookCurrent.currentClass (toBookCurrent A) =
        SGPT.PSH.BookCurrent.currentClass (toBookCurrent B) :=
      hp.currentClass_eq.trans hq.currentClass_eq.symm
    change classPullback π.1.contMDiff_map (SGPT.PSH.BookCurrent.currentClass (toBookCurrent B)) -
        π.1.divPullClass (toBookCurrent B).current hB -
      (classPullback π.1.contMDiff_map (SGPT.PSH.BookCurrent.currentClass (toBookCurrent A)) -
        π.1.divPullClass (toBookCurrent A).current hA) = _
    rw [hEq]
    abel
  rw [he]
  exact siuDivisorialClass_sub_mem_effectiveClosure κ
    (Modification4.isClosedPositiveCurrent_pull π.1.isAnalyticModification hA)
    (Modification4.isClosedPositiveCurrent_pull π.1.isAnalyticModification hB)
    (PrimePushforward.currentGenericLelong_pull_le_of_iOrder
      π.1.isAnalyticModification hA hB hu hv hp.2 hq.2 hI)

private theorem finiteEffectiveCone_add {P V : Type*} [AddCommGroup V] [Module ℝ V]
    {p : P → V} {x y : V} (hx : x ∈ finiteEffectiveCone p) (hy : y ∈ finiteEffectiveCone p) :
    x + y ∈ finiteEffectiveCone p := by
  classical
  obtain ⟨S, a, ha, rfl⟩ := hx
  obtain ⟨T, b, hb, rfl⟩ := hy
  let a' := fun i => if i ∈ S then a i else 0
  let b' := fun i => if i ∈ T then b i else 0
  refine ⟨S ∪ T, fun i => a' i + b' i, fun i _ => ?_, ?_⟩
  · apply add_nonneg
    · by_cases h : i ∈ S <;> simp [a', h, ha]
    · by_cases h : i ∈ T <;> simp [b', h, hb]
  have hS : (∑ i ∈ S ∪ T, a' i • p i) = ∑ i ∈ S, a i • p i := by
    rw [← Finset.sum_subset Finset.subset_union_left (fun i _ hi => by simp [a', hi])]
    exact Finset.sum_congr rfl fun i hi => by simp [a', hi]
  have hT : (∑ i ∈ S ∪ T, b' i • p i) = ∑ i ∈ T, b i • p i := by
    rw [← Finset.sum_subset Finset.subset_union_right (fun i _ hi => by simp [b', hi])]
    exact Finset.sum_congr rfl fun i hi => by simp [b', hi]
  simp_rw [add_smul, Finset.sum_add_distrib, hS, hT]

private theorem finiteEffectiveCone_smul {P V : Type*} [AddCommGroup V] [Module ℝ V]
    {p : P → V} {x : V} (hx : x ∈ finiteEffectiveCone p) {c : ℝ} (hc : 0 ≤ c) :
    c • x ∈ finiteEffectiveCone p := by
  obtain ⟨S, a, ha, rfl⟩ := hx
  refine ⟨S, fun i => c * a i, fun i hi => mul_nonneg hc (ha i hi), ?_⟩
  simp only [Finset.smul_sum, smul_smul]

private theorem closure_finiteEffectiveCone_add_smul {P V : Type*}
    [AddCommGroup V] [Module ℝ V] (p : P → V) {x y : V}
    (hx : x ∈ @closure _ (euclideanTopology V) (finiteEffectiveCone p))
    (hy : y ∈ @closure _ (euclideanTopology V) (finiteEffectiveCone p))
    {c : ℝ} (hc : 0 ≤ c) :
    x + c • y ∈ @closure _ (euclideanTopology V) (finiteEffectiveCone p) := by
  letI := euclideanTopology V
  let f : V × V → V := fun z => z.1 + c • z.2
  have hf : Continuous f := by
    apply continuous_iff_continuousAt.mpr
    intro z
    apply tendsto_euclideanTopology_iff.mpr
    intro φ
    have hl := (continuous_euclideanTopology φ).continuousAt.comp
      (continuous_fst.continuousAt (x := z))
    have hr := (continuous_euclideanTopology φ).continuousAt.comp
      (continuous_snd.continuousAt (x := z))
    simp only [f, map_add, map_smul, smul_eq_mul]
    exact hl.tendsto.add (hr.tendsto.const_mul c)
  have hxy : (x, y) ∈ closure (finiteEffectiveCone p ×ˢ finiteEffectiveCone p) := by
    rw [closure_prod_eq]
    exact ⟨hx, hy⟩
  have hmaps : f '' (finiteEffectiveCone p ×ˢ finiteEffectiveCone p) ⊆ finiteEffectiveCone p := by
    rintro _ ⟨z, hz, rfl⟩
    exact finiteEffectiveCone_add hz.1 (finiteEffectiveCone_smul hz.2 hc)
  exact closure_mono hmaps (image_closure_subset_closure_image hf ⟨(x, y), hxy, rfl⟩)

private theorem metered_curvature_mem_effectiveClosure {Y : Type} [TopologicalSpace Y]
    [ChartedSpace (ComplexModel (m + 1)) Y] [IsComplexManifold (m + 1) Y]
    [CompactSpace Y] [ConnectedSpace Y] (κ : KahlerBackground (m + 1) Y)
    (F : MeteredEffectiveQDivisor (m + 1) Y) :
    RealBottChern.ofRepresentative F.curvature ∈ effectiveClosure := by
  let hψ := SGPT.Okounkov.TranscendentalLifting.isThetaPshPotential_weight F
  let hT := SGPT.Siu.isClosedPositiveCurrent_thetaPotentialCurrent _ _ hψ
  have hs := hasDivisorClassSum_siuDivisorialPart κ hT
  let T := thetaPotentialCurrent F.curvature.val F.weight hψ
  let hDiv := SGPT.Siu.isClosedPositiveCurrent_siuDivisorialPart hT
  let divT : ClosedOneOneCurrent (M := Y) (canonicalBasis (m + 1)) (Nat.succ_pos m) :=
    ⟨SGPT.Siu.siuDivisorialPart T hT, hDiv.1, hDiv.2.1⟩
  have hcurrent : divT.val =
      (ThetaPotentialCurrentBottChernClass.thetaClosedCurrent F.curvature F.weight hψ).val :=
    SGPT.Hodge.BDivChain.siuDivisorialPart_weightCurrent F hψ hT
  have hclass : bottChernClass (canonicalBasis (m + 1)) (Nat.succ_pos m) divT =
      RealBottChern.ofRepresentative F.curvature :=
    (SGPT.Hodge.BDivChain.bottChernClass_congr hcurrent).trans
      (ThetaPotentialCurrentBottChernClass.bottChernClass_thetaClosedCurrent _ _ hψ)
  change HasDivisorClassSum
    (fun P => (SGPT.Siu.currentGenericLelong T hT P).toReal)
    (bottChernClass (canonicalBasis (m + 1)) (Nat.succ_pos m) divT) at hs
  rw [hclass] at hs
  unfold HasDivisorClassSum at hs
  simp_rw [primeDivisorClass_eq_cycleClass] at hs
  letI := euclideanTopology (RealBottChern (m + 1) Y)
  change Tendsto _ (atTop : Filter (Finset (SGPT.PSH.GeometricPrimeCarrier (m + 1) Y))) _ at hs
  apply mem_closure_of_tendsto hs
  exact Eventually.of_forall fun S => ⟨S, _, fun P _ => ENNReal.toReal_nonneg, rfl⟩

private theorem rootMetered_mem_effectiveClosure
    (κ : ∀ π : (ModelSystem.blowup (m + 1) X).Model, KahlerBackground (m + 1) π.1.carrier)
    (F : MeteredEffectiveQDivisor (m + 1) X) (π : (ModelSystem.blowup (m + 1) X).Model) :
    (rootCartierAny (RealBottChern.ofRepresentative F.curvature)).val π ∈ effectiveClosure := by
  let G := MeteredDivisorOperations.pullback π.1.contMDiff_map
    (Modification4.interior_exceptionalLocus_eq_empty π.1.isAnalyticModification) F
  change (rootCartier (RealBottChern.ofRepresentative F.curvature)).onModel π ∈ effectiveClosure
  rw [rootCartier_onModel, classPullback_ofRepresentative]
  exact metered_curvature_mem_effectiveClosure (κ π) G

/-- A metered hyperplane with positive curvature gives the actual dyadic approximants
whose differences on every book model lie in the closure of the effective prime cone. -/
theorem exists_effectively_antitone_algNefCartier_seq_pos (H : MeteredEffectiveQDivisor (m + 1) X)
    {D_H : EffectiveDivisor (m + 1) X} (hmetric : DivisorMetric.IsDivisorMetric D_H H)
    (hH : H.curvature.val.IsKahler)
    (D : WeilFamilyAny (ModelSystem.blowup (m + 1) X)) (hD : IsNefAny D)
    (hDX : sourceRootClass D ∈ neronSeveri (m + 1) X) :
    ∃ F : ℕ → WeilFamilyAny (ModelSystem.blowup (m + 1) X),
      (∀ i, IsAlgNefCartierAny (F i) ∧ 0 < volumeAny (F i)) ∧
      (∀ i j : ℕ, i ≤ j → ∀ π : (ModelSystem.blowup (m + 1) X).Model, (F i).val π - (F j).val π ∈ effectiveClosure) ∧
        ConvergesAny atTop F D := by
  let ωX : KahlerBackground (m + 1) X := ⟨H.curvature, hH⟩
  have hωX : RealBottChern.ofRepresentative ωX.form ∈ neronSeveri (m + 1) X :=
    curvature_mem_neronSeveri hmetric
  have hX : SGPT.Trace.Bertini.IsProjectiveManifold (m + 1) X :=
    NSKodaira.isProjectiveManifold_iff_exists_kahler_mem_neronSeveri.mpr ⟨H.curvature, hH, hωX⟩
  let κ (π : (ModelSystem.blowup (m + 1) X).Model) : KahlerBackground (m + 1) π.1.carrier := Classical.choice (by
    obtain ⟨form, hform, _⟩ :=
      NSKodaira.isProjectiveManifold_iff_exists_kahler_mem_neronSeveri.mp
        (blowup_model_isProjective hX π)
    exact ⟨⟨form, hform⟩⟩)
  obtain ⟨θ, u, hu, hK, hclass, hfamily⟩ := exists_kahler_realization_rows ωX D hD
  have hθNS : ∀ i, RealBottChern.ofRepresentative (θ i) ∈ neronSeveri (m + 1) X := fun i => by
    rw [hclass i]
    exact Submodule.add_mem _ hDX (Submodule.smul_mem _ _ hωX)
  have hI := realization_rows_IEquivalent ωX D θ u hu hclass hfamily
  choose U threshold hQ hgentle hterm using fun i => exists_eventuallyKahler_exactDyadicQEA (hK i)
  let k := threshold 0
  let V (i j : ℕ) := U i (j + k)
  have hV₀ (j : ℕ) : IsThetaPshPotential (θ 0).val (V 0 j) ∧
      IsKahlerCurrentPotential (θ 0) (V 0 j) :=
    hterm 0 (j + k) (Nat.le_add_left _ _)
  have hV (i j : ℕ) (hj : threshold i ≤ j) : IsThetaPshPotential (θ i).val (V i j) ∧
      IsKahlerCurrentPotential (θ i) (V i j) :=
    hterm i (j + k) (hj.trans (Nat.le_add_right _ _))
  have hQ₀ : SGPT.PSH.SourceQuasiEquisingularApproximation (θ 0) (u 0) (V 0) :=
    SGPT.PSH.sourceQuasiEquisingularApproximation_tail (hQ 0) k
  let C := rootCartierAny (RealBottChern.ofRepresentative ωX.form)
  let S (j : ℕ) := currentBDivisorAnyOn (ModelSystem.blowup (m + 1) X)
    (representedCurrent (θ 0) (V 0 j) (hV₀ j).1)
  let B (j : ℕ) := S j - C
  have hSconv : ConvergesAny atTop S (D + C) := by
    have hc := representedFamily_converges_of_kahler_qea ωX (θ 0) (u 0) (hu 0) (hK 0)
      (V 0) hQ₀ (fun j => (hV₀ j).1)
    rw [hfamily 0] at hc
    simpa only [reciprocalStep, Nat.cast_zero, zero_add, div_one, one_smul] using hc
  have hBconv : ConvergesAny atTop B D := by
    simpa only [add_sub_cancel_right] using convergesAny_sub_const hSconv C
  let j := fastIndex threshold
  have hj (i : ℕ) : threshold i ≤ j i := fastIndex_ge threshold i
  let F (i : ℕ) := currentBDivisorAnyOn (ModelSystem.blowup (m + 1) X)
    (representedCurrent (θ i) (V i (j i)) (hV i (j i) (hj i)).1)
  have hF (i : ℕ) : IsAlgNefCartierAny (F i) ∧ 0 < volumeAny (F i) :=
    ⟨isAlgNefCartierAny_representedCurrent ωX (θ i) (V i (j i)) (hV i (j i) (hj i)).1
        (hgentle i (j i + k)).2.2.1 (hθNS i),
      (representedFamily_big_nefCartier ωX (θ i) (V i (j i))
        (hV i (j i) (hj i)).1 (hV i (j i) (hj i)).2 (hgentle i (j i + k)).2.2.1).2⟩
  have hmatch (i : ℕ) : F i = B (j i) + reciprocalStep i • C := by
    have hs := sameDyadicType_of_IEquivalent (hI i) (hgentle i) (hgentle 0) (j i + k)
    exact matchedRow_family_minus_shift ωX (sourceRootClass D) θ hclass i
      (V i (j i)) (V 0 (j i)) (hV i (j i) (hj i)).1 (hV₀ (j i)).1 hs
  refine ⟨F, hF, ?_, ?_⟩
  · intro a b hab π
    have hjab := (fastIndex_strictMono threshold).monotone hab
    have hIorder := iOrderOnManifold_of_le (hV₀ (j a)).1.1.quasiPlurisubharmonic
      (fun x => hQ₀.2.2.1.1 x hjab)
    have hd := represented_difference_mem_effectiveClosure π (κ π) (θ 0)
      (hV₀ (j b)).1 (hV₀ (j a)).1 hIorder
    have ht := rootMetered_mem_effectiveClosure κ H π
    have hsum := closure_finiteEffectiveCone_add_smul _ hd ht
      (sub_nonneg.mpr (reciprocalStep_antitone hab))
    rw [hmatch a, hmatch b]
    have hdiff : ((S (j a)).val π - C.val π + reciprocalStep a • C.val π) -
        ((S (j b)).val π - C.val π + reciprocalStep b • C.val π) =
        (S (j a)).val π - (S (j b)).val π +
          (reciprocalStep a - reciprocalStep b) • C.val π := by
      rw [sub_smul]
      abel
    change (((S (j a)).val π - C.val π + reciprocalStep a • C.val π) -
      ((S (j b)).val π - C.val π + reciprocalStep b • C.val π)) ∈ effectiveClosure
    rw [hdiff]
    exact hsum
  · have hc := convergesAny_add_smul_zero
      (convergesAny_comp hBconv (fastIndex_tendsto threshold)) C reciprocalStep_tendsto
    have heF : F = (fun i => B (j i) + reciprocalStep i • C) := funext hmatch
    rw [heF]
    exact hc


open AlgebraicGeometry

/-- The converse closure comparison on a single incarnation. The hypothesis is the literal
correspondence between the scheme primes' numerical classes and the analytic prime classes. -/
theorem numericalClass_mem_effectiveClosure_of_chern
    {Y : Type} [TopologicalSpace Y] [ChartedSpace (ComplexModel (m + 1)) Y]
    [IsComplexManifold (m + 1) Y] [CompactSpace Y] [ConnectedSpace Y]
    {V : Scheme.{0}} (hY : SGPT.Trace.Bertini.IsProjectiveManifold (m + 1) Y)
    (prime : {x : V // Order.coheight x = 1} → NumericalClasses m Y)
    (corr : {x : V // Order.coheight x = 1} ≃ SGPT.PSH.GeometricPrimeCarrier (m + 1) Y)
    (hprime : ∀ P, numericalClassEquiv hY (prime P) = primeCycleClassNS (corr P))
    (a : NumericalClasses m Y) (ha : (numericalClassEquiv hY a : RealBottChern (m + 1) Y) ∈
      effectiveClosure) :
    a ∈ @closure _ (euclideanTopology _) (finiteEffectiveCone prime) := by
  let V₁ := NumericalClasses m Y
  let V₂ := RealBottChern (m + 1) Y
  letI := euclideanTopology V₁
  letI := euclideanTopology V₂
  let L : V₁ →ₗ[ℝ] V₂ := (neronSeveri (m + 1) Y).subtype.comp
    (numericalClassEquiv hY).toLinearMap
  have hinj : Function.Injective L :=
    Subtype.val_injective.comp (numericalClassEquiv hY).injective
  have hind : Topology.IsInducing L := by
    apply Topology.isInducing_iff_nhds.mpr
    intro a
    apply le_antisymm
    · apply (tendsto_comap_iff).mpr
      exact (tendsto_euclideanTopology_iff_of_injective L hinj).mp tendsto_id
    · have h : Tendsto L (comap L (𝓝 (L a))) (𝓝 (L a)) := tendsto_comap
      have hId : Tendsto (id : V₁ → V₁) (comap L (𝓝 (L a))) (𝓝 a) :=
        (tendsto_euclideanTopology_iff_of_injective L hinj).mpr h
      simpa only [Tendsto, map_id] using hId
  have himage : L '' finiteEffectiveCone prime =
      finiteEffectiveCone (fun P : SGPT.PSH.GeometricPrimeCarrier (m + 1) Y =>
        cycleClass (SGPT.Siu.primeEffectiveDivisor P)) := by
    change (((neronSeveri (m + 1) Y).subtype : _ → _) ∘ numericalClassEquiv hY) ''
      finiteEffectiveCone prime = _
    rw [Set.image_comp, (numericalClassEquiv_effective_cones hY prime corr hprime).1]
    apply le_antisymm
    · rintro _ ⟨b, ⟨S, c, hc, rfl⟩, rfl⟩
      refine ⟨S, c, hc, ?_⟩
      change (neronSeveri (m + 1) Y).subtype (∑ P ∈ S, c P • primeCycleClassNS P) = _
      simp only [map_sum, map_smul]
      rfl
    · rintro _ ⟨S, c, hc, rfl⟩
      refine ⟨∑ P ∈ S, c P • primeCycleClassNS P, ⟨S, c, hc, rfl⟩, ?_⟩
      change (neronSeveri (m + 1) Y).subtype (∑ P ∈ S, c P • primeCycleClassNS P) = _
      simp only [map_sum, map_smul]
      rfl
  change a ∈ closure (finiteEffectiveCone prime)
  rw [hind.closure_eq_preimage_closure_image, himage]
  exact ha


/-- A proper prime pushforward takes each prime to zero or to a nonnegative multiple
of a target prime. Its linear extension respects algebraic effective closures. -/
theorem mapsTo_effectiveClosure_of_push_primes
    {P Q V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    (p : P → V) (q : Q → W) (L : V →ₗ[ℝ] W)
    (hL : ∀ a, L (p a) = 0 ∨ ∃ b : Q, ∃ c : ℝ, 0 ≤ c ∧ L (p a) = c • q b) :
    MapsTo L (@closure _ (euclideanTopology V) (finiteEffectiveCone p))
      (@closure _ (euclideanTopology W) (finiteEffectiveCone q)) := by
  classical
  letI := euclideanTopology V
  letI := euclideanTopology W
  have hzero : (0 : W) ∈ finiteEffectiveCone q :=
    ⟨∅, fun _ => 0, by simp, by simp⟩
  have hfinite : MapsTo L (finiteEffectiveCone p) (finiteEffectiveCone q) := by
    rintro _ ⟨S, c, hc, rfl⟩
    simp only [map_sum, map_smul]
    induction S using Finset.induction_on with
    | empty =>
      simpa using hzero
    | @insert a S hna ih =>
      rw [Finset.sum_insert hna]
      apply finiteEffectiveCone_add _
        (ih (fun i hi => hc i (Finset.mem_insert_of_mem hi)))
      apply finiteEffectiveCone_smul _ (hc a (Finset.mem_insert_self _ _))
      rcases hL a with h | ⟨b, r, hr, h⟩
      · rwa [h]
      · rw [h]
        refine ⟨{b}, fun _ => r, fun _ _ => hr, ?_⟩
        simp
  have hcont : Continuous L := by
    apply continuous_iff_continuousAt.mpr
    intro x
    apply tendsto_euclideanTopology_iff.mpr
    intro φ
    exact (continuous_euclideanTopology (φ.comp L)).continuousAt
  intro x hx
  have himage : L '' finiteEffectiveCone p ⊆ finiteEffectiveCone q := by
    rintro _ ⟨a, ha, rfl⟩
    exact hfinite ha
  exact closure_mono himage (image_closure_subset_closure_image hcont ⟨x, hx, rfl⟩)

/-- Read a difference on an arbitrary algebraic model by pushing its difference from a
cofinal algebraized book model. The equality `htrace` is the transition formula for
the coordinates of the cofinal Chern equivalence. -/
theorem algebraicTrace_mem_effectiveClosure_of_dominating_chern
    {Y : Type} [TopologicalSpace Y] [ChartedSpace (ComplexModel (m + 1)) Y]
    [IsComplexManifold (m + 1) Y] [CompactSpace Y] [ConnectedSpace Y]
    {V : Scheme.{0}} (hY : SGPT.Trace.Bertini.IsProjectiveManifold (m + 1) Y)
    (highPrime : {x : V // Order.coheight x = 1} → NumericalClasses m Y)
    (corr : {x : V // Order.coheight x = 1} ≃ SGPT.PSH.GeometricPrimeCarrier (m + 1) Y)
    (hprime : ∀ P, numericalClassEquiv hY (highPrime P) = primeCycleClassNS (corr P))
    {W : Scheme.{0}} {N : Type*} [AddCommGroup N] [Module ℝ N]
    (prime : {x : W // Order.coheight x = 1} → N)
    (push : NumericalClasses m Y →ₗ[ℝ] N)
    (hpush : ∀ P, push (highPrime P) = 0 ∨
      ∃ Q : {x : W // Order.coheight x = 1}, ∃ c : ℝ, 0 ≤ c ∧ push (highPrime P) = c • prime Q)
    (upper lower : NumericalClasses m Y) (upperTarget lowerTarget : N)
    (htrace : push (upper - lower) = upperTarget - lowerTarget)
    (h : (numericalClassEquiv hY (upper - lower) : RealBottChern (m + 1) Y) ∈ effectiveClosure) :
    upperTarget - lowerTarget ∈ @closure _ (euclideanTopology N) (finiteEffectiveCone prime) := by
  rw [← htrace]
  exact mapsTo_effectiveClosure_of_push_primes highPrime prime push hpush
    (numericalClass_mem_effectiveClosure_of_chern hY highPrime corr hprime (upper - lower) h)

end SGPT.BDivisor.BD7
