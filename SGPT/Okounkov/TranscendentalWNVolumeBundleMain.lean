import SGPT.Okounkov.TranscendentalWNVolumeBundleChartMass

/-!
# The bundle Legendre identity on the exceptional divisor (package WN-VF4)

Blueprint `claude-tok-wn-vf3`, node `tok-wn-vf3:bundle-legendre-ma` (refined), and
`claude-tok-wn-vf4`, nodes `tok-wn-vf4:null-sets`, `tok-wn-vf4:gluing`; source WN21 Theorem 3.5
applied at the end of §4 on `ℰ \ (X' ∪ Z̃) = N_{Z|X} \ 0`.

`excBundleLegendreMA_of_charts`: `ExcBundleChartStatement F →
ExcBundleLegendreMAStatement F`.  Cover `Z` by countably many bundle chart domains, cut `Z` into
the disjoint Borel pieces `Cₙ` (off the pluripolar set `Z ∩ (E_nK(ξ) ∪ E_nK(ξ_c))`), apply
`excBundle_chart_identity` on each piece, and sum (the integrands are a.e.-measurable,
`legendreMAMeasurable`).  The rest of `ℰ` — the zero sets of `S₁`, `S₂` and `π⁻¹(E_nK(ξ) ∪ E_nK(ξ_c))`
— is a proper analytic subset of the connected `ℰ`, so it is pluripolar and not charged.  Finally
`∫_Z ⟨((θ - tη)|_Z + dd^c W_t)^m⟩ = R(ξ_t)` (`firstFlagRestrictedVolume_eq_mass`).
-/

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

noncomputable section

universe u

namespace SGPT.Okounkov.TranscendentalWN

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Manifold ContDiff ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.HolomorphicMaps
open SGPT.Foundations.Analysis.FirstPass.LocalPotentialPullback
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.NumericalRestrictedVolumeScaffold
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.GlobalNonPluripolar
open SGPT.Foundations.Analysis.Pending.FiniteGeodesicMaximality
open SGPT.Okounkov.TranscendentalMain

/-! ### Null sets -/

section Null

variable {k n : ℕ} {V : Type*} [TopologicalSpace V] [ChartedSpace (ComplexModel k) V]
  [IsComplexManifold k V] [ConnectedSpace V] {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- **`tok-wn-vf4:null-sets`**: the preimage of an analytic set under a holomorphic map from a
connected manifold, missing one point, is pluripolar. -/
theorem manifoldLocallyPluripolar_preimage_of_notMem {f : V → M}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ f) {A : Set M}
    (hA : IsComplexAnalyticSubset (n := n) A) {v : V} (hv : f v ∉ A) :
    ManifoldLocallyPluripolar (n := k) (f ⁻¹' A) := by
  have hpre := AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage hf hA
  refine ModificationMassInvariance.manifoldLocallyPluripolar_of_isComplexAnalyticSubset hpre ?_
  refine PshAnalyticSetExtension.IsComplexAnalyticSubset.interior_eq_empty_of_ne_univ hpre ?_
  intro h
  exact hv (show v ∈ f ⁻¹' A from h ▸ mem_univ v)

/-- The zero set `{U ≤ 0}` of a factorized weight is analytic. -/
theorem isComplexAnalyticSubset_weight_nonpos [CompactSpace M] {U : M → ℝ}
    (Fw : FactorizedWeightForm.WeightFactorization n U) :
    IsComplexAnalyticSubset (n := n) {y | U y ≤ 0} := by
  have h := ResidualNef.isComplexAnalyticSubset_support
    (ExceptionalMetricProof.ofWeightFactorization Fw 1 one_pos)
  convert h using 1
  ext y
  simp only [mem_ofPred_eq, MeteredEffectiveQDivisor.support, mem_poleSet,
    ExceptionalMetricProof.ofWeightFactorization, FactorizedWeightPsh.logWeight, Rat.cast_one,
    EReal.coe_one, one_mul, ENNReal.log_eq_bot_iff, ENNReal.ofReal_eq_zero]

end Null

variable {m : ℕ} (F : OriginalFlagGeometry.{u} (m + 1))

/-! ### The gluing -/

section Gluing

variable {𝒳 : Type u} [TopologicalSpace 𝒳] [ChartedSpace (ComplexModel (m + 1 + 1)) 𝒳]
  [IsComplexManifold (m + 1 + 1) 𝒳] {μ : 𝒳 → F.carrier × ProjectiveLine}

omit [IsComplexManifold (m + 1 + 1) 𝒳] in
/-- The projection `ℰ → Z`. -/
def excProjZ (p : exceptionalSet F μ) : F.tail.carrier :=
  ⟨(μ p).1, ((mem_deformationCentre_iff F).mp p.2).1⟩

omit [IsComplexManifold (m + 1 + 1) 𝒳] in
theorem continuous_excProjZ (hμ : Continuous μ) : Continuous (excProjZ F (μ := μ)) :=
  ((continuous_fst.comp hμ).comp continuous_subtype_val).subtype_mk _

omit [IsComplexManifold (m + 1 + 1) 𝒳] in
theorem firstFlagInclusion_excProjZ (p : exceptionalSet F μ) :
    firstFlagInclusion F (excProjZ F p) = (μ p).1 := rfl

omit [IsComplexManifold (m + 1 + 1) 𝒳] in
theorem mem_image_firstFlagInclusion_iff (p : exceptionalSet F μ) (C : Set F.tail.carrier) :
    (μ p).1 ∈ firstFlagInclusion F '' C ↔ excProjZ F p ∈ C := by
  constructor
  · rintro ⟨y, hy, hyp⟩
    have : y = excProjZ F p := Subtype.val_injective hyp
    rwa [← this]
  · intro h
    exact ⟨_, h, rfl⟩

/-- Every point of `Z` lies under a point of `ℰ \ (X' ∪ Z̃)`. -/
theorem exists_exceptional_point (hch : ExcBundleChartStatement F)
    {E : MeteredEffectiveQDivisor (m + 1) F.carrier} (hE : IsFirstDivisorUnitMetric F E)
    (hμ : IsNormalConeDeformation F μ) (y : F.tail.carrier) :
    ∃ p ∈ exceptionalSet F μ, 0 < strictWeight F E μ p ∧ 0 < zStrictWeight F E μ p ∧
      (μ p).1 = firstFlagInclusion F y := by
  obtain ⟨eZ, Ω, Λ, g, hc, hy, hyΩ⟩ := hch E hE 𝒳 μ hμ y
  obtain ⟨h1, h2, -⟩ := hc.weights _ hyΩ 1 one_ne_zero
  refine ⟨Λ (eZ.val y) 1, hc.mem _ hyΩ 1, h1, h2, ?_⟩
  rw [hc.proj _ hyΩ, eZ.val.left_inv hy]

end Gluing

/-! ### The bundle Legendre identity -/

/-- **`tok-wn-vf3:bundle-legendre-ma`** (WN21 Theorem 3.5 on `ℰ \ (X' ∪ Z̃) = N_{Z|X} \ 0`) from
the bundle charts (`ExcBundleChartStatement`). -/
theorem excBundleLegendreMA_of_charts (hch : ExcBundleChartStatement F) :
    ExcBundleLegendreMAStatement F := by
  intro E hE hE0 𝒳 _ _ _ μ hμ Eℰ hEℰ θ b c hc hcb hξ hξc W hW1 hW2 hW3 φ hφ hformula
  classical
  obtain ⟨C₀, hC₀⟩ := hW3
  letI := exceptionalChartedSpace F hμ
  haveI := isComplexManifold_exceptional F hμ
  letI : MeasurableSpace (exceptionalSet F μ) := borel (exceptionalSet F μ)
  haveI : BorelSpace (exceptionalSet F μ) := ⟨rfl⟩
  haveI := compactSpace_exceptional F hμ
  haveI := compactSpace_normalCone F hμ
  haveI := connectedSpace_exceptional F hμ
  letI : MeasurableSpace F.tail.carrier := borel F.tail.carrier
  haveI : BorelSpace F.tail.carrier := ⟨rfl⟩
  have hι := contMDiff_firstFlagInclusion F
  have hιE := contMDiff_exceptionalInclusion F hμ
  set Θ := deformationForm F hμ.contMDiff θ b c Eℰ with hΘ
  set ν := globalMixedMeasure (fun _ : Fin (m + 1) => ClosedRealOneOneForm.pullback hιE Θ)
    (fun _ => fun y : exceptionalSet F μ => φ y) (fun _ => hφ.1) with hνdef
  have hmass : exceptionalMass F hμ Θ φ hφ = ν univ := rfl
  set ξ := RealBottChern.ofRepresentative θ with hξdef
  set ξc := RealBottChern.ofRepresentative θ - c • RealBottChern.ofRepresentative E.curvature
    with hξcdef
  have : Nonempty F.carrier := by
    obtain ⟨y, -, -⟩ := hξ.2
    exact ⟨y⟩
  have hbig0 : IsBigClass ξ := (SGPT.PSH.BookCurrent.isBig_iff_isBigClass _).mp hξ.1
  have hbigc : IsBigClass ξc := (SGPT.PSH.BookCurrent.isBig_iff_isBigClass _).mp hξc.1
  have hA0 := NonKahlerLocusPoleSet.isComplexAnalyticSubset_nonKahlerLocus (Nat.succ_pos m) ξ hbig0
  have hAc := NonKahlerLocusPoleSet.isComplexAnalyticSubset_nonKahlerLocus (Nat.succ_pos m) ξc hbigc
  set bad : Set F.carrier := nonKahlerLocus ξ ∪ nonKahlerLocus ξc with hbaddef
  -- points of `Z` off each non-Kähler locus
  obtain ⟨x₁, hx₁Z, hx₁⟩ := hξ.2
  obtain ⟨x₂, hx₂Z, hx₂⟩ := hξc.2
  set y₁ : F.tail.carrier := ⟨x₁, hx₁Z⟩
  set y₂ : F.tail.carrier := ⟨x₂, hx₂Z⟩
  have : Nonempty F.tail.carrier := ⟨y₁⟩
  -- the null sets on `Z`
  have hZ0 : ManifoldLocallyPluripolar (n := m) (firstFlagInclusion F ⁻¹' nonKahlerLocus ξ) :=
    manifoldLocallyPluripolar_preimage_of_notMem hι hA0 (v := y₁) hx₁
  have hZc : ManifoldLocallyPluripolar (n := m) (firstFlagInclusion F ⁻¹' nonKahlerLocus ξc) :=
    manifoldLocallyPluripolar_preimage_of_notMem hι hAc (v := y₂) hx₂
  -- the null sets on `ℰ`
  have hπE : ContMDiff 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel (m + 1)) ∞
      (fun p : exceptionalSet F μ => (μ p).1) :=
    (contMDiff_deformationProjX F hμ.contMDiff).comp hιE
  obtain ⟨p₁, hp₁, hp₁S1, hp₁S2, hp₁x⟩ := exists_exceptional_point F hch hE hμ y₁
  obtain ⟨p₂, hp₂, -, -, hp₂x⟩ := exists_exceptional_point F hch hE hμ y₂
  have hN1 : ManifoldLocallyPluripolar (n := m + 1)
      ((Subtype.val : exceptionalSet F μ → 𝒳) ⁻¹' {y | strictWeight F E μ y ≤ 0}) :=
    manifoldLocallyPluripolar_preimage_of_notMem hιE
      (isComplexAnalyticSubset_weight_nonpos (strictFactorization F hμ hE))
      (v := ⟨p₁, hp₁⟩) (not_le.mpr hp₁S1)
  have hN2 : ManifoldLocallyPluripolar (n := m + 1)
      ((Subtype.val : exceptionalSet F μ → 𝒳) ⁻¹' {y | zStrictWeight F E μ y ≤ 0}) :=
    manifoldLocallyPluripolar_preimage_of_notMem hιE
      (isComplexAnalyticSubset_weight_nonpos (zStrictFactorization F hμ hE))
      (v := ⟨p₁, hp₁⟩) (not_le.mpr hp₁S2)
  have hN3 : ManifoldLocallyPluripolar (n := m + 1)
      ((fun p : exceptionalSet F μ => (μ p).1) ⁻¹' nonKahlerLocus ξ) :=
    manifoldLocallyPluripolar_preimage_of_notMem hπE hA0 (v := ⟨p₁, hp₁⟩)
      (by show (μ p₁).1 ∉ nonKahlerLocus ξ; rw [hp₁x]; exact hx₁)
  have hN4 : ManifoldLocallyPluripolar (n := m + 1)
      ((fun p : exceptionalSet F μ => (μ p).1) ⁻¹' nonKahlerLocus ξc) :=
    manifoldLocallyPluripolar_preimage_of_notMem hπE hAc (v := ⟨p₂, hp₂⟩)
      (by show (μ p₂).1 ∉ nonKahlerLocus ξc; rw [hp₂x]; exact hx₂)
  have hνnull := globalMixedMeasure_doesNotChargeManifoldPluripolar
    (θ := fun _ : Fin (m + 1) => ClosedRealOneOneForm.pullback hιE Θ)
    (u := fun _ => fun y : exceptionalSet F μ => φ y) (fun _ => hφ.1)
  -- the chart data at every point of `Z`
  have hθpsh : ThetaPlurisubharmonic θ.val (W 0) := by
    have h := hW1 0 ⟨le_rfl, hc.le⟩
    rwa [zero_smul, sub_zero] at h
  have hdata : ∀ y : F.tail.carrier, ∃ (eZ : ComplexChart m F.tail.carrier)
      (Ω : Set (ComplexModel m)) (Λ : ComplexModel m → ℂ → 𝒳) (g : ComplexModel m → ℝ)
      (dX : ComplexChart (m + 1) F.carrier) (WX : Set (ComplexModel (m + 1)))
      (ρX : ComplexModel (m + 1) → ℝ), IsExcBundleChart F E hμ eZ Ω Λ g ∧
        IsSmoothLocalPotential θ.val dX WX ρX ∧
        Ω ⊆ potentialDomain (firstFlagInclusion F) eZ dX WX ∧
        y ∈ eZ.val.source ∧ eZ.val y ∈ Ω := by
    intro y
    obtain ⟨eZ, Ω, Λ, g, hc', hy, hyΩ⟩ := hch E hE 𝒳 μ hμ y
    set dX : ComplexChart (m + 1) F.carrier := complexChartAt (firstFlagInclusion F y)
    have hxd : firstFlagInclusion F y ∈ dX.val.source := mem_complexChartAt_source _
    obtain ⟨WX, ρX, hxW, hρX⟩ := hθpsh.hasSmoothLocalPotentials dX _ (dX.val.map_source hxd)
    have hPD := potentialDomain_isOpen hι eZ dX hρX.1
    refine ⟨eZ, Ω ∩ potentialDomain (firstFlagInclusion F) eZ dX WX, Λ, g, dX, WX, ρX,
      hc'.mono (hc'.isOpen.inter hPD) inter_subset_left, hρX, inter_subset_right, hy,
      hyΩ, ?_⟩
    refine ⟨⟨eZ.val.map_source hy, ?_⟩, ?_⟩
    · change firstFlagInclusion F (eZ.val.symm (eZ.val y)) ∈ dX.val.source
      rw [eZ.val.left_inv hy]; exact hxd
    · change dX.val (firstFlagInclusion F (eZ.val.symm (eZ.val y))) ∈ WX
      rw [eZ.val.left_inv hy]; exact hxW
  choose eZ Ω Λ g dX WX ρX hchart hρX hΩX hy hyΩ using hdata
  set U : F.tail.carrier → Set F.tail.carrier := fun y => (eZ y).val.source ∩ (eZ y).val ⁻¹' Ω y
    with hUdef
  have hUo : ∀ y, IsOpen (U y) := fun y =>
    (eZ y).val.isOpen_inter_preimage (hchart y).isOpen
  obtain ⟨ys, hys⟩ := exists_seq_cover U hUo fun y => ⟨hy y, hyΩ y⟩
  set D : ℕ → Set F.tail.carrier := disjointed fun n => U (ys n) with hDdef
  have hDm : ∀ n, MeasurableSet (D n) :=
    MeasurableSet.disjointed fun n => (hUo (ys n)).measurableSet
  have hDdisj : Pairwise (Function.onFun Disjoint D) := disjoint_disjointed _
  have hDcov : (⋃ n, D n) = univ := by rw [hDdef, iUnion_disjointed, hys]
  have hDU : ∀ n, D n ⊆ U (ys n) := disjointed_subset _
  set Zg : Set F.tail.carrier := (firstFlagInclusion F ⁻¹' bad)ᶜ with hZgdef
  have hZgm : MeasurableSet Zg :=
    ((hA0.isClosed.union hAc.isClosed).preimage hι.continuous).isOpen_compl.measurableSet
  set Cn : ℕ → Set F.tail.carrier := fun n => D n ∩ Zg with hCndef
  have hCnm : ∀ n, MeasurableSet (Cn n) := fun n => (hDm n).inter hZgm
  have hCndisj : Pairwise (Function.onFun Disjoint Cn) := fun i j hij =>
    (hDdisj hij).mono inter_subset_left inter_subset_left
  have hCnU : (⋃ n, Cn n) = Zg := by rw [← iUnion_inter, hDcov, univ_inter]
  -- the identity on each piece
  have hpiece := fun n => excBundle_chart_identity hE hμ hEℰ hc hξ hξc hW1 hW2 hC₀ hformula
    (hchart (ys n)) (dX (ys n)) (hρX (ys n)) (hΩX (ys n)) hφ.1 (Cn n) (hCnm n)
    (fun y hy => (hDU n hy.1).1) (fun y hy => ⟨(hDU n hy.1).2, hy.2⟩)
  -- the good part of `ℰ`
  set T : ℕ → Set (exceptionalSet F μ) := fun n => {p | 0 < strictWeight F E μ p ∧
    0 < zStrictWeight F E μ p ∧ (μ p).1 ∈ firstFlagInclusion F '' Cn n} with hTdef
  have hS1c : Continuous fun p : exceptionalSet F μ => strictWeight F E μ p :=
    (continuous_strictWeight F hμ hE).comp continuous_subtype_val
  have hS2c : Continuous fun p : exceptionalSet F μ => zStrictWeight F E μ p :=
    (continuous_zStrictWeight F hμ hE).comp continuous_subtype_val
  have hTm : ∀ n, MeasurableSet (T n) := by
    intro n
    have h1 : MeasurableSet {p : exceptionalSet F μ | 0 < strictWeight F E μ p} :=
      (isOpen_lt continuous_const hS1c).measurableSet
    have h2 : MeasurableSet {p : exceptionalSet F μ | 0 < zStrictWeight F E μ p} :=
      (isOpen_lt continuous_const hS2c).measurableSet
    have h3 : MeasurableSet {p : exceptionalSet F μ | (μ p).1 ∈ firstFlagInclusion F '' Cn n} := by
      have : {p : exceptionalSet F μ | (μ p).1 ∈ firstFlagInclusion F '' Cn n} =
          excProjZ F ⁻¹' Cn n := by
        ext p; exact mem_image_firstFlagInclusion_iff F p _
      rw [this]
      exact (continuous_excProjZ F hμ.continuous).measurable (hCnm n)
    exact h1.inter (h2.inter h3)
  have hTdisj : Pairwise (Function.onFun Disjoint T) := by
    intro i j hij
    rw [Function.onFun, disjoint_left]
    intro p hpi hpj
    simp only [hTdef, mem_ofPred_eq, mem_image_firstFlagInclusion_iff] at hpi hpj
    exact disjoint_left.mp (hCndisj hij) hpi.2.2 hpj.2.2
  set Tg : Set (exceptionalSet F μ) := {p | 0 < strictWeight F E μ p ∧
    0 < zStrictWeight F E μ p ∧ (μ p).1 ∉ bad} with hTgdef
  have hTU : (⋃ n, T n) = Tg := by
    ext p
    simp only [mem_iUnion, hTdef, hTgdef, mem_ofPred_eq, mem_image_firstFlagInclusion_iff]
    constructor
    · rintro ⟨n, h1, h2, h3⟩
      exact ⟨h1, h2, h3.2⟩
    · rintro ⟨h1, h2, h3⟩
      have hmem : excProjZ F p ∈ ⋃ n, Cn n := by
        rw [hCnU]; exact h3
      obtain ⟨n, hn⟩ := mem_iUnion.mp hmem
      exact ⟨n, h1, h2, hn⟩
  have hTgc : ν Tgᶜ = 0 := by
    refine measure_mono_null (t := ((Subtype.val : exceptionalSet F μ → 𝒳) ⁻¹'
      {y | strictWeight F E μ y ≤ 0} ∪ (Subtype.val : exceptionalSet F μ → 𝒳) ⁻¹'
      {y | zStrictWeight F E μ y ≤ 0}) ∪ ((fun p : exceptionalSet F μ => (μ p).1) ⁻¹'
      nonKahlerLocus ξ ∪ (fun p : exceptionalSet F μ => (μ p).1) ⁻¹' nonKahlerLocus ξc))
      ?_ ?_
    · intro p hp
      simp only [hTgdef, mem_compl_iff, mem_ofPred_eq, not_and_or, not_lt, not_not] at hp
      rcases hp with h | h | h
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr h)
      · rcases h with h | h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h)
    · exact measure_union_null (measure_union_null (hνnull _ hN1) (hνnull _ hN2))
        (measure_union_null (hνnull _ hN3) (hνnull _ hN4))
  have hνU : ν univ = ∑' n, ν (T n) := by
    have hTgm : MeasurableSet Tg := hTU ▸ MeasurableSet.iUnion hTm
    rw [← measure_add_measure_compl hTgm, hTgc, add_zero, ← hTU, measure_iUnion hTdisj hTm]
  -- the integrands
  set Rt : ℝ → ℝ≥0∞ := fun t => firstFlagRestrictedVolume F (RealBottChern.ofRepresentative θ -
    t • RealBottChern.ofRepresentative E.curvature) with hRtdef
  have hZbad : ∀ t, excZMeasure F E θ c W hW1 t (firstFlagInclusion F ⁻¹' bad) = 0 := by
    intro t
    rw [excZMeasure]
    split_ifs with ht
    · have hnull := globalMixedMeasure_doesNotChargeManifoldPluripolar
        (θ := fun _ : Fin m => ClosedRealOneOneForm.pullback hι (θ - t • E.curvature))
        (u := fun _ => fun y => W t (firstFlagInclusion F y))
        (fun _ => GlobalPotentialPullback.thetaPlurisubharmonic_comp hι (hW1 t ht))
      rw [preimage_union]
      exact measure_union_null (hnull _ hZ0) (hnull _ hZc)
    · rfl
  have hsum : ∀ t ∈ Icc (0 : ℝ) c, ∑' n, excZMeasure F E θ c W hW1 t (Cn n) = Rt t := by
    intro t ht
    rw [← measure_iUnion hCndisj hCnm, hCnU]
    have hcompl := hZbad t
    have hfull : excZMeasure F E θ c W hW1 t Zg = excZMeasure F E θ c W hW1 t univ := by
      rw [← measure_add_measure_compl hZgm, hZgdef, compl_compl, hcompl, add_zero]
    rw [hfull]
    have hξt := isBigMeetingFirstDivisor_sub_smul_of_mem_Icc F hξ hξc ht
    rw [← ofRepresentative_sub_smul] at hξt
    obtain ⟨hWZ, hR⟩ := firstFlagRestrictedVolume_eq_mass F hξt (hW1 t ht) (hC₀ t ht)
    simp only [hRtdef]
    rw [← ofRepresentative_sub_smul, hR, excZMeasure, dif_pos ht]
    rfl
  have hfin : ∀ t ∈ Icc (0 : ℝ) c, Rt t < ⊤ := by
    intro t ht
    rw [← hsum t ht, ← measure_iUnion hCndisj hCnm, excZMeasure, dif_pos ht]
    exact globalMixedMeasure_apply_lt_top F.tail.omega _ _
  have hmeasR : AEMeasurable Rt (volume.restrict (Icc (0 : ℝ) c)) := by
    refine (AEMeasurable.ennreal_tsum fun n => (hpiece n).2).congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact hsum t ht
  have hint : ν univ = ((m + 1 : ℕ) : ℝ≥0∞) * ∫⁻ t in Icc (0 : ℝ) c, Rt t := by
    rw [hνU, tsum_congr fun n => (hpiece n).1, ENNReal.tsum_mul_left,
      ← lintegral_tsum fun n => (hpiece n).2]
    congr 1
    exact setLIntegral_congr_fun measurableSet_Icc hsum
  rw [hmass, hint, ENNReal.toReal_mul, ENNReal.toReal_natCast,
    intervalIntegral.integral_of_le hc.le, ← integral_Icc_eq_integral_Ioc,
    integral_toReal hmeasR ((ae_restrict_iff' measurableSet_Icc).mpr
      (Eventually.of_forall hfin))]

end SGPT.Okounkov.TranscendentalWN
