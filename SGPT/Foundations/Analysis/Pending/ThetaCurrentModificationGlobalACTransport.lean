import SGPT.Foundations.Analysis.Pending.ThetaCurrentModificationLocalTransport
import SGPT.Foundations.Analysis.Pending.GlobalACTopPluripolarNull

set_option autoImplicit false

/-! The ENTIRE mathematical BP proof precedes Lean. The same original
unbounded potentials, currents and atlas-independent measures are retained.
All exceptional nullity, fiber containment and measure compatibility are
internally produced. Infinite mass is allowed throughout. -/

noncomputable section
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Distributions ContDiff Manifold
universe u
namespace SGPT.Foundations.Analysis.Pending.ThetaCurrentModificationGlobalACTransport
open FirstPass FirstPass.HolomorphicMaps GlobalCurrents
  NaturalThetaPshGeometricCurrent GlobalPositiveCurrentACRestriction
  GlobalPositiveCurrentACTopMeasure GlobalACTopPluripolarNull
  ThetaCurrentModificationLocalTransport AnalyticModificationLocalDiscrepancy
  AnalyticModificationStrongPullback LocalCurrentPullback PositiveCurrentACTopMeasure
  ActualAnalyticCurrentLocalDensity BedfordTaylor

private theorem restrict_eq_of_local_on_open {M : Type*} [TopologicalSpace M]
    [SecondCountableTopology M] [MeasurableSpace M]
    {μ ν : Measure M} {O : Set M}
    (hμ : μ Oᶜ = 0) (hν : ν Oᶜ = 0)
    (hlocal : ∀ x : O, ∃ U : Set M, IsOpen U ∧ x.val ∈ U ∧ U ⊆ O ∧
      μ.restrict U = ν.restrict U) : μ = ν := by
  classical
  choose U hU hxU hUO hEq using hlocal
  obtain ⟨I, hIc, hIU⟩ := TopologicalSpace.isOpen_iUnion_countable U hU
  have : Countable I := hIc.to_subtype
  have hcover : (⋃ i : I, U i) = O := by
    ext x
    constructor
    · intro hx
      obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      exact hUO i hi
    · intro hx
      have hx' : x ∈ ⋃ i ∈ I, U i :=
        hIU ▸ mem_iUnion.mpr ⟨⟨x, hx⟩, hxU ⟨x, hx⟩⟩
      obtain ⟨i, hiI, hxi⟩ := mem_iUnion₂.mp hx'
      exact mem_iUnion.mpr ⟨⟨i, hiI⟩, hxi⟩
  have heq := Measure.restrict_iUnion_congr.mpr (fun i : I => hEq i)
  rw [hcover, Measure.restrict_eq_self_of_ae_mem (ae_iff.mpr hμ),
    Measure.restrict_eq_self_of_ae_mem (ae_iff.mpr hν)] at heq
  exact heq

section ChartMeasure
variable {n : ℕ} {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
  [ChartedSpace (ComplexModel n) X] [ChartedSpace (ComplexModel n) Y]

private theorem measurable_inverse_preimage (e : ComplexChart n X)
    {A : Opens (ComplexModel n)} (hA : A ≤ chartTarget e)
    {S : Set X} (hS : MeasurableSet S) :
    MeasurableSet ((A : Set (ComplexModel n)) ∩ e.val.symm ⁻¹' S) := by
  have hf : ContinuousOn e.val.symm A := e.val.continuousOn_symm.mono hA
  have hemb := MeasurableEmbedding.subtype_coe A.isOpen.measurableSet
  have hm : Measurable ((A : Set (ComplexModel n)).domRestrict e.val.symm) :=
    (continuousOn_iff_continuous_domRestrict.mp hf).measurable
  have ht := hemb.measurableSet_image.mpr (hm hS)
  convert ht using 1
  ext z
  simp only [mem_inter_iff, mem_preimage, mem_image, Subtype.exists,
    exists_and_right, exists_eq_right]
  tauto

private theorem local_pushforward_restrict_eq
    {π : Y → X} (hπ : Continuous π) {Z : Set X} (hZ : IsClosed Z)
    (hinj : ∀ q q' : Y, π q = π q' → π q ∉ Z → q = q')
    (e : ComplexChart n Y) (d : ComplexChart n X)
    (A B : Opens (ComplexModel n)) (hAe : A ≤ chartTarget e) (hBd : B ≤ chartTarget d)
    (hAdom : (A : Set (ComplexModel n)) ⊆ coordinateDomain π e d)
    {σ : ComplexModel n → ComplexModel n}
    (hpair : IsBiholomorphicPair A B (coordinateMap π e d) σ)
    (μY : Measure Y) (μX : Measure X) (lY lX : Measure (ComplexModel n))
    (hY : ∀ S : Set Y, μY (S ∩ e.val.source) = lY (e.val.target ∩ e.val.symm ⁻¹' S))
    (hX : ∀ S : Set X, μX (S ∩ d.val.source) = lX (d.val.target ∩ d.val.symm ⁻¹' S))
    (hcov : (lX.restrict (B : Set (ComplexModel n))).map (onOpen B σ) =
      lY.restrict (A : Set (ComplexModel n))) :
    let U : Set X := (d.val.source ∩ d.val ⁻¹' (B : Set (ComplexModel n))) ∩ Zᶜ
    (μY.map π).restrict U = μX.restrict U := by
  let U : Set X := (d.val.source ∩ d.val ⁻¹' (B : Set (ComplexModel n))) ∩ Zᶜ
  have hU : IsOpen U := (d.val.isOpen_inter_preimage B.isOpen).inter hZ.isOpen_compl
  have hcomm (w : ComplexModel n) (hw : w ∈ B) :
      π (e.val.symm (σ w)) = d.val.symm w := by
    have ha := hpair.mapsTo_inv hw
    have hd := (hAdom ha).2
    have heq : d.val (π (e.val.symm (σ w))) = w := hpair.right_inv w hw
    calc
      π (e.val.symm (σ w)) = d.val.symm (d.val (π (e.val.symm (σ w)))) :=
        (d.val.left_inv hd).symm
      _ = d.val.symm w := congrArg d.val.symm heq
  have hsource (q : Y) (hq : π q ∈ U) : q ∈ e.val.source ∧ e.val q ∈ A := by
    have hw : d.val (π q) ∈ B := hq.1.2
    have ha := hpair.mapsTo_inv hw
    have hqeq : q = e.val.symm (σ (d.val (π q))) := by
      apply hinj q _
      · exact ((hcomm _ hw).trans (d.val.left_inv hq.1.1)).symm
      · exact hq.2
    rw [hqeq]
    exact ⟨e.val.map_target (hAe ha), by rwa [e.val.right_inv (hAe ha)]⟩
  ext S hS
  let Q : Set X := S ∩ U
  let H : Set (ComplexModel n) := (A : Set (ComplexModel n)) ∩ e.val.symm ⁻¹' (π ⁻¹' Q)
  have hQ : MeasurableSet Q := hS.inter hU.measurableSet
  have hH : MeasurableSet H := measurable_inverse_preimage e hAe (hπ.measurable hQ)
  have hpre : π ⁻¹' Q ⊆ e.val.source := fun q hq => (hsource q hq.2).1
  have hsetY : e.val.target ∩ e.val.symm ⁻¹' (π ⁻¹' Q) = H := by
    ext z
    constructor
    · rintro ⟨hz, hq⟩
      have ha := (hsource (e.val.symm z) hq.2).2
      rw [e.val.right_inv hz] at ha
      exact ⟨ha, hq⟩
    · rintro ⟨ha, hq⟩
      exact ⟨hAe ha, hq⟩
  have hsetX : d.val.target ∩ d.val.symm ⁻¹' Q =
      (B : Set (ComplexModel n)) ∩ d.val.symm ⁻¹' Q := by
    ext w
    constructor
    · rintro ⟨hw, hq⟩
      have hb := hq.2.1.2
      change d.val (d.val.symm w) ∈ B at hb
      rw [d.val.right_inv hw] at hb
      exact ⟨hb, hq⟩
    · rintro ⟨hb, hq⟩
      exact ⟨hBd hb, hq⟩
  have hsetCov : onOpen B σ ⁻¹' H ∩ (B : Set (ComplexModel n)) =
      (B : Set (ComplexModel n)) ∩ d.val.symm ⁻¹' Q := by
    ext w
    constructor
    · rintro ⟨hwh, hw⟩
      rw [mem_preimage, onOpen_of_mem hw] at hwh
      exact ⟨hw, by simpa only [mem_preimage, hcomm w hw] using hwh.2⟩
    · rintro ⟨hw, hq⟩
      refine ⟨?_, hw⟩
      rw [mem_preimage, onOpen_of_mem hw]
      exact ⟨hpair.mapsTo_inv hw, by simpa only [mem_preimage, hcomm w hw] using hq⟩
  have hlocal := congrArg (fun μ : Measure (ComplexModel n) => μ H) hcov
  rw [Measure.map_apply (measurable_onOpen_inv hpair) hH,
    Measure.restrict_apply' B.isOpen.measurableSet,
    Measure.restrict_apply' A.isOpen.measurableSet,
    inter_eq_left.mpr (show H ⊆ (A : Set (ComplexModel n)) from inter_subset_left),
    hsetCov] at hlocal
  rw [Measure.restrict_apply hS, Measure.restrict_apply hS,
    Measure.map_apply hπ.measurable hQ]
  change μY (π ⁻¹' Q) = μX Q
  calc
    μY (π ⁻¹' Q) = μY ((π ⁻¹' Q) ∩ e.val.source) :=
      congrArg μY (inter_eq_left.mpr hpre).symm
    _ = lY H := (hY (π ⁻¹' Q)).trans (congrArg lY hsetY)
    _ = lX ((B : Set (ComplexModel n)) ∩ d.val.symm ⁻¹' Q) := hlocal.symm
    _ = lX (d.val.target ∩ d.val.symm ⁻¹' Q) := congrArg lX hsetX.symm
    _ = μX (Q ∩ d.val.source) := (hX Q).symm
    _ = μX Q := congrArg μX (inter_eq_left.mpr (fun _ hq => hq.2.1.1))
end ChartMeasure

variable {m : ℕ} {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
  [ChartedSpace (ComplexModel (m + 1)) X] [IsComplexManifold (m + 1) X]
  [ChartedSpace (ComplexModel (m + 1)) Y] [IsComplexManifold (m + 1) Y]

private theorem global_inter_chart [CompactSpace X]
    (T : GlobalCurrent (m + 1) X (degreeTwo (Nat.succ_pos m)))
    (hT : IsFullPositive T) (e : ComplexChart (m + 1) X) (S : Set X) :
    globalACtopMeasure T hT (S ∩ e.val.source) =
      acTopMeasure (isPositive_chartSpanCurrent T hT e) (e.val.target ∩ e.val.symm ⁻¹' S) := by
  have hInv : MeasurableEmbedding (fun z : e.val.target => e.val.symm z) :=
    (MeasurableEmbedding.subtype_coe e.val.open_source.measurableSet).comp
      (e.val.toHomeomorphSourceTarget).symm.measurableEmbedding
  have hsub : MeasurableEmbedding (Subtype.val : e.val.target → ComplexModel (m + 1)) :=
    MeasurableEmbedding.subtype_coe e.val.open_target.measurableSet
  have h := congrArg (fun μ : Measure X => μ S) (globalACtopMeasure_restrict_chart T hT e)
  rw [Measure.restrict_apply' e.val.open_source.measurableSet] at h
  refine h.trans ?_
  change (((acTopMeasure (isPositive_chartSpanCurrent T hT e)).comap
      (Subtype.val : e.val.target → ComplexModel (m + 1))).map
        (fun z : e.val.target => e.val.symm z)) S = _
  rw [hInv.map_apply, hsub.comap_apply]
  congr 1
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨w.property, hw⟩
  · intro hz
    exact ⟨⟨z, hz.1⟩, hz.2, rfl⟩

/-- Natural actual modification and original theta-potential data internally
give genuine upstairs compactness/potential and the global SAME-current AC
measure equality. Infinity is retained; no calibration/current/atlas input. -/
theorem exists_global_original_ac_transport [CompactSpace X]
    {π : Y → X} (hπ : IsAnalyticModification (n := m + 1) π)
    (θ : ClosedRealOneOneForm (m + 1) X) {u : X → EReal}
    (hu : IsThetaPshPotential θ.val u) :
    letI : CompactSpace Y := compactSpace_of_isAnalyticModification hπ
    let θY := ClosedRealOneOneForm.pullback hπ.1 θ
    ∃ huY : IsThetaPshPotential θY.val (fun y => u (π y)),
      let TX := thetaPotentialCurrent θ.val u hu
      let TY := thetaPotentialCurrent θY.val (fun y => u (π y)) huY
      let hTX : IsFullPositive TX := fun e α hα =>
        thetaPotentialCurrent_full_positive θ.val u hu e α hα
      let hTY : IsFullPositive TY := fun e α hα =>
        thetaPotentialCurrent_full_positive θY.val (fun y => u (π y)) huY e α hα
      (globalACtopMeasure TY hTY).map π = globalACtopMeasure TX hTX := by
  let : CompactSpace Y := compactSpace_of_isAnalyticModification hπ
  let θY := ClosedRealOneOneForm.pullback hπ.1 θ
  obtain ⟨huY, E, s, hEc, hEa, hEi, hprea, hprei, hpairs⟩ :=
    exists_original_theta_current_transport hπ θ hu
  let TX := thetaPotentialCurrent θ.val u hu
  let TY := thetaPotentialCurrent θY.val (fun y => u (π y)) huY
  let hTX : IsFullPositive TX := fun e α hα => thetaPotentialCurrent_full_positive θ.val u hu e α hα
  let hTY : IsFullPositive TY := fun e α hα =>
    thetaPotentialCurrent_full_positive θY.val (fun y => u (π y)) huY e α hα
  let μX := globalACtopMeasure TX hTX
  let μY := globalACtopMeasure TY hTY
  let ν := μY.map π
  obtain ⟨D, Z, s0, _hDc, hDa, hDi, hZc, hZa, hZi, hpre, _hs0, _hright, hleft⟩ := hπ.2.2
  let O : Set X := (E ∪ Z)ᶜ
  have hXnull : μX (E ∪ Z) = 0 :=
    measure_union_null
      (globalACtopMeasure_doesNotCharge_pluripolar TX hTX E
        (ModificationMassInvariance.manifoldLocallyPluripolar_of_isComplexAnalyticSubset hEa hEi))
      (globalACtopMeasure_doesNotCharge_pluripolar TX hTX Z
        (ModificationMassInvariance.manifoldLocallyPluripolar_of_isComplexAnalyticSubset hZa hZi))
  have hYnull : μY (π ⁻¹' (E ∪ Z)) = 0 := by
    rw [preimage_union]
    apply measure_union_null
    · exact globalACtopMeasure_doesNotCharge_pluripolar TY hTY (π ⁻¹' E)
        (ModificationMassInvariance.manifoldLocallyPluripolar_of_isComplexAnalyticSubset hprea hprei)
    · rw [hpre]
      exact globalACtopMeasure_doesNotCharge_pluripolar TY hTY D
        (ModificationMassInvariance.manifoldLocallyPluripolar_of_isComplexAnalyticSubset hDa hDi)
  have hνnull : ν (E ∪ Z) = 0 := by
    rw [Measure.map_apply hπ.1.continuous.measurable (hEc.union hZc).measurableSet]
    exact hYnull
  have hinj (q q' : Y) (heq : π q = π q') (hq : π q ∉ Z) : q = q' := by
    have hqD : q ∉ D := by simpa only [← hpre, mem_preimage] using hq
    have hq'D : q' ∉ D := by simpa only [← hpre, mem_preimage, ← heq] using hq
    exact (hleft q hqD).symm.trans ((congrArg s0 heq).trans (hleft q' hq'D))
  refine ⟨huY, ?_⟩
  apply restrict_eq_of_local_on_open (O := O)
    (by simpa only [O, compl_compl] using hνnull)
    (by simpa only [O, compl_compl] using hXnull)
  intro x
  obtain ⟨y, hy⟩ := surjective_of_isAnalyticModification hπ x.val
  let e := complexChartAt (n := m + 1) y
  let d := complexChartAt (n := m + 1) x.val
  have hxE : x.val ∉ E := fun hx => x.property (Or.inl hx)
  have hxZ : x.val ∉ Z := fun hx => x.property (Or.inr hx)
  have hye : y ∈ e.val.source := mem_complexChartAt_source y
  have hyd : π y ∈ d.val.source := by rw [hy]; exact mem_complexChartAt_source x.val
  obtain ⟨A, B, hAe, hBd, hyA, hAdom, hBoff, hpair, _hcur, _hform, hcov⟩ :=
    hpairs y (by rwa [hy]) e d hye hyd
  let U : Set X := (d.val.source ∩ d.val ⁻¹' (B : Set (ComplexModel (m + 1)))) ∩ Zᶜ
  have hU : IsOpen U := (d.val.isOpen_inter_preimage B.isOpen).inter hZc.isOpen_compl
  have hxU : x.val ∈ U := by
    refine ⟨⟨mem_complexChartAt_source x.val, ?_⟩, hxZ⟩
    have hb := hpair.mapsTo hyA
    change d.val (π (e.val.symm (e.val y))) ∈ B at hb
    rw [e.val.left_inv hye, hy] at hb
    exact hb
  have hUO : U ⊆ O := by
    intro q hq hqO
    rcases hqO with hqE | hqZ
    · have hb := hBoff (d.val q) hq.1.2
      rw [d.val.left_inv hq.1.1] at hb
      exact hb hqE
    · exact hq.2 hqZ
  refine ⟨U, hU, hxU, hUO, ?_⟩
  exact local_pushforward_restrict_eq hπ.1.continuous hZc hinj e d A B hAe hBd hAdom hpair
    μY μX (acTopMeasure (isPositive_chartSpanCurrent TY hTY e))
    (acTopMeasure (isPositive_chartSpanCurrent TX hTX d))
    (global_inter_chart TY hTY e) (global_inter_chart TX hTX d) hcov

end SGPT.Foundations.Analysis.Pending.ThetaCurrentModificationGlobalACTransport
