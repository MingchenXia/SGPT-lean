import SGPT.Trace.BertiniUniversalLocalMass

/-! Actual compact original residue mass, from internally manufactured
finite-mass neighborhoods and actual compact finite subcover. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Trace.BertiniUniversal
open Bundle Set Filter Metric MeasureTheory
open scoped Topology Manifold ContDiff ENNReal BigOperators
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.ProductComplexManifold
open SGPT.Foundations.Analysis.Pending.ChartwiseGlobalL1
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace
open SGPT.Trace.Bertini
open SGPT.Bergman.QuantizationDraft SGPT.Bergman.TensorDictionaryDraft

variable {k d : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (d + 1)) X] [IsComplexManifold (d + 1) X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X]
  (p : ContMDiffMap 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel (k + 1)) X (ComplexProjectiveSpace (k + 1)) ∞)
  {φ : X → EReal} (c : SliceChart (d + 1) (p : X → ComplexProjectiveSpace (k + 1)) φ)

theorem originalResidue_multiplier_compact_integral_lt_top
    (a : X) (ha : c.e = complexChartAt (n := d + 1) a)
    (L : HermitianHolomorphicLineBundle.{0,0} (d + 1) X)
    {K : Set (ComplexModel (k + 1 + d))} (hK : IsCompact K) (hKU : K ⊆ originalQSourceDomain p c)
    (hφ : IsGlobalQuasiPshPotential (n := d + 1) φ)
    (T : nativeMultiplierSections (OriginalAmbientPhysicalBundle p L) φ)
    (μ : Measure X) (hμ : IsSmoothPositiveVolume (n := d + 1) μ) :
    (∫⁻ z in K, originalMemberResidueSourceDensity p c L T.val (fun x => multiplierWeight 1 (φ x)) z) < ⊤ := by
  classical
  let f := originalMemberResidueSourceDensity p c L T.val (fun x => multiplierWeight 1 (φ x))
  have hloc (z : K) : ∃ W : Set (ComplexModel (k + 1 + d)), IsOpen W ∧ z.val ∈ W ∧
      (∫⁻ y in W, f y) < ⊤ := by
    let q := originalQSourcePair p c ⟨z.val,hKU z.property⟩
    obtain ⟨W,hW,hz,hsub,hfin⟩ := exists_originalResidue_multiplier_finite_neighborhood p c a ha L q
    have heq : prodModelEquiv (k + 1) d (q.1.val,q.2.val) = z.val := (prodModelEquiv (k + 1) d).apply_symm_apply z.val
    rw [heq] at hz
    exact ⟨W,hW,hz,hfin hφ T μ hμ⟩
  choose W hW hzW hfin using hloc
  obtain ⟨t,ht⟩ := hK.elim_finite_subcover W hW (fun z hz => mem_iUnion.mpr ⟨⟨z,hz⟩,hzW ⟨z,hz⟩⟩)
  have hsub : K ⊆ ⋃ z : t, W z.val := by
    intro z hz
    obtain ⟨u,hu,hzu⟩ := mem_iUnion₂.mp (ht hz)
    exact mem_iUnion.mpr ⟨⟨u,hu⟩,hzu⟩
  have hsum : (∑ z : t, ∫⁻ y in W z.val, f y) < ⊤ :=
    ENNReal.sum_lt_top.mpr (fun z _ => hfin z.val)
  have hunion : (∫⁻ y in ⋃ z : t, W z.val, f y) ≤ ∑ z : t, ∫⁻ y in W z.val, f y := by
    simpa only [tsum_fintype] using lintegral_iUnion_le (μ := (volume : Measure (ComplexModel (k + 1 + d))))
      (fun z : t => W z.val) f
  exact ((lintegral_mono' (Measure.restrict_mono hsub le_rfl) le_rfl).trans hunion).trans_lt hsum

end SGPT.Trace.BertiniUniversal
