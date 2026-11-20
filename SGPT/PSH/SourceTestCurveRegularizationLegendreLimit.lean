import SGPT.PSH.SourceTestCurveRegularizationEnergy
import SGPT.PSH.SourceTestCurveLegendrePSH
import SGPT.Convex.FamilyOperations
import SGPT.Convex.HalfLine

set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.VariableComplexAtlas
open Set Filter Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]
  {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)}
  {φ : M → EReal} {hφ : SourceModelPotential θ φ}

private theorem regularization_negative_at (omega : KahlerBackground n M)
    (Γ : SourceTestCurve θ) (hΓ : Γ ∈ SourceTestCurvesBased θ φ hφ)
    (hmax : Γ.max = 0) (k : ℕ) {r : ℝ} (hr : r < 0) (x : M) :
    sourceTestCurveAt (sourceTestCurveRegularizationSequence omega Γ hΓ hmax k).toSourceTestCurvePredata r x =
      sourceTestCurveRegularizationFamily Γ φ (sourceRegularizationParameter k) r x := by
  rw [sourceTestCurveAt_of_lt _ (show r <
    (sourceTestCurveRegularizationSequence omega Γ hΓ hmax k).max from hr)]
  rfl

/-- Literal entire-extension infimum, including the actual cutoff. -/
theorem sourceTestCurveRegularizationSequence_at_iInf (omega : KahlerBackground n M)
    (Γ : SourceTestCurve θ) (hΓ : Γ ∈ SourceTestCurvesBased θ φ hφ)
    (hmax : Γ.max = 0) (r : ℝ) (x : M) :
    (⨅ k, sourceTestCurveAt
      (sourceTestCurveRegularizationSequence omega Γ hΓ hmax k).toSourceTestCurvePredata r x) =
      sourceTestCurveAt Γ.toSourceTestCurvePredata r x := by
  let G := sourceTestCurveRegularizationSequence omega Γ hΓ hmax
  have hneg {s : ℝ} (hs : s < 0) :
      (⨅ k, sourceTestCurveAt (G k).toSourceTestCurvePredata s x) =
      sourceTestCurveAt Γ.toSourceTestCurvePredata s x := by
    change (⨅ k, sourceTestCurveAt (sourceTestCurveRegularizationSequence omega Γ hΓ hmax k).toSourceTestCurvePredata s x) = _
    simp_rw [regularization_negative_at omega Γ hΓ hmax _ hs x]
    exact congrFun (sourceTestCurveRegularizationFamily_iInf omega Γ hΓ hmax hs) x
  by_cases hr : r < 0
  · exact hneg hr
  by_cases hz : r = 0
  · subst r
    calc
      _ = ⨅ k, ⨅ s : Iio (0 : ℝ), sourceTestCurveAt (G k).toSourceTestCurvePredata s.1 x :=
        iInf_congr fun k => (G k).toSourceTestCurvePredata.at_eq_earlierInf x 0
      _ = ⨅ s : Iio (0 : ℝ), ⨅ k, sourceTestCurveAt (G k).toSourceTestCurvePredata s.1 x := iInf_comm
      _ = ⨅ s : Iio (0 : ℝ), sourceTestCurveAt Γ.toSourceTestCurvePredata s.1 x :=
        iInf_congr fun s => hneg s.2
      _ = _ := (Γ.toSourceTestCurvePredata.at_eq_earlierInf x 0).symm
  · have hp : 0 < r := lt_of_le_of_ne (le_of_not_gt hr) (Ne.symm hz)
    have hb (k : ℕ) : sourceTestCurveAt (G k).toSourceTestCurvePredata r x = ⊥ := by
      rw [sourceTestCurveAt_of_gt _ (show (G k).max < r from hp)]
      rfl
    change (⨅ k, sourceTestCurveAt (G k).toSourceTestCurvePredata r x) = _
    simp [hb, sourceTestCurveAt_of_gt Γ.toSourceTestCurvePredata (by simpa only [hmax] using hp)]

/-- Entire-extension order retains the original cutoff and super-cutoff branch. -/
theorem sourceTestCurveRegularizationSequence_at_antitone (omega : KahlerBackground n M)
    (Γ : SourceTestCurve θ) (hΓ : Γ ∈ SourceTestCurvesBased θ φ hφ)
    (hmax : Γ.max = 0) (r : ℝ) (x : M) :
    Antitone (fun k => sourceTestCurveAt
      (sourceTestCurveRegularizationSequence omega Γ hΓ hmax k).toSourceTestCurvePredata r x) := by
  let G := sourceTestCurveRegularizationSequence omega Γ hΓ hmax
  have hneg {s : ℝ} (hs : s < 0) :
      Antitone (fun k => sourceTestCurveAt (G k).toSourceTestCurvePredata s x) := by
    intro i j hij
    change sourceTestCurveAt (sourceTestCurveRegularizationSequence omega Γ hΓ hmax j).toSourceTestCurvePredata s x ≤
      sourceTestCurveAt (sourceTestCurveRegularizationSequence omega Γ hΓ hmax i).toSourceTestCurvePredata s x
    rw [regularization_negative_at omega Γ hΓ hmax j hs x,
      regularization_negative_at omega Γ hΓ hmax i hs x]
    exact sourceTestCurveRegularizationFamily_antitone_sequence Γ hΓ hs hij x
  by_cases hr : r < 0
  · exact hneg hr
  by_cases hz : r = 0
  · subst r
    intro i j hij
    change sourceTestCurveAt (G j).toSourceTestCurvePredata 0 x ≤ sourceTestCurveAt (G i).toSourceTestCurvePredata 0 x
    rw [(G j).toSourceTestCurvePredata.at_eq_earlierInf x 0,
      (G i).toSourceTestCurvePredata.at_eq_earlierInf x 0]
    exact iInf_mono fun s => hneg s.2 hij
  · have hp : 0 < r := lt_of_le_of_ne (le_of_not_gt hr) (Ne.symm hz)
    intro i j hij
    change sourceTestCurveAt (G j).toSourceTestCurvePredata r x ≤ sourceTestCurveAt (G i).toSourceTestCurvePredata r x
    simp only [sourceTestCurveAt_of_gt _ (show (G j).max < r from hp),
      sourceTestCurveAt_of_gt _ (show (G i).max < r from hp), Pi.bot_apply, le_refl]

/-- Every actual raw transform decreases, on the entire real time line. -/
theorem sourceTestCurveRegularizationSequence_rawLegendre_antitone (omega : KahlerBackground n M)
    (Γ : SourceTestCurve θ) (hΓ : Γ ∈ SourceTestCurvesBased θ φ hφ)
    (hmax : Γ.max = 0) (t : ℝ) :
    Antitone (fun k => sourceTestCurveRawLegendre
      (sourceTestCurveRegularizationSequence omega Γ hΓ hmax k).toSourceTestCurvePredata t) := by
  intro i j hij x
  apply iSup_mono
  intro r
  exact add_le_add le_rfl (sourceTestCurveRegularizationSequence_at_antitone omega Γ hΓ hmax r x hij)

private theorem sub_real_iInf (b : ℕ → EReal) (c : ℝ) :
    (⨅ k, b k) - (c : EReal) = ⨅ k, b k - (c : EReal) := by
  let e : EReal ≃o EReal := {
    toFun := fun z => ((-c : ℝ) : EReal) + z
    invFun := fun z => (c : EReal) + z
    left_inv := by intro z; cases z using EReal.rec <;> simp [-EReal.coe_neg, ← EReal.coe_add]
    right_inv := by intro z; cases z using EReal.rec <;> simp [-EReal.coe_neg, ← EReal.coe_add]
    map_rel_iff' := (EReal.addLECancellable_coe (-c)).add_le_add_iff_left }
  have hh := e.map_iInf b
  change ((-c : ℝ) : EReal) + (⨅ k, b k) = ⨅ k, ((-c : ℝ) : EReal) + b k at hh
  simpa only [sub_eq_add_neg, ← EReal.coe_neg, add_comm] using hh

/-- Convexity of the literal decreasing positive-time infimum is produced. -/
theorem sourceTestCurveRegularizationSequence_rawInf_positiveEpigraph (omega : KahlerBackground n M)
    (Γ : SourceTestCurve θ) (hΓ : Γ ∈ SourceTestCurvesBased θ φ hφ)
    (hmax : Γ.max = 0) (x : M) :
    Convex ℝ {p : ℝ × ℝ | 0 < p.1 ∧
      (⨅ k, sourceTestCurveRawLegendre
        (sourceTestCurveRegularizationSequence omega Γ hΓ hmax k).toSourceTestCurvePredata p.1 x) ≤ (p.2 : EReal)} := by
  let G := sourceTestCurveRegularizationSequence omega Γ hΓ hmax
  let f := fun k => SGPT.Convex.positiveExtension
    (fun t => sourceTestCurveRawLegendre (G k).toSourceTestCurvePredata t x)
  have hf (k : ℕ) : SGPT.Convex.IsConvex (f k) :=
    SGPT.Convex.isConvex_positiveExtension ((G k).toSourceTestCurvePredata.rawLegendre_positiveEpigraph_convex x)
  have ha : Antitone f := by
    intro i j hij t
    by_cases ht : 0 < t
    · simp only [f, SGPT.Convex.positiveExtension, if_pos ht]
      exact sourceTestCurveRegularizationSequence_rawLegendre_antitone omega Γ hΓ hmax t hij x
    · simp only [f, SGPT.Convex.positiveExtension, if_neg ht, le_refl]
  have hc := SGPT.Convex.isConvex_iInf_of_antitone hf ha
  have heq : (fun t => ⨅ k, f k t) = SGPT.Convex.positiveExtension
      (fun t => ⨅ k, sourceTestCurveRawLegendre (G k).toSourceTestCurvePredata t x) := by
    funext t
    by_cases ht : 0 < t <;> simp [f, SGPT.Convex.positiveExtension, ht]
  rw [heq] at hc
  simpa only [SGPT.Convex.IsConvex, SGPT.Convex.epigraph_positiveExtension] using hc

/-- Literal positive raw Legendre infimum equals the ORIGINAL raw function. -/
theorem sourceTestCurveRegularizationSequence_rawLegendre_iInf (omega : KahlerBackground n M)
    (Γ : SourceTestCurve θ) (hΓ : Γ ∈ SourceTestCurvesBased θ φ hφ)
    (hmax : Γ.max = 0) {t : ℝ} (ht : 0 < t) (x : M) :
    (⨅ k, sourceTestCurveRawLegendre
      (sourceTestCurveRegularizationSequence omega Γ hΓ hmax k).toSourceTestCurvePredata t x) =
      sourceTestCurveRawLegendre Γ.toSourceTestCurvePredata t x := by
  let G := sourceTestCurveRegularizationSequence omega Γ hΓ hmax
  let F := fun s => ⨅ k, sourceTestCurveRawLegendre (G k).toSourceTestCurvePredata s x
  have hinv (r : ℝ) : sourceTestCurveAt Γ.toSourceTestCurvePredata r x =
      ⨅ s : Ioi (0 : ℝ), F s.1 - ((s.1 * r : ℝ) : EReal) := by
    calc
      _ = ⨅ k, sourceTestCurveAt (G k).toSourceTestCurvePredata r x :=
        (sourceTestCurveRegularizationSequence_at_iInf omega Γ hΓ hmax r x).symm
      _ = ⨅ k, ⨅ s : Ioi (0 : ℝ), sourceTestCurveRawLegendre (G k).toSourceTestCurvePredata s.1 x -
          ((s.1 * r : ℝ) : EReal) := iInf_congr fun k =>
        (G k).toSourceTestCurvePredata.at_eq_iInf_positive_rawLegendre r x
      _ = ⨅ s : Ioi (0 : ℝ), ⨅ k, sourceTestCurveRawLegendre (G k).toSourceTestCurvePredata s.1 x -
          ((s.1 * r : ℝ) : EReal) := iInf_comm
      _ = _ := iInf_congr fun s => (sub_real_iInf _ _).symm
  have hhalf (r : ℝ) : SGPT.Convex.halfLineConjugate F r =
      -sourceTestCurveAt Γ.toSourceTestCurvePredata r x := by
    rw [hinv]
    have hn : -(⨅ s : Ioi (0 : ℝ), F s.1 - ((s.1 * r : ℝ) : EReal)) =
        ⨆ s : Ioi (0 : ℝ), -(F s.1 - ((s.1 * r : ℝ) : EReal)) := map_iInf EReal.negOrderIso _
    rw [hn]
    have he (s : Ioi (0 : ℝ)) : -(F s.1 - ((s.1 * r : ℝ) : EReal)) =
        ((s.1 * r : ℝ) : EReal) - F s.1 := by
      rw [EReal.neg_sub (Or.inr (EReal.coe_ne_bot _)) (Or.inr (EReal.coe_ne_top _))]
      simp only [sub_eq_add_neg, add_comm]
    simp_rw [he]
    simp only [SGPT.Convex.halfLineConjugate, iSup_subtype, mem_Ioi]
  have hfinite (s : ℝ) (hs : 0 < s) : F s < ⊤ := by
    have h0 := (G 0).toSourceTestCurvePredata.rawLegendre_le_cutoff hs.le x
    exact (iInf_le (fun k => sourceTestCurveRawLegendre (G k).toSourceTestCurvePredata s x) 0).trans_lt
      (h0.trans_lt (EReal.coe_lt_top _))
  have hi := SGPT.Convex.halfLineConjugate_inversion
    (sourceTestCurveRegularizationSequence_rawInf_positiveEpigraph omega Γ hΓ hmax x) hfinite ht
  change F t = _
  rw [← hi]
  unfold SGPT.Convex.conjugate sourceTestCurveRawLegendre
  apply iSup_congr
  intro r
  rw [hhalf]
  simp only [SGPT.Convex.scalarPairing, LinearMap.mul_apply', sub_eq_add_neg, neg_neg, mul_comm]

/-- Every point of the SAME actual raw transforms converges, including poles. -/
theorem sourceTestCurveRegularizationSequence_rawLegendre_tendsto (omega : KahlerBackground n M)
    (Γ : SourceTestCurve θ) (hΓ : Γ ∈ SourceTestCurvesBased θ φ hφ)
    (hmax : Γ.max = 0) {t : ℝ} (ht : 0 < t) (x : M) :
    Tendsto (fun k => sourceTestCurveRawLegendre
      (sourceTestCurveRegularizationSequence omega Γ hΓ hmax k).toSourceTestCurvePredata t x)
      atTop (𝓝 (sourceTestCurveRawLegendre Γ.toSourceTestCurvePredata t x)) := by
  have hh := tendsto_atTop_iInf (fun i j hij =>
    sourceTestCurveRegularizationSequence_rawLegendre_antitone omega Γ hΓ hmax t hij x)
  simpa only [sourceTestCurveRegularizationSequence_rawLegendre_iInf omega Γ hΓ hmax ht x] using hh

/-- ALL assigned times include the SAME actual initial model at zero. -/
theorem sourceTestCurveRegularizationSequence_assignedLegendre_iInf (omega : KahlerBackground n M)
    (Γ : SourceTestCurve θ) (hΓ : Γ ∈ SourceTestCurvesBased θ φ hφ)
    (hmax : Γ.max = 0) (t : Ici (0 : ℝ)) (x : M) :
    (⨅ k, sourceTestCurveLegendreRay
      (sourceTestCurveRegularizationSequence omega Γ hΓ hmax k).toSourceTestCurvePredata t x) =
      sourceTestCurveLegendreRay Γ.toSourceTestCurvePredata t x := by
  have hbased (k : ℕ) : sourceTestCurveLimit
      (sourceTestCurveRegularizationSequence omega Γ hΓ hmax k).toSourceTestCurvePredata = φ :=
    (sourceTestCurveRegularizationSequence_bounded omega Γ hΓ hmax k).1
  have hbase : sourceTestCurveLimit Γ.toSourceTestCurvePredata = φ := hΓ
  by_cases hz : t.1 = 0
  · simp only [sourceTestCurveLegendreRay, sourceTestCurveLegendreWithInitial, if_pos hz,
      hbased, hbase, iInf_const]
  · simpa only [sourceTestCurveLegendreRay, sourceTestCurveLegendreWithInitial, if_neg hz] using
      sourceTestCurveRegularizationSequence_rawLegendre_iInf omega Γ hΓ hmax
        (lt_of_le_of_ne t.2 (Ne.symm hz)) x

/-- Actual assigned-ray convergence includes time zero and every pole. -/
theorem sourceTestCurveRegularizationSequence_assignedLegendre_tendsto (omega : KahlerBackground n M)
    (Γ : SourceTestCurve θ) (hΓ : Γ ∈ SourceTestCurvesBased θ φ hφ)
    (hmax : Γ.max = 0) (t : Ici (0 : ℝ)) (x : M) :
    Tendsto (fun k => sourceTestCurveLegendreRay
      (sourceTestCurveRegularizationSequence omega Γ hΓ hmax k).toSourceTestCurvePredata t x)
      atTop (𝓝 (sourceTestCurveLegendreRay Γ.toSourceTestCurvePredata t x)) := by
  have hbased (k : ℕ) : sourceTestCurveLimit
      (sourceTestCurveRegularizationSequence omega Γ hΓ hmax k).toSourceTestCurvePredata = φ :=
    (sourceTestCurveRegularizationSequence_bounded omega Γ hΓ hmax k).1
  have hbase : sourceTestCurveLimit Γ.toSourceTestCurvePredata = φ := hΓ
  by_cases hz : t.1 = 0
  · simpa only [sourceTestCurveLegendreRay, sourceTestCurveLegendreWithInitial, if_pos hz,
      hbased, hbase] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => φ x) atTop (𝓝 (φ x)))
  · simpa only [sourceTestCurveLegendreRay, sourceTestCurveLegendreWithInitial, if_neg hz] using
      sourceTestCurveRegularizationSequence_rawLegendre_tendsto omega Γ hΓ hmax
        (lt_of_le_of_ne t.2 (Ne.symm hz)) x

end SGPT.PSH.VariableComplexAtlas
