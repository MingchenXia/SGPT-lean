import SGPT.PSH.SourceTestCurveLegendreGeodesic

/-! # The analytic inverse preceding the original binary test-curve join

The actual maximum of the assigned-initial Legendre rays is constructed first.
Its positive-time inverse is not silently identified with the literal LCE.
No original join environment is covered until that separate bridge is proved.
-/
set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.VariableComplexAtlas
open Set Filter Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)}

/-- Maximum of the two actual assigned-initial Legendre rays, retaining
both actual source limit functions at time zero. -/
def sourceTestCurveMaxLegendreRay (Γ Δ : SourceTestCurvePredata θ) : SourceRayFamily M :=
  fun t x => max (sourceTestCurveLegendreRay Γ t x) (sourceTestCurveLegendreRay Δ t x)

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]

/-- The maximum ray has the exact finite linear cutoff bound at ALL actual
nonnegative times, including its genuine assigned initial value. -/
theorem sourceTestCurveMaxLegendreRay_le_cutoff (omega : KahlerBackground n M)
    (Γ Δ : SourceTestCurvePredata θ) (t : Ici (0 : ℝ)) :
    sourceTestCurveMaxLegendreRay Γ Δ t ≤
      fun _ => ((t.1 * max Γ.max Δ.max : ℝ) : EReal) := by
  intro x
  apply max_le
  · rw [Γ.legendreRay_eq_regularized omega]
    exact (Γ.regularizedLegendre_le_cutoff t.2 x).trans
      (EReal.coe_le_coe (mul_le_mul_of_nonneg_left (le_max_left _ _) t.2))
  · rw [Δ.legendreRay_eq_regularized omega]
    exact (Δ.regularizedLegendre_le_cutoff t.2 x).trans
      (EReal.coe_le_coe (mul_le_mul_of_nonneg_left (le_max_right _ _) t.2))

/-- A genuine maximum subgeodesic ray: EVERY original closed segment and
both actual global L1 endpoint limits are produced by the existing mother. -/
theorem sourceTestCurveMaxLegendreRay_isSubgeodesic (omega : KahlerBackground n M)
    (Γ Δ : SourceTestCurvePredata θ) :
    SourceIsSubgeodesicRay omega θ (sourceTestCurveMaxLegendreRay Γ Δ) := by
  let R : Bool → SourceRayFamily M := fun i =>
    if i = true then sourceTestCurveLegendreRay Δ else sourceTestCurveLegendreRay Γ
  have hR (i : Bool) : SourceIsSubgeodesicRay omega θ (R i) := by
    cases i
    · exact (Γ.legendreRay_emanates omega).1
    · exact (Δ.legendreRay_emanates omega).1
  have hSup (t : ℝ) : uscSup (fun i => sourceRayExtension (R i) t) =
      sourceRayExtension (sourceTestCurveMaxLegendreRay Γ Δ) t := by
    have hu (i : Bool) : UpperSemicontinuousOn (sourceRayExtension (R i) t) univ := by
      have hn := (isThetaPSH_iff_nativeThetaPotential θ _).mp
        ((hR i).thetaPSH ⟨max t 0, le_max_right t 0⟩)
      exact hn.1.quasiPlurisubharmonic.upperSemicontinuous.upperSemicontinuousOn univ
    funext x
    rw [uscSup_eq_iSup_finite isOpen_univ hu (mem_univ x)]
    simp [iSup_bool_eq, R, sourceRayExtension, sourceTestCurveMaxLegendreRay, max_comm]
  have hbound (t : ℝ) (ht : 0 ≤ t) (i : Bool) (x : M) :
      sourceRayExtension (R i) t x ≤ ((t * max Γ.max Δ.max : ℝ) : EReal) := by
    have hle : sourceRayExtension (R i) t x ≤
        sourceRayExtension (sourceTestCurveMaxLegendreRay Γ Δ) t x := by
      cases i
      · exact le_max_left _ _
      · exact le_max_right _ _
    apply hle.trans
    rw [sourceRayExtension_nonneg _ t ht]
    exact sourceTestCurveMaxLegendreRay_le_cutoff omega Γ Δ ⟨t, ht⟩ x
  intro a b ha hab
  have hs (i : Bool) := (hR i a b ha hab).2
  have hp := sourceSubgeodesic_uscSup omega hs
    ⟨a * max Γ.max Δ.max, hbound a ha⟩
    ⟨b * max Γ.max Δ.max, hbound b (ha.trans hab)⟩
  refine ⟨hab, ?_⟩
  simpa only [hSup] using hp

/-- A positive-time window of the SAME original literal inverse. -/
def sourcePositiveRayInverseWindow {X : Type*} (ℓ : SourceRayFamily X)
    (τ : ℝ) (j : ℕ) : X → EReal := fun x =>
  ⨅ t : Ioo (1 / ((j : ℝ)+2)) ((j : ℝ)+2),
    sourceRayExtension ℓ t.1 x - ((t.1*τ : ℝ) : EReal)

/-- Every inverse window has strictly positive left endpoint and length. -/
theorem sourcePositiveInverseWindow_pos (j : ℕ) :
    0 < 1 / ((j : ℝ)+2) ∧ 1 / ((j : ℝ)+2) < (j : ℝ)+2 := by
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hp : (0 : ℝ) < (j : ℝ)+2 := by positivity
  refine ⟨one_div_pos.mpr hp, (div_lt_iff₀ hp).mpr ?_⟩
  nlinarith

/-- The actual positive-time windows are increasing by inclusion. -/
theorem sourcePositiveInverseWindow_mono {i j : ℕ} (hij : i ≤ j) :
    Ioo (1 / ((i : ℝ)+2)) ((i : ℝ)+2) ⊆
      Ioo (1 / ((j : ℝ)+2)) ((j : ℝ)+2) := by
  have hcast : (i : ℝ) ≤ j := by exact_mod_cast hij
  have hl : 1 / ((j : ℝ)+2) ≤ 1 / ((i : ℝ)+2) :=
    one_div_le_one_div_of_le (by positivity) (by linarith)
  exact fun _ ht => ⟨hl.trans_lt ht.1, ht.2.trans_le (by linarith)⟩

/-- Every actual positive real time occurs in an inverse window. -/
theorem sourcePositiveInverseWindow_cover {t : ℝ} (ht : 0 < t) :
    ∃ j : ℕ, t ∈ Ioo (1 / ((j : ℝ)+2)) ((j : ℝ)+2) := by
  obtain ⟨j, hj⟩ := exists_nat_gt (max t (1/t))
  have htr : t < (j : ℝ)+2 := by linarith [le_max_left t (1/t)]
  have hir : 1/t < (j : ℝ)+2 := by linarith [le_max_right t (1/t)]
  exact ⟨j, (one_div_lt (by positivity) ht).mpr hir, htr⟩

/-- Window infima decrease pointwise, without an analytic assumption. -/
theorem sourcePositiveRayInverseWindow_antitone {X : Type*} (ℓ : SourceRayFamily X)
    (τ : ℝ) (x : X) : Antitone (fun j => sourcePositiveRayInverseWindow ℓ τ j x) := by
  intro i j hij
  apply le_iInf
  intro t
  exact iInf_le (fun s : Ioo (1 / ((j : ℝ)+2)) ((j : ℝ)+2) =>
    sourceRayExtension ℓ s.1 x - ((s.1*τ : ℝ) : EReal))
      ⟨t.1, sourcePositiveInverseWindow_mono hij t.2⟩

/-- The literal sequence of windows exhausts the ORIGINAL all-positive-time
inverse, retaining every extended-real value. -/
theorem sourcePositiveRayInverseWindow_exhaust {X : Type*} (ℓ : SourceRayFamily X)
    (τ : ℝ) : (fun x => ⨅ j : ℕ, sourcePositiveRayInverseWindow ℓ τ j x) =
      sourcePositiveRayInverse ℓ τ := by
  funext x
  apply le_antisymm
  · apply le_iInf
    intro t
    obtain ⟨j, hj⟩ := sourcePositiveInverseWindow_cover t.2
    exact (iInf_le (fun j => sourcePositiveRayInverseWindow ℓ τ j x) j).trans
      (iInf_le (fun s : Ioo (1 / ((j : ℝ)+2)) ((j : ℝ)+2) =>
        sourceRayExtension ℓ s.1 x - ((s.1*τ : ℝ) : EReal)) ⟨t.1,hj⟩)
  · apply le_iInf
    intro j
    apply le_iInf
    intro t
    exact iInf_le (fun s : Ioi (0 : ℝ) =>
      sourceRayExtension ℓ s.1 x - ((s.1*τ : ℝ) : EReal))
        ⟨t.1, (sourcePositiveInverseWindow_pos j).1.trans t.2.1⟩

/-- Actual fixed-strip Kiselman supplies each finite inverse window from
only the genuine original subgeodesic-ray condition. -/
theorem sourcePositiveRayInverseWindow_thetaPSH {omega : KahlerBackground n M}
    {ℓ : SourceRayFamily M} (h : SourceIsSubgeodesicRay omega θ ℓ) (τ : ℝ) (j : ℕ) :
    (ofFixedModel n M).IsThetaPSH θ (sourcePositiveRayInverseWindow ℓ τ j) :=
  ((h _ _ (sourcePositiveInverseWindow_pos j).1.le
    (sourcePositiveInverseWindow_pos j).2.le).isThetaPSH_timeInf_sub_affine
      (sourcePositiveInverseWindow_pos j).2 τ)

/-- A genuine ordinary fixedpoint lower potential manufactures noncollapse
of the actual all-positive-time inverse; output PSH is a conclusion. -/
theorem sourcePositiveRayInverse_thetaPSH_of_fixedPointLowerBound
    {omega : KahlerBackground n M} {ℓ : SourceRayFamily M}
    (h : SourceIsSubgeodesicRay omega θ ℓ) {u : M → EReal}
    (hu : (ofFixedModel n M).IsThetaPSH θ u)
    (hfix : sourceSingularityEnvelope θ u = u) (τ : ℝ)
    (hlower : ∀ t : Ioi (0 : ℝ), u ≤
      fun x => sourceRayExtension ℓ t.1 x - ((t.1*τ : ℝ) : EReal)) :
    (ofFixedModel n M).IsThetaPSH θ (sourcePositiveRayInverse ℓ τ) := by
  have hzero := sourceOrdinaryFixedPoint_globalSup_zero hu hfix
  have hl (j : ℕ) : u ≤ sourcePositiveRayInverseWindow ℓ τ j := by
    intro x
    apply le_iInf
    intro t
    exact hlower ⟨t.1, (sourcePositiveInverseWindow_pos j).1.trans t.2.1⟩ x
  have hh := (SGPT.PSH.isThetaPshPotential_iInf_of_compact_antitone_iSup_lower_bound
    (fun j => (isThetaPSH_iff_nativeThetaPotential θ _).mp
      (sourcePositiveRayInverseWindow_thetaPSH h τ j))
    (sourcePositiveRayInverseWindow_antitone ℓ τ) 0 (fun j => by
      change (0 : EReal) ≤ _
      rw [← hzero]
      exact iSup_mono (hl j))).1
  rw [sourcePositiveRayInverseWindow_exhaust] at hh
  exact (isThetaPSH_iff_nativeThetaPotential θ _).mpr hh

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M] in
/-- At every POSITIVE time the genuine assigned-initial maximum ray has the
literal maximum of raw transforms. No raw zero-time equality is asserted. -/
theorem sourceTestCurveMaxLegendreRay_positive (Γ Δ : SourceTestCurvePredata θ)
    {t : ℝ} (ht : 0 < t) :
    sourceRayExtension (sourceTestCurveMaxLegendreRay Γ Δ) t =
      fun x => max (sourceTestCurveRawLegendre Γ t x) (sourceTestCurveRawLegendre Δ t x) := by
  change (fun x => max
    (sourceTestCurveLegendreWithInitial Γ (sourceTestCurveLimit Γ) (max t 0) x)
    (sourceTestCurveLegendreWithInitial Δ (sourceTestCurveLimit Δ) (max t 0) x)) = _
  rw [max_eq_left ht.le]
  simp only [sourceTestCurveLegendreWithInitial, if_neg ht.ne']

omit [MeasurableSpace M] [BorelSpace M] in
/-- The actual all-positive-time inverse dominates the ENTIRE first input
extension, including the literal cutoff and bottom branches. -/
theorem sourceTestCurveMaxLegendreInverse_ge_left (Γ Δ : SourceTestCurvePredata θ)
    (τ : ℝ) : sourceTestCurveAt Γ τ ≤
      sourcePositiveRayInverse (sourceTestCurveMaxLegendreRay Γ Δ) τ := by
  intro x
  rw [Γ.at_eq_iInf_positive_rawLegendre τ x]
  apply le_iInf
  intro t
  apply (iInf_le (fun s : Ioi (0 : ℝ) =>
    sourceTestCurveRawLegendre Γ s.1 x - ((s.1*τ : ℝ) : EReal)) t).trans
  rw [sourceTestCurveMaxLegendreRay_positive Γ Δ t.2]
  exact EReal.sub_le_sub (le_max_left _ _) le_rfl

omit [MeasurableSpace M] [BorelSpace M] in
/-- The same exact manufactured lower comparison for the second input. -/
theorem sourceTestCurveMaxLegendreInverse_ge_right (Γ Δ : SourceTestCurvePredata θ)
    (τ : ℝ) : sourceTestCurveAt Δ τ ≤
      sourcePositiveRayInverse (sourceTestCurveMaxLegendreRay Γ Δ) τ := by
  intro x
  rw [Δ.at_eq_iInf_positive_rawLegendre τ x]
  apply le_iInf
  intro t
  apply (iInf_le (fun s : Ioi (0 : ℝ) =>
    sourceTestCurveRawLegendre Δ s.1 x - ((s.1*τ : ℝ) : EReal)) t).trans
  rw [sourceTestCurveMaxLegendreRay_positive Γ Δ t.2]
  exact EReal.sub_le_sub (le_max_right _ _) le_rfl

/-- Genuine PSH of the actual maximum-ray inverse is manufactured from the
original fields, even at the common cutoff where mass may be zero.
The literal LCE identity and join modelness are NOT premises or conclusions. -/
theorem sourceTestCurveMaxLegendreInverse_thetaPSH (omega : KahlerBackground n M)
    (Γ Δ : SourceTestCurvePredata θ) {τ : ℝ} (hτ : τ ≤ max Γ.max Δ.max) :
    (ofFixedModel n M).IsThetaPSH θ
      (sourcePositiveRayInverse (sourceTestCurveMaxLegendreRay Γ Δ) τ) := by
  have hfixed (A : SourceTestCurvePredata θ) (ha : τ ≤ A.max) :
      sourceSingularityEnvelope θ (sourceTestCurveAt A τ) = sourceTestCurveAt A τ := by
    rcases ha.eq_or_lt with heq | hlt
    · rw [heq, sourceTestCurveAt_eq_max]
      exact A.cutoff_fixedPoint
    · rw [sourceTestCurveAt_of_lt A hlt]
      exact A.fixedPoint ⟨τ,hlt⟩
  have hR := sourceTestCurveMaxLegendreRay_isSubgeodesic omega Γ Δ
  rcases le_max_iff.mp hτ with hΓ | hΔ
  · apply sourcePositiveRayInverse_thetaPSH_of_fixedPointLowerBound hR
      ((source_test_curve_extension_whole Γ).2.2.2 τ hΓ) (hfixed Γ hΓ) τ
    intro t x
    exact (sourceTestCurveMaxLegendreInverse_ge_left Γ Δ τ x).trans
      (iInf_le (fun s : Ioi (0 : ℝ) =>
        sourceRayExtension (sourceTestCurveMaxLegendreRay Γ Δ) s.1 x -
          ((s.1*τ : ℝ) : EReal)) t)
  · apply sourcePositiveRayInverse_thetaPSH_of_fixedPointLowerBound hR
      ((source_test_curve_extension_whole Δ).2.2.2 τ hΔ) (hfixed Δ hΔ) τ
    intro t x
    exact (sourceTestCurveMaxLegendreInverse_ge_right Γ Δ τ x).trans
      (iInf_le (fun s : Ioi (0 : ℝ) =>
        sourceRayExtension (sourceTestCurveMaxLegendreRay Γ Δ) s.1 x -
          ((s.1*τ : ℝ) : EReal)) t)

/-- Strictly below the actual maximum cutoff, the analytic inverse has
positive ACTUAL non-pluripolar mass, manufactured from a genuine input slice.
No positive mass or model property of the output is assumed. -/
theorem sourceTestCurveMaxLegendreInverse_mass_positive (omega : KahlerBackground n M)
    (Γ Δ : SourceTestCurve θ) {τ : ℝ} (hτ : τ < max Γ.max Δ.max) :
    0 < sourcePotentialNonPluripolarMeasure θ
      (sourcePositiveRayInverse
        (sourceTestCurveMaxLegendreRay Γ.toSourceTestCurvePredata Δ.toSourceTestCurvePredata) τ)
      (sourceTestCurveMaxLegendreInverse_thetaPSH omega Γ.toSourceTestCurvePredata
        Δ.toSourceTestCurvePredata hτ.le) univ := by
  have hψ := sourceTestCurveMaxLegendreInverse_thetaPSH omega Γ.toSourceTestCurvePredata
    Δ.toSourceTestCurvePredata hτ.le
  rcases lt_max_iff.mp hτ with hΓ | hΔ
  · have hl := sourceTestCurveMaxLegendreInverse_ge_left Γ.toSourceTestCurvePredata
      Δ.toSourceTestCurvePredata τ
    rw [sourceTestCurveAt_of_lt _ hΓ] at hl
    exact (Γ.mass_positive omega ⟨τ,hΓ⟩).trans_le
      (sourcePotentialNonPluripolarMass_mono omega (Γ.thetaPSH ⟨τ,hΓ⟩) hψ
        (MoreSingularOn.of_le (fun x _ => hl x)))
  · have hl := sourceTestCurveMaxLegendreInverse_ge_right Γ.toSourceTestCurvePredata
      Δ.toSourceTestCurvePredata τ
    rw [sourceTestCurveAt_of_lt _ hΔ] at hl
    exact (Δ.mass_positive omega ⟨τ,hΔ⟩).trans_le
      (sourcePotentialNonPluripolarMass_mono omega (Δ.thetaPSH ⟨τ,hΔ⟩) hψ
        (MoreSingularOn.of_le (fun x _ => hl x)))

end SGPT.PSH.VariableComplexAtlas
