import SGPT.Envelopes.LapClassKahlerClass
import SGPT.Envelopes.DNTRegQuasiPsh
import SGPT.Okounkov.TranscendentalVolIdCurve

/-!
# `thm:DNT23_C11bar` for big classes in complex dimension at most one

Lane DNT-BIG (blueprint `claude-dnt-big`, nodes `dnt-big:low-dim-kahler`,
`dnt-big:low-dim`).  Source `thm:DNT23_C11bar` (Di Nezza–Trapani): for a smooth closed real
`(1,1)`-form `θ` whose class is big and `f ∈ C^{1,1̄}(X)`,
`P_θ(f) ∈ C^{1,1̄}(X ∖ nK({θ}))`, and in particular `V_θ ∈ C^{1,1̄}(X ∖ nK({θ}))`.

The Kähler-class case is `SGPT.Envelopes.LapClass.sourceObstacleEnvelope_hasBoundedMetricLaplacianOn_of_kahlerClass`.
In complex dimension `n ≤ 1` every big class is a Kähler class:

* `n = 0`: every closed real `(1,1)`-form is a Kähler form (the positivity condition is vacuous).
* `n = 1`: a big class has positive volume, the volume of a class on a curve is
  `max(∫_X θ, 0)` (`sourceClassVolume_eq_ofReal_curveDegree`), and a class of positive degree
  contains a Kähler form (`exists_kahler_of_curveDegree_pos`, the `dd^c`-lemma on a curve, from
  Yau's theorem in dimension one).

Hence the source statement holds for every big class when `n ≤ 1`.

## Main results

* `exists_isKahler_add_ddc_of_isBigClass_of_dim_le_one`: for `n ≤ 1`, a big class `{θ}` contains
  the Kähler form `θ + dd^c ρ` for a chart-smooth `ρ`.
* `sourceObstacleEnvelope_hasBoundedMetricLaplacianOn_of_isBigClass_of_dim_le_one`: source
  `thm:DNT23_C11bar` for `n ≤ 1`, the book's class `C^{1,1̄}` (bounded `ω`-Laplacian).
* `sourceMinimalEnvelope_hasBoundedMetricLaplacianOn_of_isBigClass_of_dim_le_one`: its
  "in particular" for `V_θ`.
* `sourceObstacleEnvelope_isCOneOneBarOn_of_isBigClass_of_dim_le_one_of_hasBoundedComplexHessian`,
  `sourceMinimalEnvelope_isCOneOneBarOn_of_isBigClass_of_dim_le_one`: the same for obstacles with
  bounded complex Hessian, in the bounded-complex-Hessian class `IsCOneOneBarOn`.
-/

set_option autoImplicit false

noncomputable section

universe u

open Set Filter MeasureTheory
open scoped Topology

namespace SGPT.NPP.DNTBig

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.ManifoldTubePositivity
open SGPT.PSH SGPT.PSH.VariableComplexAtlas
open SGPT.Envelopes.LapClass SGPT.Envelopes.DNTReg
open SGPT.Okounkov SGPT.Okounkov.TranscendentalVolId

/-! ### Big classes in dimension at most one are Kähler classes -/

section Kahler

variable {N : ℕ} {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel N) Y]
  [IsComplexManifold N Y]

/-- If the classes of `θ` and of a Kähler form `κ` agree, then `θ + dd^c ρ` is a Kähler form for
a chart-smooth `ρ`. -/
theorem exists_isKahler_add_ddc_of_ofRepresentative_eq (θ : ClosedRealOneOneForm N Y)
    (κ : KahlerBackground N Y)
    (h : RealBottChern.ofRepresentative θ = RealBottChern.ofRepresentative κ.form) :
    ∃ ρ : Y → ℝ, ∃ hρ : ChartSmooth (n := N) ρ, (θ + ddcClosedForm ρ hρ).val.IsKahler := by
  obtain ⟨g, hg, heq⟩ := (RealBottChern.ofRepresentative_eq_iff _ _).mp h
  refine ⟨g, hg, ?_⟩
  have hgeom : κ.form.val.GeometricallyEq (θ + ddcClosedForm g hg).val := by
    intro e z hz
    rw [heq e z hz, ClosedRealOneOneForm.coeff_add, ddcClosedForm_coeff]
  exact hgeom.isKahler_iff.mp κ.isKahler

/-- In complex dimension zero every closed real `(1,1)`-form is a Kähler form. -/
theorem isKahler_of_dim_zero (hN : N = 0) (θ : ClosedRealOneOneForm N Y) : θ.val.IsKahler := by
  subst hN
  refine ⟨fun e z _ => ⟨θ.2.2 e z ‹_›, fun u hu => absurd (Subsingleton.elim u 0) hu⟩, θ.2.1⟩

omit [IsComplexManifold N Y] in
/-- The flag `X ⊇ {q}` of a curve. -/
def curvePointFlag (q : Y) : Fin (1 + 1) → Set Y := fun i => if i = 0 then univ else {q}

omit [ChartedSpace (ComplexModel N) Y] [IsComplexManifold N Y] in
/-- The flag `X ⊇ {q}` of a connected curve is a smooth flag. -/
theorem curvePointFlag_isSmooth [ChartedSpace (ComplexModel 1) Y] [IsComplexManifold 1 Y]
    [ConnectedSpace Y] (q : Y) : Okounkov.IsSmoothFlag (n := 1) (curvePointFlag q) := by
  refine ⟨rfl, ?_, ?_⟩
  · intro i j hij
    by_cases hi : i = 0
    · subst hi
      simp only [curvePointFlag]
      exact subset_univ _
    · have hj : j ≠ 0 := by
        intro hj; subst hj
        exact hi (le_antisymm hij (Fin.zero_le _))
      simp only [curvePointFlag, if_neg hi, if_neg hj, subset_refl]
  · intro i
    by_cases hi : i = 0
    · subst hi
      simp only [curvePointFlag, Fin.val_zero, Nat.sub_zero]
      exact ⟨isClosed_univ, isConnected_univ, fun x _ =>
        SGPT.Foundations.Analysis.Pending.AnalyticIrreducibleComponents.regularAtDim_univ
          (n := 1) x⟩
    · have hi1 : (i : ℕ) = 1 := by
        have := i.isLt
        have : (i : ℕ) ≠ 0 := fun h => hi (Fin.ext h)
        omega
      simp only [curvePointFlag, if_neg hi, hi1, Nat.sub_self]
      exact DominationLogResolution.isClosedConnectedSubmanifold_singleton (k := 1) q

/-- **A big class on a compact connected Kähler curve is a Kähler class.**  A big class has
positive volume (`sourceClassVolume_pos_iff_isBigClass`), the volume of a class on a curve is
`max(∫_X θ, 0)` (`sourceClassVolume_eq_ofReal_curveDegree`), and a class of positive degree
contains a Kähler form (`exists_kahler_of_curveDegree_pos`). -/
theorem exists_isKahler_add_ddc_of_isBigClass_of_dim_one [CompactSpace Y] [ConnectedSpace Y]
    (hN : N = 1) (w : KahlerBackground N Y) (θ : ClosedRealOneOneForm N Y)
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ)) :
    ∃ ρ : Y → ℝ, ∃ hρ : ChartSmooth (n := N) ρ, (θ + ddcClosedForm ρ hρ).val.IsKahler := by
  subst hN
  obtain ⟨q⟩ : Nonempty Y := ConnectedSpace.toNonempty
  let F : OriginalFlagGeometry.{u} 1 :=
    OriginalFlagGeometry.ofOriginal w (curvePointFlag q) (curvePointFlag_isSmooth q)
  let _ : MeasurableSpace F.carrier := borel F.carrier
  have _ : BorelSpace F.carrier := ⟨rfl⟩
  have hvol := (TranscendentalVolumeConcavity.sourceClassVolume_pos_iff_isBigClass (m := 0)
    (X := F.carrier) F.omega (RealBottChern.ofRepresentative (θ : ClosedRealOneOneForm 1 F.carrier))).mpr
    hbig
  rw [sourceClassVolume_eq_ofReal_curveDegree (F := F) θ] at hvol
  obtain ⟨κ, hκ⟩ := exists_kahler_of_curveDegree_pos (F := F) (ENNReal.ofReal_pos.mp hvol)
  exact exists_isKahler_add_ddc_of_ofRepresentative_eq θ κ hκ.symm

/-- **Big classes are Kähler classes in complex dimension at most one.** -/
theorem exists_isKahler_add_ddc_of_isBigClass_of_dim_le_one [CompactSpace Y] [ConnectedSpace Y]
    (hN : N ≤ 1) (w : KahlerBackground N Y) (θ : ClosedRealOneOneForm N Y)
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ)) :
    ∃ ρ : Y → ℝ, ∃ hρ : ChartSmooth (n := N) ρ, (θ + ddcClosedForm ρ hρ).val.IsKahler := by
  rcases Nat.lt_or_ge N 1 with h0 | h1
  · have hN0 : N = 0 := by omega
    refine ⟨fun _ => 0, fun _ => contDiffOn_const, isKahler_of_dim_zero hN0 _⟩
  · exact exists_isKahler_add_ddc_of_isBigClass_of_dim_one (by omega) w θ hbig

end Kahler

/-! ### The source statement for `n ≤ 1` -/

section Source

variable {N : ℕ} {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel N) Y]
  [IsComplexManifold N Y] [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y] [ConnectedSpace Y]

/-- **Source `thm:DNT23_C11bar` in complex dimension `n ≤ 1`** (book class `C^{1,1̄}`, bounded
`ω`-Laplacian): if `{θ}` is big and `f ∈ C^{1,1̄}_ω(X)`, then
`P_θ(f) = sourceRelativeEnvelope θ ⊤ f` (`def:Pthetaf`) is real-valued and lies in
`C^{1,1̄}_ω(X ∖ nK({θ}))`, with `nK = sourceNonKahlerLocus` (`def:nKlocus`). -/
theorem sourceObstacleEnvelope_hasBoundedMetricLaplacianOn_of_isBigClass_of_dim_le_one
    (hN : N ≤ 1) (w : KahlerBackground N Y) (θ : AtlasClosedRealOneOneForm (ofFixedModel N Y))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    {f : Y → ℝ} (hf : HasBoundedMetricLaplacian w f) :
    (∀ x, sourceRelativeEnvelope θ (fun _ => ⊤) (fun y => (f y : EReal)) x =
      (((sourceRelativeEnvelope θ (fun _ => ⊤) (fun y => (f y : EReal)) x).toReal : ℝ) : EReal)) ∧
    HasBoundedMetricLaplacianOn w
      (sourceNonKahlerLocus (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))ᶜ
      (fun x => (sourceRelativeEnvelope θ (fun _ => ⊤) (fun y => (f y : EReal)) x).toReal) := by
  obtain ⟨ρ, hρ, hK⟩ := exists_isKahler_add_ddc_of_isBigClass_of_dim_le_one hN w _ hbig
  exact sourceObstacleEnvelope_hasBoundedMetricLaplacianOn_of_kahlerClass w θ hρ hK hf

/-- **The "in particular" of source `thm:DNT23_C11bar` in complex dimension `n ≤ 1`**: if `{θ}`
is big, `V_θ` (`sourceMinimalEnvelope`, `eq:Vtheta`) is real-valued and lies in
`C^{1,1̄}_ω(X ∖ nK({θ}))`. -/
theorem sourceMinimalEnvelope_hasBoundedMetricLaplacianOn_of_isBigClass_of_dim_le_one
    (hN : N ≤ 1) (w : KahlerBackground N Y) (θ : AtlasClosedRealOneOneForm (ofFixedModel N Y))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ))) :
    (∀ x, sourceMinimalEnvelope θ x = (((sourceMinimalEnvelope θ x).toReal : ℝ) : EReal)) ∧
    HasBoundedMetricLaplacianOn w
      (sourceNonKahlerLocus (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))ᶜ
      (fun x => (sourceMinimalEnvelope θ x).toReal) := by
  obtain ⟨ρ, hρ, hK⟩ := exists_isKahler_add_ddc_of_isBigClass_of_dim_le_one hN w _ hbig
  exact sourceMinimalEnvelope_hasBoundedMetricLaplacianOn_of_kahlerClass w θ hρ hK

omit [MeasurableSpace Y] [BorelSpace Y] in
/-- **Source `thm:DNT23_C11bar` in complex dimension `n ≤ 1`, obstacles with bounded complex
Hessian**: if `{θ}` is big and `f` has bounded complex Hessian, then `P_θ(f)` is real-valued and
`C^{1,1̄}` (bounded complex Hessian) on `X ∖ nK({θ})`. -/
theorem sourceObstacleEnvelope_isCOneOneBarOn_of_isBigClass_of_dim_le_one_of_hasBoundedComplexHessian
    (hN : N ≤ 1) (w : KahlerBackground N Y) (θ : AtlasClosedRealOneOneForm (ofFixedModel N Y))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    {f : Y → ℝ} (hf : SGPT.Envelopes.DNTC11.HasBoundedComplexHessian (n := N) f) :
    (∀ x, sourceRelativeEnvelope θ (fun _ => ⊤) (fun y => (f y : EReal)) x =
      (((sourceRelativeEnvelope θ (fun _ => ⊤) (fun y => (f y : EReal)) x).toReal : ℝ) : EReal)) ∧
    IsCOneOneBarOn (N := N)
      (sourceNonKahlerLocus (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))ᶜ
      (fun x => (sourceRelativeEnvelope θ (fun _ => ⊤) (fun y => (f y : EReal)) x).toReal) := by
  obtain ⟨ρ, hρ, hK⟩ := exists_isKahler_add_ddc_of_isBigClass_of_dim_le_one hN w _ hbig
  exact sourceObstacleEnvelope_isCOneOneBarOn_of_kahlerClass_of_hasBoundedComplexHessian θ hρ hK hf

/-- **The "in particular" in complex dimension `n ≤ 1`, bounded-complex-Hessian class**: if `{θ}`
is big, `V_θ` is real-valued and `C^{1,1̄}` (bounded complex Hessian) on `X ∖ nK({θ})`. -/
theorem sourceMinimalEnvelope_isCOneOneBarOn_of_isBigClass_of_dim_le_one
    (hN : N ≤ 1) (w : KahlerBackground N Y) (θ : AtlasClosedRealOneOneForm (ofFixedModel N Y))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ))) :
    (∀ x, sourceMinimalEnvelope θ x = (((sourceMinimalEnvelope θ x).toReal : ℝ) : EReal)) ∧
    IsCOneOneBarOn (N := N)
      (sourceNonKahlerLocus (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))ᶜ
      (fun x => (sourceMinimalEnvelope θ x).toReal) := by
  obtain ⟨ρ, hρ, hK⟩ := exists_isKahler_add_ddc_of_isBigClass_of_dim_le_one hN w _ hbig
  exact sourceMinimalEnvelope_isCOneOneBarOn_of_kahlerClass w θ hρ hK

end Source

end SGPT.NPP.DNTBig
