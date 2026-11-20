import SGPT.Trace.BertiniSliceNormLowerSemicontinuity

/-!+# Genuine residue coordinates for the Bertini slices

The normal derivative is derived nonzero from the actual holomorphic inverse
chart. Fibre parameters have the actual complex dimension n-1, with a literal
Lebesgue patch measure. These are geometric inputs to the residue norm step;
the canonical-bundle adjunction and global norm identity remain separate.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace SGPT.Trace.Bertini

open Bundle Set Filter Metric MeasureTheory
open scoped Manifold ContDiff Topology ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open scoped ProductComplexManifold
open ProductComplexManifold
open SGPT.Bergman.QuantizationDraft SGPT.Bergman.CompactHolomorphicSectionsDraft
open SGPT.Bergman.TensorDictionaryDraft

/-- Actual holomorphic inverse maps force the original derivative injective
at EVERY point of their genuine source. -/
theorem localHolomorphicEquivAt_fderiv_injective {d : ℕ} {w₀ : ComplexModel d}
    (Φ : LocalHolomorphicEquivAt w₀) {w : ComplexModel d} (hw : w ∈ Φ.source) :
    Function.Injective (fderiv ℂ Φ.toFun w) := by
  have hF := (Φ.toFun_holomorphic w hw).differentiableAt (Φ.isOpen_source.mem_nhds hw)
  have hinv := (Φ.invFun_holomorphic (Φ.toFun w) (Φ.mapsTo_toFun hw)).differentiableAt
    (Φ.isOpen_target.mem_nhds (Φ.mapsTo_toFun hw))
  have hcomp := hinv.hasFDerivAt.comp w hF.hasFDerivAt
  have heq : (Φ.invFun ∘ Φ.toFun) =ᶠ[𝓝 w] id := by
    filter_upwards [Φ.isOpen_source.mem_nhds hw] with z hz
    exact Φ.left_inv z hz
  have hid := hcomp.congr_of_eventuallyEq heq.symm
  have hD := hid.unique (hasFDerivAt_id w)
  intro a b hab
  have h := congrArg (fderiv ℂ Φ.invFun (Φ.toFun w)) hab
  change ((fderiv ℂ Φ.invFun (Φ.toFun w)).comp (fderiv ℂ Φ.toFun w)) a =
    ((fderiv ℂ Φ.invFun (Φ.toFun w)).comp (fderiv ℂ Φ.toFun w)) b at h
  rw [hD] at h
  exact h

variable {n N : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  {p : X → SGPT.Projective.ComplexProjectiveSpace N} {φ : X → EReal}

namespace SliceChart

/-- The actual normal derivative of the original incidence equation cannot
vanish anywhere in the genuine flattening source. -/
theorem conormal_normal_ne_zero (c : SliceChart n p φ)
    (hp : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel N) ∞ p)
    {w : ComplexModel (N + n)} (hw : w ∈ c.Φ.source) :
    conormalGenerator p c.i c.e c.j c.m.succ w ≠ 0 := by
  have hwD := c.source_subset hw
  have hG := (differentiableOn_conormalGenerator p hp c.i c.e c.j 0 w hwD).differentiableAt
    ((isOpen_conormalDomain p hp c.e c.j).mem_nhds hwD)
  let D := ContinuousLinearMap.id ℂ (ComplexModel (N + n)) +
    (fderiv ℂ (conormalGenerator p c.i c.e c.j 0) w - slCoord c.m).smulRight (slDir c.m)
  have hD : fderiv ℂ (flatMap p c.i c.e c.j c.m) w = D :=
    (hasFDerivAt_flatMap p c.m hG.hasFDerivAt).fderiv
  have hinj : Function.Injective D := by
    rw [← hD, ← c.toFun_eq]
    exact localHolomorphicEquivAt_fderiv_injective c.Φ hw
  intro hzero
  have hGzero : fderiv ℂ (conormalGenerator p c.i c.e c.j 0) w (slDir c.m) = 0 := by
    rw [fderiv_conormalGenerator_zero_slDir p hp hwD c.m, hzero]
  have hdir : D (slDir c.m) = 0 := by
    change slDir c.m +
      (fderiv ℂ (conormalGenerator p c.i c.e c.j 0) w (slDir c.m) - slCoord c.m (slDir c.m)) •
        slDir c.m = 0
    rw [hGzero, slCoord_slDir]
    simp
  have hz : slDir (N := N) c.m = 0 := hinj (hdir.trans (map_zero D).symm)
  have h := congrArg (slCoord (N := N) c.m) hz
  simp only [slCoord_slDir, map_zero, one_ne_zero] at h

/-- The native conormal denominator in the actual moving inverse coordinates. -/
def normalDenominator (c : SliceChart n p φ)
    (q : (ball c.ζ₀ c.r) × (ball c.z₀ c.r)) : ℂ :=
  conormalGenerator p c.i c.e c.j c.m.succ
    (c.Φ.invFun (flatProj c.m (prodModelEquiv N n (q.1.val, q.2.val))))

/-- Actual transversality, with no nonvanishing denominator certificate. -/
theorem normalDenominator_ne_zero (c : SliceChart n p φ)
    (hp : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel N) ∞ p)
    (q : (ball c.ζ₀ c.r) × (ball c.z₀ c.r)) : c.normalDenominator q ≠ 0 :=
  c.conormal_normal_ne_zero hp
    (c.Φ.mapsTo_invFun (c.mapsTo_target q.1.val q.1.property q.2.val q.2.property))

/-- The actual normal factor depends continuously on the moving fibre point. -/
theorem continuous_normalDenominator (c : SliceChart n p φ)
    (hp : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel N) ∞ p) :
    Continuous c.normalDenominator := by
  have harg : Continuous (fun q : (ball c.ζ₀ c.r) × (ball c.z₀ c.r) =>
      flatProj c.m (prodModelEquiv N n (q.1.val, q.2.val))) :=
    (flatProj c.m).continuous.comp ((prodModelEquiv N n).continuous.comp
      ((continuous_subtype_val.comp continuous_fst).prodMk
        (continuous_subtype_val.comp continuous_snd)))
  have hinv := c.Φ.invFun_holomorphic.continuousOn.comp_continuous harg
    (fun q => c.mapsTo_target q.1.val q.1.property q.2.val q.2.property)
  exact (differentiableOn_conormalGenerator p hp c.i c.e c.j c.m.succ).continuousOn.comp_continuous
    hinv (fun q => c.source_subset
      (c.Φ.mapsTo_invFun (c.mapsTo_target q.1.val q.1.property q.2.val q.2.property)))

end SliceChart

/-- Insertion into the original tangent-coordinate hyperplane is an actual
continuous complex-linear map, with domain of complex dimension d. -/
def tangentCoordinateInsert {d : ℕ} (m : Fin (d + 1)) :
    ComplexModel d →L[ℂ] ComplexModel (d + 1) :=
  LinearMap.toContinuousLinearMap {
    toFun b := WithLp.toLp 2 (Fin.insertNth m 0 fun i => b i)
    map_add' a b := by
      ext i
      rcases Fin.eq_self_or_eq_succAbove m i with rfl | ⟨j, rfl⟩ <;> simp
    map_smul' a b := by
      ext i
      rcases Fin.eq_self_or_eq_succAbove m i with rfl | ⟨j, rfl⟩ <;> simp }

namespace SliceChart

variable {d : ℕ} {Y : Type} [TopologicalSpace Y]
  [ChartedSpace (ComplexModel (d + 1)) Y] [IsComplexManifold (d + 1) Y]
  {p : Y → SGPT.Projective.ComplexProjectiveSpace N} {φ : Y → EReal}
  (c : SliceChart (d + 1) p φ)

/-- The redundant normal coordinate is fixed, while the genuine d tangent
coordinates vary. The flattening projection removes that fixed coordinate. -/
def tangentLift (b : ComplexModel d) : ComplexModel (d + 1) :=
  EuclideanSpace.single c.m (c.z₀ c.m) + tangentCoordinateInsert c.m b

theorem continuous_tangentLift : Continuous c.tangentLift :=
  continuous_const.add (tangentCoordinateInsert c.m).continuous

/-- Actual open tangent-coordinate domain, of complex dimension d=n-1. -/
def tangentPatch : Set (ComplexModel d) := c.tangentLift ⁻¹' ball c.z₀ c.r

theorem isOpen_tangentPatch : IsOpen c.tangentPatch :=
  isOpen_ball.preimage c.continuous_tangentLift

/-- The actual tangent patch contains the original point's remaining coordinates. -/
theorem tangentPatch_nonempty : c.tangentPatch.Nonempty := by
  let b : ComplexModel d := WithLp.toLp 2 (fun i => c.z₀ (c.m.succAbove i))
  have hb : c.tangentLift b = c.z₀ := by
    ext i
    rcases Fin.eq_self_or_eq_succAbove c.m i with rfl | ⟨j, rfl⟩ <;>
      simp [tangentLift, tangentCoordinateInsert, b, Fin.succAbove_ne]
  refine ⟨b, ?_⟩
  change c.tangentLift b ∈ ball c.z₀ c.r
  rw [hb]
  exact mem_ball_self c.r_pos

/-- Literal Lebesgue measure on the original d-dimensional tangent-coordinate patch. -/
def tangentPatchVolume : Measure c.tangentPatch :=
  Measure.comap (Subtype.val : c.tangentPatch → ComplexModel d) volume

/-- The actual member parametrization, now with only n-1 complex fibre coordinates. -/
def tangentPoint (q : (ball c.ζ₀ c.r) × c.tangentPatch) : Y :=
  c.point q.1.val (c.tangentLift q.2.val)

theorem continuous_tangentPoint : Continuous c.tangentPoint := by
  have hl : Continuous (fun b : c.tangentPatch =>
      (⟨c.tangentLift b.val, b.property⟩ : ball c.z₀ c.r)) :=
    (c.continuous_tangentLift.comp continuous_subtype_val).subtype_mk _
  have hpair : Continuous (fun q : (ball c.ζ₀ c.r) × c.tangentPatch =>
      (q.1, (⟨c.tangentLift q.2.val, q.2.property⟩ : ball c.z₀ c.r))) :=
    continuous_fst.prodMk (hl.comp continuous_snd)
  exact Continuous.comp
    (g := fun q : (ball c.ζ₀ c.r) × (ball c.z₀ c.r) => c.point q.1.val q.2.val)
    (f := fun q : (ball c.ζ₀ c.r) × c.tangentPatch =>
      (q.1, (⟨c.tangentLift q.2.val, q.2.property⟩ : ball c.z₀ c.r)))
    c.continuous_joint_point hpair

/-- These are actual points on the original varying hyperplane member. -/
theorem tangentPoint_mem_member (q : (ball c.ζ₀ c.r) × c.tangentPatch) :
    c.tangentPoint q ∈ member p (SGPT.Projective.ComplexProjectiveSpace.affinePoint c.i q.1.val) :=
  c.point_mem_member q.1.property q.2.property

/-- Actual Fatou for original finite-section norms, with the genuine n-1
coordinate Lebesgue measure on the produced native incidence patch. -/
theorem lowerSemicontinuous_nativeTangentSectionMass
    (E : HermitianHolomorphicLineBundle (d + 1) Y) {r : ℕ}
    (S : Fin r → HolomorphicSections (n := d + 1) E.Fiber)
    (hφ : ManifoldQuasiPlurisubharmonic (n := d + 1) φ) :
    LowerSemicontinuous (fun q : (ball c.ζ₀ c.r) × (Fin r → ℂ) =>
      ∫⁻ b, nativeMovingSectionDensity E S c.tangentPoint φ q b ∂c.tangentPatchVolume) :=
  lowerSemicontinuous_nativeMovingSectionMass E S c.tangentPoint φ
    c.tangentPatchVolume c.continuous_tangentPoint hφ

end SliceChart

end SGPT.Trace.Bertini
