import SGPT.PSH.BookDeep2LelongBound
import SGPT.Okounkov.FlagLelong
import SGPT.PSH.SourceTestCurvePositiveMass
import SGPT.Foundations.Analysis.Pending.PshConvexCone

/-!
# Slice Lelong numbers of a test curve along a prime divisor over `X`

For a test curve `Γ` on a compact complex manifold `X` and a prime divisor `E` over `X` (a
`PrimePresentation`: a modification `π : Y → X` and a connected smooth hypersurface `E ⊆ Y`),
the generic Lelong numbers `τ ↦ ν(Γ_τ, E)` (`presentationReader`, `def:pshfunctions:L1112`) form
a finite, monotone and convex function on `(-∞, Γ_max)`.  This is the input of the Legendre
inversion used in the book's proof of `lma:anaorder` (`chapter_NApotential.tex`): there
`Γ^An(t ord_E) = sup_τ (τ - t ν(Γ_τ, E))` and the inversion recovers `ν(Γ_τ, E)`.

Convexity comes from the concavity of `τ ↦ Γ_τ`, the antitonicity of Lelong numbers and the
subadditivity and positive homogeneity of generic Lelong numbers along `E`.

## Main results

* `squaredLogLelongNumber_anti`, `presentationReader_anti`: Lelong numbers are antitone.
* `manifoldQuasiPlurisubharmonic_const_mul`: positive multiples of quasi-psh functions.
* `sourceGeneric_subtype_add_le`: `ν(u + v, W) ≤ ν(u, W) + ν(v, W)` for quasi-psh `u, v`
  (no nondegeneracy needed).
* `presentationReader_convexComb_le`, `presentationReader_ne_top`.
* `sliceLelong Γ E τ = ν(Γ_τ, E)`, with `sliceLelong_monotoneOn` and `sliceLelong_convexOn`.
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.NAPotential.BJPrep

universe u

open Set Filter
open scoped ENNReal Topology ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.ThetaPshConvexCombination
open SquaredLogLelongSourceNormalization SourceTraceRepresentativeDefinition
open SGPT.PSH.VariableComplexAtlas SGPT.PSH.CompactPrimeOver

section Pointwise

variable {n : ℕ} {Y : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]

/-- Lelong numbers are antitone: a larger function has smaller Lelong numbers. -/
theorem squaredLogLelongNumber_anti {u v : Y → EReal} (huv : u ≤ v) (x : Y) :
    squaredLogLelongNumber (n := n) v x ≤ squaredLogLelongNumber (n := n) u x := by
  unfold squaredLogLelongNumber
  split_ifs
  · exact le_rfl
  · apply biSup_mono
    rintro γ ⟨C, hC⟩
    exact ⟨C, hC.mono fun y hy => (huv y).trans hy⟩

/-- Generic Lelong numbers along a carrier are positively homogeneous. -/
theorem sourceGeneric_subtype_smul_eq (W : Set Y) (u : Y → EReal) {c : ℝ} (hc : 0 < c) :
    sourceGenericLelongNumber (n := n) (Subtype.val : W → Y) (fun y => (c : EReal) * u y) =
      ENNReal.ofReal c * sourceGenericLelongNumber (n := n) (Subtype.val : W → Y) u := by
  unfold sourceGenericLelongNumber
  simp_rw [SGPT.Okounkov.squaredLogLelongNumber_smul_eq u _ hc,
    ← ENNReal.mul_iInf_of_ne (ENNReal.ofReal_pos.mpr hc).ne' ENNReal.ofReal_ne_top]

variable [IsComplexManifold n Y]

/-- Positive multiples of quasi-psh functions are quasi-psh. -/
theorem manifoldQuasiPlurisubharmonic_const_mul {u : Y → EReal}
    (hu : ManifoldQuasiPlurisubharmonic (n := n) u) {c : ℝ} (hc : 0 < c) :
    ManifoldQuasiPlurisubharmonic (n := n) (fun y => (c : EReal) * u y) := by
  intro e z hz
  obtain ⟨p, h, hp, hh, heq⟩ := hu e z hz
  refine ⟨fun w => (c : EReal) * p w, fun w => c * h w, hp.const_mul hc, ?_, ?_⟩
  · exact hh.mono fun w hw => contDiffAt_const.mul hw
  · filter_upwards [heq] with w hw
    change (c : EReal) * u (e.val.symm w) = (c : EReal) * p w + ((c * h w : ℝ) : EReal)
    change u (e.val.symm w) = p w + (h w : EReal) at hw
    rw [hw, coe_mul_add_coe hc]

/-- Generic Lelong numbers along a closed connected submanifold are subadditive on quasi-psh
functions.  (Unlike `SGPT.Okounkov.sourceGeneric_subtype_add_eq`, no nondegeneracy is needed for
this inequality.) -/
theorem sourceGeneric_subtype_add_le {W : Set Y} {k : ℕ}
    (hW : IsClosedConnectedSubmanifold n W k) {u v : Y → EReal}
    (hu : ManifoldQuasiPlurisubharmonic (n := n) u)
    (hv : ManifoldQuasiPlurisubharmonic (n := n) v) :
    sourceGenericLelongNumber (n := n) (Subtype.val : W → Y) (fun y => u y + v y) ≤
      sourceGenericLelongNumber (n := n) (Subtype.val : W → Y) u +
        sourceGenericLelongNumber (n := n) (Subtype.val : W → Y) v := by
  by_cases htop : sourceGenericLelongNumber (n := n) (Subtype.val : W → Y) u = ⊤
  · rw [htop, top_add]
    exact le_top
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε _hsum
  obtain ⟨x, hx⟩ := SourceGenericSubmanifoldMinimum.exists_sourceGeneric_subtype_minimum hu hW
  let O : Set Y := {y | squaredLogLelongNumber (n := n) u y <
    sourceGenericLelongNumber (n := n) (Subtype.val : W → Y) u + ε}
  have hO : IsOpen O :=
    (SGPT.Okounkov.upperSemicontinuous_squaredLogLelongNumber hu).isOpen_preimage _
  have hxO : (x : Y) ∈ O := by
    change squaredLogLelongNumber (n := n) u x <
      sourceGenericLelongNumber (n := n) (Subtype.val : W → Y) u + ε
    rw [hx]
    exact ENNReal.lt_add_right htop (by exact_mod_cast hε.ne')
  obtain ⟨V, hV, _⟩ :=
    SourceGenericSubmanifoldMinimum.exists_subvariety_carrier_eq_of_submanifold hW
  obtain ⟨y, hy, hmin⟩ := SourceGenericPrimeIdealOrder.exists_source_minimum_on_open_piece
    hv V hO ⟨x, by simpa only [hV] using x.property, hxO⟩
  have hyW : y ∈ W := by simpa only [hV] using hy.1
  have hminv : squaredLogLelongNumber (n := n) v y =
      sourceGenericLelongNumber (n := n) (Subtype.val : W → Y) v := by
    rw [SourceGenericSubmanifoldMinimum.sourceGeneric_subtype_eq_iInf]
    simpa only [hV] using hmin
  calc
    sourceGenericLelongNumber (n := n) (Subtype.val : W → Y) (fun z => u z + v z) ≤
        squaredLogLelongNumber (n := n) (fun z => u z + v z) y :=
      iInf_le _ (⟨y, hyW⟩ : W)
    _ = squaredLogLelongNumber (n := n) u y + squaredLogLelongNumber (n := n) v y :=
      SGPT.Okounkov.squaredLogLelongNumber_add_eq hu hv y
    _ ≤ (sourceGenericLelongNumber (n := n) (Subtype.val : W → Y) u + ε) +
        sourceGenericLelongNumber (n := n) (Subtype.val : W → Y) v :=
      add_le_add hy.2.le hminv.le
    _ = _ := by ac_rfl

end Pointwise

section Presentation

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]

/-- The generic Lelong number `ν(φ, E) = ν(π^* φ, E)` of a prime divisor over `X`, written as
the generic Lelong number along the carrier `E ⊆ Y`. -/
theorem presentationReader_eq_sourceGenericLelongNumber (φ : X → EReal)
    (p : PrimePresentation n X) :
    presentationReader φ p = sourceGenericLelongNumber (n := n)
      (Subtype.val : p.divisor → p.model) (fun y => φ (p.projection y)) := by
  rw [SourceGenericSubmanifoldMinimum.sourceGeneric_subtype_eq_iInf]
  simp only [presentationReader, sourceGenericLelong, sourceLelong_ofFixedModel_eq,
    Function.comp_def]

/-- `φ ≤ ψ` implies `ν(ψ, E) ≤ ν(φ, E)`. -/
theorem presentationReader_anti {φ ψ : X → EReal} (h : φ ≤ ψ) (p : PrimePresentation n X) :
    presentationReader ψ p ≤ presentationReader φ p := by
  rw [presentationReader_eq_sourceGenericLelongNumber,
    presentationReader_eq_sourceGenericLelongNumber]
  unfold sourceGenericLelongNumber
  exact iInf_mono fun y => squaredLogLelongNumber_anti (fun z => h (p.projection z)) _

/-- The pull-back of a `θ`-psh function to the model of a prime divisor over `X` is quasi-psh. -/
theorem manifoldQuasiPlurisubharmonic_comp_projection
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n X)} {φ : X → EReal}
    (hφ : (ofFixedModel n X).IsThetaPSH θ φ) (p : PrimePresentation n X) :
    ManifoldQuasiPlurisubharmonic (n := n) (fun y => φ (p.projection y)) :=
  GlobalPotentialPullback.manifoldQuasiPlurisubharmonic_comp p.modification.1
    (SGPT.PSH.BookDeep2LelongBound.manifoldQuasiPlurisubharmonic_of_isThetaPSH hφ)

/-- Convexity of `ν(·, E)` on `PSH(X, θ)`:
`ν((1-s)ψ + sφ, E) ≤ s ν(φ, E) + (1-s) ν(ψ, E)` (with `convexComb s φ ψ = sφ + (1-s)ψ`). -/
theorem presentationReader_convexComb_le
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n X)} {φ ψ : X → EReal}
    (hφ : (ofFixedModel n X).IsThetaPSH θ φ) (hψ : (ofFixedModel n X).IsThetaPSH θ ψ)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (p : PrimePresentation n X) :
    presentationReader (convexComb s φ ψ) p ≤
      ENNReal.ofReal s * presentationReader φ p +
        ENNReal.ofReal (1 - s) * presentationReader ψ p := by
  have hφ' := manifoldQuasiPlurisubharmonic_comp_projection hφ p
  have hψ' := manifoldQuasiPlurisubharmonic_comp_projection hψ p
  have hs1' : 0 < 1 - s := sub_pos.mpr hs1
  rw [presentationReader_eq_sourceGenericLelongNumber,
    presentationReader_eq_sourceGenericLelongNumber,
    presentationReader_eq_sourceGenericLelongNumber]
  have hsub := sourceGeneric_subtype_add_le p.smooth
    (manifoldQuasiPlurisubharmonic_const_mul hφ' hs0)
    (manifoldQuasiPlurisubharmonic_const_mul hψ' hs1')
  rw [sourceGeneric_subtype_smul_eq _ _ hs0, sourceGeneric_subtype_smul_eq _ _ hs1'] at hsub
  simpa only [convexComb] using hsub

/-- The generic Lelong number of a `θ`-psh function along a prime divisor over a compact `X`
is finite (`prop:Lelongnumberupperbound`). -/
theorem presentationReader_ne_top [CompactSpace X]
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n X)} {φ : X → EReal}
    (hφ : (ofFixedModel n X).IsThetaPSH θ φ) (p : PrimePresentation n X) :
    presentationReader φ p ≠ ⊤ := by
  obtain ⟨C, hC⟩ := SGPT.PSH.BookDeep2LelongBound.exists_presentationReader_le θ p
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hC φ hφ)

end Presentation

section TestCurve

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)}

/-- The slice Lelong numbers `τ ↦ ν(Γ_τ, E)` of a test curve along a prime divisor over `M`, as
a real function on `(-∞, Γ_max)` (set to `0` elsewhere). -/
def sliceLelong (Γ : SourceTestCurvePredata θ) (p : PrimePresentation n M) (τ : ℝ) : ℝ :=
  if h : τ < Γ.max then (presentationReader (Γ.potential ⟨τ, h⟩) p).toReal else 0

theorem sliceLelong_of_lt (Γ : SourceTestCurvePredata θ) (p : PrimePresentation n M)
    {τ : ℝ} (h : τ < Γ.max) :
    sliceLelong Γ p τ = (presentationReader (Γ.potential ⟨τ, h⟩) p).toReal :=
  dif_pos h

theorem sliceLelong_nonneg (Γ : SourceTestCurvePredata θ) (p : PrimePresentation n M) (τ : ℝ) :
    0 ≤ sliceLelong Γ p τ := by
  unfold sliceLelong
  split_ifs
  · exact ENNReal.toReal_nonneg
  · exact le_rfl

/-- `ν(Γ_τ, E)` is finite and its real value is `sliceLelong`. -/
theorem coe_sliceLelong [CompactSpace M] (Γ : SourceTestCurvePredata θ)
    (p : PrimePresentation n M) {τ : ℝ} (h : τ < Γ.max) :
    ENNReal.ofReal (sliceLelong Γ p τ) = presentationReader (Γ.potential ⟨τ, h⟩) p := by
  rw [sliceLelong_of_lt Γ p h,
    ENNReal.ofReal_toReal (presentationReader_ne_top (Γ.thetaPSH _) p)]

/-- `τ ↦ ν(Γ_τ, E)` is increasing on `(-∞, Γ_max)`. -/
theorem sliceLelong_monotoneOn [CompactSpace M] (Γ : SourceTestCurvePredata θ)
    (p : PrimePresentation n M) : MonotoneOn (sliceLelong Γ p) (Iio Γ.max) := by
  intro a ha b hb hab
  rw [sliceLelong_of_lt Γ p ha, sliceLelong_of_lt Γ p hb]
  apply ENNReal.toReal_mono (presentationReader_ne_top (Γ.thetaPSH _) p)
  apply presentationReader_anti
  intro x
  exact Γ.antitone x (show (⟨a, ha⟩ : Iio Γ.max) ≤ ⟨b, hb⟩ from hab)

/-- `τ ↦ ν(Γ_τ, E)` is convex on `(-∞, Γ_max)`, by concavity of `τ ↦ Γ_τ`. -/
theorem sliceLelong_convexOn [CompactSpace M] (Γ : SourceTestCurvePredata θ)
    (p : PrimePresentation n M) : ConvexOn ℝ (Iio Γ.max) (sliceLelong Γ p) := by
  refine ⟨convex_Iio _, ?_⟩
  intro a ha b hb s r hs hr hsr
  rcases hs.eq_or_lt with hs0 | hs0
  · subst hs0
    have hr1 : r = 1 := by linarith
    subst hr1
    simp
  rcases hr.eq_or_lt with hr0 | hr0
  · subst hr0
    have hs1 : s = 1 := by linarith
    subst hs1
    simp
  have hs1 : s < 1 := by linarith
  have hr_eq : r = 1 - s := by linarith
  subst hr_eq
  have ha' : a < Γ.max := ha
  have hb' : b < Γ.max := hb
  have hdom : s * a + (1 - s) * b < Γ.max := by
    nlinarith [mul_pos hs0 (sub_pos.mpr ha'), mul_pos hr0 (sub_pos.mpr hb')]
  have hmid := Γ.convexComb_le ⟨a, ha⟩ ⟨b, hb⟩ hs0 hs1
  simp only [smul_eq_mul]
  rw [sliceLelong_of_lt Γ p hdom, sliceLelong_of_lt Γ p ha, sliceLelong_of_lt Γ p hb]
  have h1 : presentationReader (Γ.potential ⟨s * a + (1 - s) * b, hdom⟩) p ≤
      presentationReader (convexComb s (Γ.potential ⟨a, ha⟩) (Γ.potential ⟨b, hb⟩)) p :=
    presentationReader_anti hmid p
  have h2 := presentationReader_convexComb_le (Γ.thetaPSH ⟨a, ha⟩) (Γ.thetaPSH ⟨b, hb⟩)
    hs0 hs1 p
  have hfa := presentationReader_ne_top (Γ.thetaPSH ⟨a, ha⟩) p
  have hfb := presentationReader_ne_top (Γ.thetaPSH ⟨b, hb⟩) p
  have hfin : ENNReal.ofReal s * presentationReader (Γ.potential ⟨a, ha⟩) p +
      ENNReal.ofReal (1 - s) * presentationReader (Γ.potential ⟨b, hb⟩) p ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfa,
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfb⟩
  calc (presentationReader (Γ.potential ⟨s * a + (1 - s) * b, hdom⟩) p).toReal
      ≤ (ENNReal.ofReal s * presentationReader (Γ.potential ⟨a, ha⟩) p +
          ENNReal.ofReal (1 - s) * presentationReader (Γ.potential ⟨b, hb⟩) p).toReal :=
        ENNReal.toReal_mono hfin (h1.trans h2)
    _ = s * (presentationReader (Γ.potential ⟨a, ha⟩) p).toReal +
          (1 - s) * (presentationReader (Γ.potential ⟨b, hb⟩) p).toReal := by
        rw [ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfa)
            (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfb),
          ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hs0.le,
          ENNReal.toReal_ofReal hr0.le]

end TestCurve

end SGPT.NAPotential.BJPrep
