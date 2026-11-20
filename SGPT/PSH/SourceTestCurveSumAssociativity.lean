import SGPT.PSH.SourceTestCurveSumAlgebra
import SGPT.PSH.SourceGlobalOrderAddition
import SGPT.PSH.SourceGlobalOrderSupremum

/-! # Associativity of the original test-curve sum

Closed original triple summands produce a genuine common global type. Strict
outer recovery avoids asserting an envelope identity at a zero-mass cutoff.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.VariableComplexAtlas

open Set
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]
  {θ σ ρ : AtlasClosedRealOneOneForm (ofFixedModel n M)}

private theorem rawSum_le_modeled_open (omega : KahlerBackground n M)
    (Γ : SourceTestCurve θ) (Δ : SourceTestCurve σ) {r : ℝ} (hr : r < Γ.max + Δ.max) :
    sourceTestCurveRawSum Γ.toSourceTestCurvePredata Δ.toSourceTestCurvePredata r ≤
      (SourceTestCurve.sum omega Γ Δ).potential ⟨r, hr⟩ :=
  le_sourceSingularityEnvelope
    (sourceTestCurveRawSum_thetaPSH Γ.toSourceTestCurvePredata Δ.toSourceTestCurvePredata hr.le)
    (sourceTestCurveRawSum_le_zero Γ.toSourceTestCurvePredata Δ.toSourceTestCurvePredata r)
    (MoreSingularOn.of_le fun _ _ ↦ le_rfl)

/-- The literal raw convolution is below the actual modeled WHOLE extension,
including the original cutoff infimum and the entire super-cutoff region. -/
theorem sourceTestCurveRawSum_le_sum_at (omega : KahlerBackground n M)
    (Γ : SourceTestCurve θ) (Δ : SourceTestCurve σ) (r : ℝ) :
    sourceTestCurveRawSum Γ.toSourceTestCurvePredata Δ.toSourceTestCurvePredata r ≤
      sourceTestCurveAt (SourceTestCurve.sum omega Γ Δ).toSourceTestCurvePredata r := by
  let S := SourceTestCurve.sum omega Γ Δ
  by_cases hr : r < S.max
  · rw [sourceTestCurveAt_of_lt S.toSourceTestCurvePredata hr]
    exact rawSum_le_modeled_open omega Γ Δ hr
  by_cases he : r = S.max
  · subst r
    rw [sourceTestCurveAt_eq_max]
    intro x
    apply le_iInf
    intro q
    exact (sourceTestCurveRawSum_antitone Γ.toSourceTestCurvePredata
      Δ.toSourceTestCurvePredata x q.property.le).trans
        (rawSum_le_modeled_open omega Γ Δ q.property x)
  · have hgt : S.max < r := lt_of_le_of_ne (le_of_not_gt hr) (Ne.symm he)
    rw [sourceTestCurveAt_of_gt S.toSourceTestCurvePredata hgt]
    change Γ.max + Δ.max < r at hgt
    intro x
    apply iSup_le
    intro a
    by_cases ha : a ≤ Γ.max
    · have hb : Δ.max < r - a := by linarith
      simp only [sourceTestCurveAt_of_gt Δ.toSourceTestCurvePredata hb,
        Pi.bot_apply, EReal.add_bot, le_refl]
    · simp only [sourceTestCurveAt_of_gt Γ.toSourceTestCurvePredata (lt_of_not_ge ha),
        Pi.bot_apply, EReal.bot_add, le_refl]

/-- The literal spatial USC supremum of ALL original closed triple summands. -/
def sourceTestCurveTripleConvolutionUSC (Γ : SourceTestCurve θ) (Δ : SourceTestCurve σ)
    (Λ : SourceTestCurve ρ) (r : ℝ) : M → EReal :=
  uscSup (fun p : {p : ℝ × ℝ // p.1 ≤ Γ.max ∧ p.2 ≤ Δ.max ∧ r - p.1 - p.2 ≤ Λ.max} ↦
    fun x ↦ (sourceTestCurveAt Γ.toSourceTestCurvePredata p.val.1 x +
      sourceTestCurveAt Δ.toSourceTestCurvePredata p.val.2 x) +
        sourceTestCurveAt Λ.toSourceTestCurvePredata (r - p.val.1 - p.val.2) x)

omit [BorelSpace M] in
/-- Closed triple summands are genuinely PSH, including zero-mass cutoff
slices; their uniformly bounded nonempty USC supremum is genuinely PSH. -/
theorem sourceTestCurveTripleConvolutionUSC_thetaPSH
    (Γ : SourceTestCurve θ) (Δ : SourceTestCurve σ) (Λ : SourceTestCurve ρ)
    {r : ℝ} (hr : r < (Γ.max + Δ.max) + Λ.max) :
    (ofFixedModel n M).IsThetaPSH
      (nativeClosedFormToAtlas
        (atlasClosedFormToNative
          (nativeClosedFormToAtlas (atlasClosedFormToNative θ + atlasClosedFormToNative σ)) +
            atlasClosedFormToNative ρ))
      (sourceTestCurveTripleConvolutionUSC Γ Δ Λ r) := by
  let K := {p : ℝ × ℝ // p.1 ≤ Γ.max ∧ p.2 ≤ Δ.max ∧ r - p.1 - p.2 ≤ Λ.max}
  have : Nonempty K := ⟨⟨(Γ.max, Δ.max), le_rfl, le_rfl, by linarith⟩⟩
  have hF (p : K) := sourceIndependentSum_thetaPSH
    (sourceIndependentSum_thetaPSH
      ((source_test_curve_extension_whole Γ.toSourceTestCurvePredata).2.2.2 p.val.1 p.property.1)
      ((source_test_curve_extension_whole Δ.toSourceTestCurvePredata).2.2.2 p.val.2 p.property.2.1))
    ((source_test_curve_extension_whole Λ.toSourceTestCurvePredata).2.2.2
      (r - p.val.1 - p.val.2) p.property.2.2)
  apply isThetaPSH_uscSup_of_majorant hF upperSemicontinuous_const
    (fun _ ↦ EReal.coe_ne_top (0 : ℝ))
  intro p x
  simpa only [EReal.coe_zero] using add_nonpos
    (add_nonpos (Γ.at_le_zero p.val.1 x) (Δ.at_le_zero p.val.2 x))
    (Λ.at_le_zero (r - p.val.1 - p.val.2) x)

omit [BorelSpace M] [ConnectedSpace M] in
private theorem tripleUSC_le_zero (Γ : SourceTestCurve θ) (Δ : SourceTestCurve σ)
    (Λ : SourceTestCurve ρ) (r : ℝ) : sourceTestCurveTripleConvolutionUSC Γ Δ Λ r ≤ 0 := by
  apply uscRegularization_le upperSemicontinuous_const
  intro x
  apply iSup_le
  intro p
  exact add_nonpos (add_nonpos (Γ.at_le_zero p.val.1 x) (Δ.at_le_zero p.val.2 x))
    (Λ.at_le_zero (r - p.val.1 - p.val.2) x)

omit [BorelSpace M] [ConnectedSpace M] in
private theorem triple_le_tripleUSC (Γ : SourceTestCurve θ) (Δ : SourceTestCurve σ)
    (Λ : SourceTestCurve ρ) (r a b : ℝ) (x : M) :
    (sourceTestCurveAt Γ.toSourceTestCurvePredata a x +
      sourceTestCurveAt Δ.toSourceTestCurvePredata b x) +
        sourceTestCurveAt Λ.toSourceTestCurvePredata (r - a - b) x ≤
      sourceTestCurveTripleConvolutionUSC Γ Δ Λ r x := by
  by_cases ha : a ≤ Γ.max
  swap
  · simp only [sourceTestCurveAt_of_gt Γ.toSourceTestCurvePredata (lt_of_not_ge ha),
      Pi.bot_apply, EReal.bot_add, bot_le]
  by_cases hb : b ≤ Δ.max
  swap
  · simp only [sourceTestCurveAt_of_gt Δ.toSourceTestCurvePredata (lt_of_not_ge hb),
      Pi.bot_apply, EReal.add_bot, EReal.bot_add, bot_le]
  by_cases hc : r - a - b ≤ Λ.max
  swap
  · simp only [sourceTestCurveAt_of_gt Λ.toSourceTestCurvePredata (lt_of_not_ge hc),
      Pi.bot_apply, EReal.add_bot, bot_le]
  unfold sourceTestCurveTripleConvolutionUSC SGPT.PSH.uscSup
  exact (le_iSup
    (fun p : {p : ℝ × ℝ // p.1 ≤ Γ.max ∧ p.2 ≤ Δ.max ∧ r - p.1 - p.2 ≤ Λ.max} ↦
      (sourceTestCurveAt Γ.toSourceTestCurvePredata p.val.1 x +
        sourceTestCurveAt Δ.toSourceTestCurvePredata p.val.2 x) +
          sourceTestCurveAt Λ.toSourceTestCurvePredata (r - p.val.1 - p.val.2) x)
    ⟨(a, b), ha, hb, hc⟩).trans
      (le_uscRegularization (fun y ↦ ⨆ p :
        {p : ℝ × ℝ // p.1 ≤ Γ.max ∧ p.2 ≤ Δ.max ∧ r - p.1 - p.2 ≤ Λ.max},
          (sourceTestCurveAt Γ.toSourceTestCurvePredata p.val.1 y +
            sourceTestCurveAt Δ.toSourceTestCurvePredata p.val.2 y) +
              sourceTestCurveAt Λ.toSourceTestCurvePredata (r - p.val.1 - p.val.2) y) x)

omit [BorelSpace M] in
private theorem tripleUSC_le_cyclic (Γ : SourceTestCurve θ) (Δ : SourceTestCurve σ)
    (Λ : SourceTestCurve ρ) {r : ℝ} (hr : r < (Γ.max + Δ.max) + Λ.max) :
    sourceTestCurveTripleConvolutionUSC Γ Δ Λ r ≤
      sourceTestCurveTripleConvolutionUSC Δ Λ Γ r := by
  have hrot := sourceTestCurveTripleConvolutionUSC_thetaPSH Δ Λ Γ (r := r)
    (by linarith : r < (Δ.max + Λ.max) + Γ.max)
  apply uscRegularization_le
    ((isThetaPSH_iff_nativeThetaPotential _ _).mp hrot).1.quasiPlurisubharmonic.upperSemicontinuous
  intro x
  apply iSup_le
  intro p
  have h := triple_le_tripleUSC Δ Λ Γ r p.val.2 (r - p.val.1 - p.val.2) x
  rw [show r - p.val.2 - (r - p.val.1 - p.val.2) = p.val.1 by ring] at h
  simpa only [add_assoc, add_comm, add_left_comm] using h

omit [BorelSpace M] in
/-- Actual cyclic reindexing preserves the closed triple USC function. -/
theorem sourceTestCurveTripleConvolutionUSC_cyclic
    (Γ : SourceTestCurve θ) (Δ : SourceTestCurve σ) (Λ : SourceTestCurve ρ)
    {r : ℝ} (hr : r < (Γ.max + Δ.max) + Λ.max) :
    sourceTestCurveTripleConvolutionUSC Γ Δ Λ r =
      sourceTestCurveTripleConvolutionUSC Δ Λ Γ r := by
  apply le_antisymm (tripleUSC_le_cyclic Γ Δ Λ hr)
  exact (tripleUSC_le_cyclic Δ Λ Γ (by linarith : r < (Δ.max + Λ.max) + Γ.max)).trans
    (tripleUSC_le_cyclic Λ Γ Δ (by linarith : r < (Λ.max + Γ.max) + Δ.max))

private theorem tripleUSC_le_groupedRaw (omega : KahlerBackground n M)
    (Γ : SourceTestCurve θ) (Δ : SourceTestCurve σ) (Λ : SourceTestCurve ρ)
    {r : ℝ} (hr : r < (Γ.max + Δ.max) + Λ.max) :
    sourceTestCurveTripleConvolutionUSC Γ Δ Λ r ≤
      sourceTestCurveRawSum (SourceTestCurve.sum omega Γ Δ).toSourceTestCurvePredata
        Λ.toSourceTestCurvePredata r := by
  let S := SourceTestCurve.sum omega Γ Δ
  have hraw := sourceTestCurveRawSum_thetaPSH S.toSourceTestCurvePredata Λ.toSourceTestCurvePredata hr.le
  apply uscRegularization_le
    ((isThetaPSH_iff_nativeThetaPotential _ _).mp hraw).1.quasiPlurisubharmonic.upperSemicontinuous
  intro x
  apply iSup_le
  intro p
  let d := p.val.1 + p.val.2
  have hsummand : sourceTestCurveAt Γ.toSourceTestCurvePredata p.val.1 x +
      sourceTestCurveAt Δ.toSourceTestCurvePredata p.val.2 x ≤
        sourceTestCurveRawSum Γ.toSourceTestCurvePredata Δ.toSourceTestCurvePredata d x := by
    have h := le_iSup (fun a : ℝ ↦ sourceTestCurveAt Γ.toSourceTestCurvePredata a x +
      sourceTestCurveAt Δ.toSourceTestCurvePredata (d - a) x) p.val.1
    simpa only [sourceTestCurveRawSum, show d - p.val.1 = p.val.2 by dsimp [d]; ring] using h
  have hinner := hsummand.trans (sourceTestCurveRawSum_le_sum_at omega Γ Δ d x)
  calc
    _ ≤ sourceTestCurveAt S.toSourceTestCurvePredata d x +
        sourceTestCurveAt Λ.toSourceTestCurvePredata (r - d) x := by
      dsimp only
      rw [show r - p.val.1 - p.val.2 = r - d by dsimp [d]; ring]
      exact add_le_add hinner le_rfl
    _ ≤ _ := le_iSup (fun a : ℝ ↦ sourceTestCurveAt S.toSourceTestCurvePredata a x +
      sourceTestCurveAt Λ.toSourceTestCurvePredata (r - a) x) d

private theorem iSup_add_le_of_ne_top {I : Type*} (f : I → EReal) {b c : EReal}
    (hb : b ≠ ⊤) (h : ∀ i, f i + b ≤ c) : (⨆ i, f i) + b ≤ c := by
  cases b using EReal.rec with
  | bot => simp only [EReal.add_bot, bot_le]
  | top => exact False.elim (hb rfl)
  | coe b =>
    apply (EReal.le_sub_iff_add_le (.inl (EReal.coe_ne_bot b))
      (.inl (EReal.coe_ne_top b))).mp
    exact iSup_le fun i ↦ (EReal.le_sub_iff_add_le (.inl (EReal.coe_ne_bot b))
      (.inl (EReal.coe_ne_top b))).mpr (h i)

/-- Both genuine GLOBAL orders between a grouped raw convolution and the
original closed triple function; no modeled/raw cutoff identity is assumed. -/
theorem sourceTestCurveGroupedRawSum_sourcePEquivalent_triple
    (omega : KahlerBackground n M)
    (Γ : SourceTestCurve θ) (Δ : SourceTestCurve σ) (Λ : SourceTestCurve ρ)
    {r : ℝ} (hr : r < (Γ.max + Δ.max) + Λ.max) :
    GlobalPComparison.sourcePEquivalent (n := n)
      (sourceTestCurveRawSum (SourceTestCurve.sum omega Γ Δ).toSourceTestCurvePredata
        Λ.toSourceTestCurvePredata r)
      (sourceTestCurveTripleConvolutionUSC Γ Δ Λ r) := by
  let S := SourceTestCurve.sum omega Γ Δ
  let T₀ := nativeClosedFormToAtlas (atlasClosedFormToNative θ + atlasClosedFormToNative σ)
  let T := nativeClosedFormToAtlas (atlasClosedFormToNative T₀ + atlasClosedFormToNative ρ)
  let U := sourceTestCurveTripleConvolutionUSC Γ Δ Λ r
  have hU : (ofFixedModel n M).IsThetaPSH T U :=
    sourceTestCurveTripleConvolutionUSC_thetaPSH Γ Δ Λ hr
  have hraw := sourceTestCurveRawSum_thetaPSH S.toSourceTestCurvePredata Λ.toSourceTestCurvePredata hr.le
  have hUraw := SingularGlobalPOrder.sourcePOrder_of_moreSingularOn omega
    (atlasClosedFormToNative T) (atlasClosedFormToNative T)
    ((isThetaPSH_iff_nativeThetaPotential T U).mp hU)
    ((isThetaPSH_iff_nativeThetaPotential T _).mp hraw)
    (MoreSingularOn.of_le fun x _ ↦ tripleUSC_le_groupedRaw omega Γ Δ Λ hr x)
  have hU0 : U ≤ 0 := tripleUSC_le_zero Γ Δ Λ r
  let J := Ioo (r - Λ.max) S.max
  have hSmax : S.max = Γ.max + Δ.max := rfl
  have hJ : r - Λ.max < S.max := by rw [hSmax]; linarith
  have : Nonempty J := ⟨⟨((r - Λ.max) + S.max) / 2, by constructor <;> linarith⟩⟩
  let F : J → M → EReal := fun d x ↦ sourceTestCurveAt S.toSourceTestCurvePredata d.val x +
    sourceTestCurveAt Λ.toSourceTestCurvePredata (r - d.val) x
  have hd (d : J) : r - d.val < Λ.max := by linarith [d.property.1]
  have hF (d : J) : (ofFixedModel n M).IsThetaPSH T (F d) := by
    dsimp [F]
    rw [sourceTestCurveAt_of_lt S.toSourceTestCurvePredata d.property.2,
      sourceTestCurveAt_of_lt Λ.toSourceTestCurvePredata (hd d)]
    exact sourceIndependentSum_thetaPSH (S.thetaPSH _) (Λ.thetaPSH _)
  have hFU (d : J) : GlobalPComparison.sourcePOrder (n := n) (F d) U := by
    let a : Iio S.max := ⟨d.val, d.property.2⟩
    let b : Iio Λ.max := ⟨r - d.val, hd d⟩
    have hrinner : d.val < Γ.max + Δ.max := d.property.2
    have hi := sourceTestCurveRawSum_thetaPSH Γ.toSourceTestCurvePredata
      Δ.toSourceTestCurvePredata hrinner.le
    have henvelope := SingularGlobalPEnvelopeBridge.sourcePEquivalent_singularityEnvelope omega
      (atlasClosedFormToNative T₀) ((isThetaPSH_iff_nativeThetaPotential T₀ _).mp hi)
    have hinner : GlobalPComparison.sourcePEquivalent (n := n) (S.potential a)
        (sourceTestCurveRawSum Γ.toSourceTestCurvePredata Δ.toSourceTestCurvePredata d.val) := by
      change GlobalPComparison.sourcePEquivalent (n := n)
        (sourceSingularityEnvelope T₀
          (sourceTestCurveRawSum Γ.toSourceTestCurvePredata Δ.toSourceTestCurvePredata d.val)) _
      rw [sourceSingularityEnvelope_eq_native]
      exact ⟨henvelope.2, henvelope.1⟩
    have hrefl := SingularGlobalPOrder.sourcePOrder_refl_of_isThetaPshPotential omega
      (Λ.native_thetaPSH b)
    have hadd := SGPT.PSH.GlobalOrderAddition.sourcePEquivalent_add omega
      ⟨T₀, S.thetaPSH a⟩ ⟨ρ, Λ.thetaPSH b⟩ ⟨T₀, hi⟩ ⟨ρ, Λ.thetaPSH b⟩
      hinner ⟨hrefl, hrefl⟩
    have hle : (fun x ↦ sourceTestCurveRawSum Γ.toSourceTestCurvePredata
        Δ.toSourceTestCurvePredata d.val x + Λ.potential b x) ≤ U := by
      intro x
      apply iSup_add_le_of_ne_top
        (fun q : ℝ ↦ sourceTestCurveAt Γ.toSourceTestCurvePredata q x +
          sourceTestCurveAt Δ.toSourceTestCurvePredata (d.val - q) x)
        ((Λ.native_thetaPSH b).1.quasiPlurisubharmonic.ne_top x)
      intro q
      have h := triple_le_tripleUSC Γ Δ Λ r q (d.val - q) x
      rw [show r - q - (d.val - q) = r - d.val by ring,
        sourceTestCurveAt_of_lt Λ.toSourceTestCurvePredata (hd d)] at h
      exact h
    have hsum := sourceIndependentSum_thetaPSH hi (Λ.thetaPSH b)
    have hmore := SingularGlobalPOrder.sourcePOrder_of_moreSingularOn omega
      (atlasClosedFormToNative T) (atlasClosedFormToNative T)
      ((isThetaPSH_iff_nativeThetaPotential T _).mp hsum)
      ((isThetaPSH_iff_nativeThetaPotential T U).mp hU)
      (MoreSingularOn.of_le fun x _ ↦ hle x)
    have h := GlobalPComparison.sourcePOrder_trans omega hadd.1 hmore
    simpa only [F, sourceTestCurveAt_of_lt S.toSourceTestCurvePredata d.property.2,
      sourceTestCurveAt_of_lt Λ.toSourceTestCurvePredata (hd d)] using h
  have hforward := sourcePOrder_uscSup omega hF (fun _ : J ↦ hU)
    (by
      refine ⟨0, ?_⟩
      intro d x
      change F d x ≤ (0 : EReal)
      exact add_nonpos (S.at_le_zero d.val x) (Λ.at_le_zero (r - d.val) x))
    (by
      refine ⟨0, ?_⟩
      intro _ x
      change U x ≤ (0 : EReal)
      exact hU0 x) hFU
  have hFraw : sourceTestCurveRawSum S.toSourceTestCurvePredata Λ.toSourceTestCurvePredata r =
      uscSup F := sourceTestCurveRawSum_eq_uscSup_open _ _ hr
  have hconst : uscSup (fun _ : J ↦ U) = U := by
    simpa only [SGPT.PSH.uscSup, iSup_const] using uscRegularization_eq
      ((isThetaPSH_iff_nativeThetaPotential T U).mp hU).1.quasiPlurisubharmonic.upperSemicontinuous
  rw [← hFraw, hconst] at hforward
  exact ⟨hforward, hUraw⟩

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M] in
/-- Associativity identifies the actual complete atlas forms of both groupings. -/
theorem sourceTestCurveSumBackground_assoc
    (θ σ ρ : AtlasClosedRealOneOneForm (ofFixedModel n M)) :
    nativeClosedFormToAtlas
        (atlasClosedFormToNative
          (nativeClosedFormToAtlas (atlasClosedFormToNative θ + atlasClosedFormToNative σ)) +
            atlasClosedFormToNative ρ) =
      nativeClosedFormToAtlas
        (atlasClosedFormToNative θ + atlasClosedFormToNative
          (nativeClosedFormToAtlas (atlasClosedFormToNative σ + atlasClosedFormToNative ρ))) := by
  simp only [sourceNativeAtlasForm_roundTrip, add_assoc]

/-- Actual original test-curve associativity, including both real cutoff and
all original potential functions, with the exact whole background transport. -/
theorem SourceTestCurve.sum_assoc (omega : KahlerBackground n M)
    (Γ : SourceTestCurve θ) (Δ : SourceTestCurve σ) (Λ : SourceTestCurve ρ) :
    (SourceTestCurve.sum omega (SourceTestCurve.sum omega Γ Δ) Λ).castBackground
        (sourceTestCurveSumBackground_assoc θ σ ρ) =
      SourceTestCurve.sum omega Γ (SourceTestCurve.sum omega Δ Λ) := by
  let S := SourceTestCurve.sum omega Γ Δ
  let D := SourceTestCurve.sum omega Δ Λ
  let T₀ := nativeClosedFormToAtlas
    (atlasClosedFormToNative
      (nativeClosedFormToAtlas (atlasClosedFormToNative θ + atlasClosedFormToNative σ)) +
        atlasClosedFormToNative ρ)
  let T := nativeClosedFormToAtlas
    (atlasClosedFormToNative θ + atlasClosedFormToNative
      (nativeClosedFormToAtlas (atlasClosedFormToNative σ + atlasClosedFormToNative ρ)))
  have hforms : T₀ = T := sourceTestCurveSumBackground_assoc θ σ ρ
  apply SourceTestCurve.ext_of_max_potential
  · simp only [SourceTestCurve.castBackground_max, SourceTestCurve.sum_max, add_assoc]
  · intro r hr hs
    have hrl : r < (SourceTestCurve.sum omega S Λ).max := by
      simpa only [SourceTestCurve.castBackground_max] using hr
    have hrΓΔΛ : r < (Γ.max + Δ.max) + Λ.max := hrl
    have hrΔΛΓ : r < (Δ.max + Λ.max) + Γ.max := by linarith
    rw [SourceTestCurve.castBackground_potential _ _ r hrl hr]
    change sourceSingularityEnvelope T₀
        (sourceTestCurveRawSum S.toSourceTestCurvePredata Λ.toSourceTestCurvePredata r) =
      sourceSingularityEnvelope T
        (sourceTestCurveRawSum Γ.toSourceTestCurvePredata D.toSourceTestCurvePredata r)
    rw [hforms]
    have hL := sourceTestCurveGroupedRawSum_sourcePEquivalent_triple omega Γ Δ Λ hrΓΔΛ
    have hR := sourceTestCurveGroupedRawSum_sourcePEquivalent_triple omega Δ Λ Γ hrΔΛΓ
    rw [sourceTestCurveRawSum_comm D.toSourceTestCurvePredata Γ.toSourceTestCurvePredata r,
      ← sourceTestCurveTripleConvolutionUSC_cyclic Γ Δ Λ hrΓΔΛ] at hR
    have hequiv : GlobalPComparison.sourcePEquivalent (n := n)
        (sourceTestCurveRawSum S.toSourceTestCurvePredata Λ.toSourceTestCurvePredata r)
        (sourceTestCurveRawSum Γ.toSourceTestCurvePredata D.toSourceTestCurvePredata r) :=
      ⟨GlobalPComparison.sourcePOrder_trans omega hL.1 hR.2,
        GlobalPComparison.sourcePOrder_trans omega hR.1 hL.2⟩
    have hu₀ : (ofFixedModel n M).IsThetaPSH T₀
        (sourceTestCurveRawSum S.toSourceTestCurvePredata Λ.toSourceTestCurvePredata r) :=
      sourceTestCurveRawSum_thetaPSH S.toSourceTestCurvePredata Λ.toSourceTestCurvePredata hrl.le
    have hup₀ : 0 < sourcePotentialNonPluripolarMeasure T₀
        (sourceTestCurveRawSum S.toSourceTestCurvePredata Λ.toSourceTestCurvePredata r) hu₀ univ :=
      sourceTestCurveRawSum_mass_positive omega S Λ hrl
    have hu : (ofFixedModel n M).IsThetaPSH T
        (sourceTestCurveRawSum S.toSourceTestCurvePredata Λ.toSourceTestCurvePredata r) := by
      simpa only [hforms] using hu₀
    have hup : 0 < sourcePotentialNonPluripolarMeasure T
        (sourceTestCurveRawSum S.toSourceTestCurvePredata Λ.toSourceTestCurvePredata r) hu univ := by
      simpa only [hforms] using hup₀
    have hv := sourceTestCurveRawSum_thetaPSH Γ.toSourceTestCurvePredata D.toSourceTestCurvePredata hs.le
    have hvp := sourceTestCurveRawSum_mass_positive omega Γ D hs
    have hfixed := (SingularGlobalPOrder.sourcePEquivalent_iff_pEquivalentWith omega
      (atlasClosedFormToNative T)
      ((isThetaPSH_iff_nativeThetaPotential T _).mp hu)
      ((isThetaPSH_iff_nativeThetaPotential T _).mp hv) hup hvp).mp hequiv
    simpa only [sourceSingularityEnvelope_eq_native] using
      POrder.pEquivalentWith_iff_envelope_eq.mp hfixed

end SGPT.PSH.VariableComplexAtlas
