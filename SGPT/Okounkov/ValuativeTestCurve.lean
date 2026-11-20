import SGPT.Okounkov.TestCurve
import SGPT.Okounkov.PartialBodyDS
import SGPT.Okounkov.TranscendentalCoreAlgebra
import SGPT.PSH.SourceTestCurvePositiveMass
import SGPT.PSH.SourceTestCurveEnergy
import SGPT.PSH.SourceIModelTestCurves
import SGPT.Foundations.Analysis.Pending.SingularCanonicalSingularityIncreasing
import SGPT.Foundations.Analysis.Pending.QuasiEquisingularRationalScaling

/-!
# Okounkov test curves of test curves

Source: the book's `thm:Okountescurvex` (chapter *The theory of Okounkov bodies*, section
*Okounkov test curves*, lines 2287--2333); blueprint chapter `claude-okoun-val`.

Let `X` be a connected compact Kähler manifold of dimension `n = m + 1` with a smooth flag
`Y•` (an `OriginalFlagGeometry`), `θ` a closed smooth real `(1,1)`-form representing a big class
and `Γ ∈ TC(X, θ)_{>0}` a test curve (`def:testcur`, `SGPT.PSH.VariableComplexAtlas.SourceTestCurve`).
Then `τ ↦ Δ_{Y•}(θ, Γ_τ)` (bodies of `def:generalPOB`) is an Okounkov test curve
(`def:Otc`, `SGPT.Okounkov.TestCurve`) relative to `Δ_{Y•}(θ, Γ_{-∞})`
(`okounkovTestCurve`), and if `Γ ∈ TC^∞(X, θ; Γ_{-∞})`, then this Okounkov test curve is bounded
(`okounkovTestCurve_isBounded`).

## Proof

* decreasing: `Γ_τ' ≤ Γ_τ` for `τ ≤ τ'` and `thm:pobmain` (2);
* concavity (ROUTE CHANGE): the book uses the valuative characterization `thm:Deltapartialint`;
  here, for rational `a ∈ (0, 1)`,
  `a Δ(θ, φ) + (1 - a) Δ(θ, ψ) ⊆ Δ(aθ, aφ) + Δ((1 - a)θ, (1 - a)ψ) ⊆ Δ(θ, aφ + (1 - a)ψ)`
  (homogeneity of the partial bodies, `smul_generalPartialBody_subset`, and the
  superadditivity `thm:pobmain` (6)), then `aΓ_τ + (1 - a)Γ_τ' ≤ Γ_{aτ + (1 - a)τ'}` and
  `thm:pobmain` (2); real `a` by rational approximation from the side where the parameter is
  larger, and closedness of the bodies;
* `Δ(θ, Γ_τ) → Δ(θ, Γ_{-∞})` in the Hausdorff metric as `τ → -∞`: the increasing net `Γ_τ`
  converges in `d_S` to its regularized supremum `Γ_{-∞}` (`cor:incseqnppcont`), which has
  positive mass, and `thm:pobmain` (4).

The energy clause (`Γ ∈ TC¹ ⇒ Δ(θ, Γ) ∈ TC¹` with `E^{Γ_{-∞}}(Γ) = E(Δ(θ, Γ))`) is false as
printed: its proof uses `n! vol Δ(θ, Γ_τ) = ∫_X θ_{Γ_τ}^n`, while `thm:pobmain` (1) gives
`n! vol Δ(θ, Γ_τ) = vol(θ, Γ_τ) = ∫_X (θ + dd^c P_θ[Γ_τ]_𝓘)^n`, which differs from
`∫_X θ_{Γ_τ}^n` when the model potential `Γ_τ` is not `𝓘`-model (blueprint
`claude-okoun-val:okountescurvex-energy-erratum`, with a counterexample on `ℙ¹`). The corrected
clause for `𝓘`-model test curves is `okounkovTestCurve_energy_eq_of_iModel` and
`okounkovTestCurve_hasFiniteEnergy_of_iModel`.
-/

set_option autoImplicit false

noncomputable section

universe u

namespace SGPT.Okounkov.Valuative

open Set Filter Metric
open scoped Topology Pointwise NNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.ThetaPshConvexCombination
open SGPT.Foundations.Analysis.Pending.ThetaPshL1Topology
open SGPT.Foundations.Analysis.Pending.DiagonalMass
open SGPT.PSH SGPT.Okounkov.TranscendentalCore SGPT.Okounkov.TranscendentalPartial
open SGPT.Okounkov.PartialBody

/-! ### Homogeneity of partial Okounkov bodies -/

section Scaling

variable {m : ℕ} {F : OriginalFlagGeometry.{u} (m + 1)}

/-- `(q⁻¹ : EReal) (q x) = x` for `q > 0`. -/
theorem ereal_inv_mul_mul' {q : ℝ} (hq : 0 < q) (x : EReal) :
    ((q⁻¹ : ℝ) : EReal) * ((q : EReal) * x) = x := by
  rw [← mul_assoc, ← EReal.coe_mul, inv_mul_cancel₀ hq.ne', EReal.coe_one, one_mul]

/-- A Kähler approximation of `T` scales to one of `q T`, `q ∈ ℚ_{>0}`. -/
theorem isKahlerQEA_rat_smul {θ : ClosedRealOneOneForm (m + 1) F.carrier}
    {φ : F.carrier → EReal} {U : ℕ → F.carrier → EReal} (hU : IsKahlerQEA θ φ U) {q : ℚ}
    (hq : 0 < q) :
    IsKahlerQEA ((q : ℝ) • θ) (fun x => ((q : ℝ) : EReal) * φ x)
      (fun j x => ((q : ℝ) : EReal) * U j x) := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  obtain ⟨ω, ε, hnat⟩ := native_of_sourceQuasiEquisingularApproximation hU.1
  refine ⟨sourceQuasiEquisingularApproximation_of_native
    (QuasiEquisingularRationalScaling.isQuasiEquisingularApproximation_pos_rat_smul hnat hq),
    fun j => ⟨⟨isThetaPshPotential_nonneg_smul (hU.2 j).1.1 hq'.le,
      hasAnalyticSingularities_nonneg_rat_smul (hU.2 j).1.2 hq.le⟩, ?_⟩⟩
  obtain ⟨κ, hκ⟩ := (hU.2 j).2
  refine ⟨KahlerBackground.smul hq' κ, ?_⟩
  have h := isThetaPshPotential_nonneg_smul hκ hq'.le
  rwa [KahlerBackground.smul_form, ← smul_sub]

/-- `q Δ(ξ; R) ⊆ Δ(q ξ; q R)` for the DRWNXZ partial bodies, `q ∈ ℚ_{>0}`. -/
theorem smul_partialOkounkovBody_subset (θ : ClosedRealOneOneForm (m + 1) F.carrier)
    (ψ : F.carrier → EReal) {q : ℚ} (hq : 0 < q) :
    (q : ℝ) • partialOkounkovBody F θ ψ ⊆
      partialOkounkovBody F ((q : ℝ) • θ) (fun x => ((q : ℝ) : EReal) * ψ x) := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have h := partialOkounkovBody_smul_subset θ (fun x => ((q : ℝ) : EReal) * ψ x)
    (inv_pos.mpr hq)
  have hfun : (fun x => (((q⁻¹ : ℚ) : ℝ) : EReal) * (((q : ℝ) : EReal) * ψ x)) = ψ := by
    funext x
    rw [Rat.cast_inv]
    exact ereal_inv_mul_mul' hq' (ψ x)
  rw [hfun, Rat.cast_inv, inv_inv] at h
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨y, hy, hyx⟩ := h hx
  have : (q : ℝ) • x = y := by
    rw [← hyx, smul_smul, mul_inv_cancel₀ hq'.ne', one_smul]
  show (q : ℝ) • x ∈ _
  rw [this]
  exact hy

/-- `q Δ(T) ⊆ Δ(q T)` for a Kähler current `T`, `q ∈ ℚ_{>0}` (`def:POBKahcurr`). -/
theorem smul_kahlerPartialBody_subset {θ : ClosedRealOneOneForm (m + 1) F.carrier}
    {φ : F.carrier → EReal} (hφ : IsKahlerCurrentPotential θ φ) {q : ℚ} (hq : 0 < q) :
    (q : ℝ) • kahlerPartialBody F θ φ ⊆
      kahlerPartialBody F ((q : ℝ) • θ) (fun x => ((q : ℝ) : EReal) * φ x) := by
  obtain ⟨U, hU⟩ := exists_isKahlerQEA hφ
  rw [kahlerPartialBody_eq_iInter hU, kahlerPartialBody_eq_iInter (isKahlerQEA_rat_smul hU hq)]
  rintro _ ⟨x, hx, rfl⟩
  rw [mem_iInter] at hx ⊢
  exact fun j => smul_partialOkounkovBody_subset θ (U j) hq ⟨x, hx j, rfl⟩

/-- **Homogeneity** `q Δ(T) ⊆ Δ(q T)` for `T ∈ 𝒵₊(X, α)`, `q ∈ ℚ_{>0}` (`def:generalPOB`). -/
theorem smul_generalPartialBody_subset {θ : ClosedRealOneOneForm (m + 1) F.carrier}
    {φ : F.carrier → EReal} (hφ : IsThetaPshPotential θ.val φ) {q : ℚ} (hq : 0 < q) :
    (q : ℝ) • generalPartialBody F θ φ ⊆
      generalPartialBody F ((q : ℝ) • θ) (fun x => ((q : ℝ) : EReal) * φ x) := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  rw [generalPartialBody_eq_iInter_pos hφ,
    generalPartialBody_eq_iInter_pos (isThetaPshPotential_nonneg_smul hφ hq'.le)]
  rintro _ ⟨x, hx, rfl⟩
  rw [mem_iInter₂] at hx ⊢
  intro ε hε
  have hεq : 0 < ε / q := div_pos hε hq'
  have h := smul_kahlerPartialBody_subset (isKahlerCurrentPotential_add_smul hφ F.omega hεq) hq
    ⟨x, hx _ hεq, rfl⟩
  have hform : (q : ℝ) • (θ + (ε / q) • F.omega.form) = (q : ℝ) • θ + ε • F.omega.form := by
    rw [smul_add, smul_smul, mul_div_cancel₀ _ hq'.ne']
  rwa [hform] at h

/-- **Rational concavity**: `a Δ(θ, φ) + (1 - a) Δ(θ, ψ) ⊆ Δ(θ, aφ + (1 - a)ψ)` for
`a ∈ ℚ ∩ (0, 1)` (homogeneity and `thm:pobmain` (6)). -/
theorem convexComb_mem_generalPartialBody {θ : ClosedRealOneOneForm (m + 1) F.carrier}
    {φ ψ : F.carrier → EReal} (hφ : IsThetaPshPotential θ.val φ)
    (hψ : IsThetaPshPotential θ.val ψ) {a : ℚ} (ha0 : 0 < a) (ha1 : a < 1)
    {x y : Fin (m + 1) → ℝ} (hx : x ∈ generalPartialBody F θ φ)
    (hy : y ∈ generalPartialBody F θ ψ) :
    (a : ℝ) • x + (1 - (a : ℝ)) • y ∈ generalPartialBody F θ (convexComb (a : ℝ) φ ψ) := by
  have hb : (0 : ℚ) < 1 - a := sub_pos.mpr ha1
  have hcast : (((1 - a : ℚ)) : ℝ) = 1 - (a : ℝ) := by push_cast; ring
  have h1 := smul_generalPartialBody_subset hφ ha0 ⟨x, hx, rfl⟩
  have h2 := smul_generalPartialBody_subset hψ hb ⟨y, hy, rfl⟩
  have ha' : (0 : ℝ) ≤ a := by exact_mod_cast ha0.le
  have hb' : (0 : ℝ) ≤ ((1 - a : ℚ) : ℝ) := by exact_mod_cast hb.le
  have h3 := generalPartialBody_add_subset (isThetaPshPotential_nonneg_smul hφ ha')
    (isThetaPshPotential_nonneg_smul hψ hb') ⟨_, h1, _, h2, rfl⟩
  have hform : (a : ℝ) • θ + ((1 - a : ℚ) : ℝ) • θ = θ := by
    rw [hcast, ← add_smul, add_sub_cancel, one_smul]
  rw [hform, hcast] at h3
  exact h3

end Scaling

/-! ### The Okounkov test curve -/

section TestCurve

open SGPT.PSH.VariableComplexAtlas

variable {m : ℕ} {F : OriginalFlagGeometry.{u} (m + 1)} [MeasurableSpace F.carrier]

/-- The test curve `Γ` read in the native potentials of `θ` (`atlasClosedFormToNative θ`). -/
abbrev nativeSlice {θ : AtlasClosedRealOneOneForm (ofFixedModel (m + 1) F.carrier)}
    (Γ : SourceTestCurve θ) (τ : Iio Γ.max) : ThetaPshL1 (atlasClosedFormToNative θ).val :=
  ⟨Γ.potential τ, Γ.native_thetaPSH τ⟩

/-- `Γ_{-∞}` read in the native potentials of `θ`. -/
abbrev nativeLimit {θ : AtlasClosedRealOneOneForm (ofFixedModel (m + 1) F.carrier)}
    (Γ : SourceTestCurve θ) : ThetaPshL1 (atlasClosedFormToNative θ).val :=
  ⟨sourceTestCurveLimit Γ.toSourceTestCurvePredata,
    (isThetaPSH_iff_nativeThetaPotential θ _).mp Γ.limit_thetaPSH⟩

variable {θ : AtlasClosedRealOneOneForm (ofFixedModel (m + 1) F.carrier)}

/-- `Δ(θ, Γ_τ) ⊆ Δ(θ, Γ_σ)` for `σ ≤ τ` (`thm:pobmain` (2)). -/
theorem generalPartialBody_testCurve_antitone
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    (Γ : SourceTestCurve θ) {σ τ : Iio Γ.max} (h : σ ≤ τ) :
    generalPartialBody F (atlasClosedFormToNative θ) (Γ.potential τ) ⊆
      generalPartialBody F (atlasClosedFormToNative θ) (Γ.potential σ) :=
  (generalPartialBody_subset_of_pointwise_le (Γ.native_thetaPSH τ) (Γ.native_thetaPSH σ)
    (fun x => Γ.antitone x h) hbig).1

/-- **Real concavity of `τ ↦ Δ(θ, Γ_τ)`**: for `a ∈ [0, 1]`,
`a Δ(θ, Γ_s) + (1 - a) Δ(θ, Γ_t) ⊆ Δ(θ, Γ_{as + (1 - a)t})`. -/
theorem convexComb_mem_generalPartialBody_testCurve
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    (Γ : SourceTestCurve θ) (s t : Iio Γ.max) {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    {x y : Fin (m + 1) → ℝ} (hx : x ∈ generalPartialBody F (atlasClosedFormToNative θ)
      (Γ.potential s))
    (hy : y ∈ generalPartialBody F (atlasClosedFormToNative θ) (Γ.potential t)) :
    a • x + (1 - a) • y ∈ generalPartialBody F (atlasClosedFormToNative θ)
      (Γ.potential ⟨a * (s : ℝ) + (1 - a) * (t : ℝ),
        (convex_Iio Γ.max) s.property t.property ha0 (sub_nonneg.mpr ha1) (by ring)⟩) := by
  set θn := atlasClosedFormToNative θ
  -- the parameter as a function of the weight
  let par : ∀ b : ℝ, 0 ≤ b → b ≤ 1 → Iio Γ.max := fun b hb0 hb1 =>
    ⟨b * (s : ℝ) + (1 - b) * (t : ℝ),
      (convex_Iio Γ.max) s.property t.property hb0 (sub_nonneg.mpr hb1) (by ring)⟩
  -- rational weights
  have hrat : ∀ b : ℚ, 0 < b → b < 1 → ∀ (hb0 : (0 : ℝ) ≤ b) (hb1 : (b : ℝ) ≤ 1),
      (b : ℝ) • x + (1 - (b : ℝ)) • y ∈ generalPartialBody F θn (Γ.potential (par b hb0 hb1)) := by
    intro b hb0 hb1 hb0' hb1'
    have hb0R : (0 : ℝ) < b := by exact_mod_cast hb0
    have hb1R : (b : ℝ) < 1 := by exact_mod_cast hb1
    have h := convexComb_mem_generalPartialBody (Γ.native_thetaPSH s) (Γ.native_thetaPSH t)
      hb0 hb1 hx hy
    have hle := Γ.toSourceTestCurvePredata.convexComb_le s t hb0R hb1R
    exact (generalPartialBody_subset_of_pointwise_le
      (isThetaPshPotential_convexComb (Γ.native_thetaPSH s) (Γ.native_thetaPSH t) hb0R hb1R)
      (Γ.native_thetaPSH _) hle hbig).1 h
  -- the endpoint cases
  have key : ∀ (σ : ℝ) (hσ : σ ∈ Iio Γ.max) (r : Iio Γ.max), σ = r →
      Γ.potential ⟨σ, hσ⟩ = Γ.potential r := by
    rintro σ hσ r rfl
    rfl
  rcases ha0.lt_or_eq with ha0' | ha0'
  swap
  · subst ha0'
    rw [key _ _ t (by ring), zero_smul, zero_add, sub_zero, one_smul]
    exact hy
  rcases ha1.lt_or_eq with ha1' | ha1'
  swap
  · subst ha1'
    rw [key _ _ s (by ring), one_smul, sub_self, zero_smul, add_zero]
    exact hx
  -- `0 < a < 1`
  have hclosed := isClosed_generalPartialBody θn (Γ.potential (par a ha0 ha1))
  rw [← hclosed.closure_eq, Metric.mem_closure_iff]
  intro ε hε
  set D : ℝ := dist x y + 1 with hD
  have hDpos : 0 < D := by positivity
  have hδ : 0 < min (ε / D) (min a (1 - a)) := lt_min (div_pos hε hDpos) (lt_min ha0' (by linarith))
  -- a rational weight on the correct side of `a`
  rcases le_total (s : ℝ) t with hst | hst
  · -- `s ≤ t`: take `b ≤ a`, then `par b ≥ par a`
    obtain ⟨b, hb1, hb2⟩ := exists_rat_btwn (sub_lt_self a hδ)
    have hbpos : (0 : ℝ) < b := by
      have := min_le_right (ε / D) (min a (1 - a))
      have := min_le_left a (1 - a)
      linarith
    have hblt1 : (b : ℝ) < 1 := by linarith
    have hb0 : (0 : ℚ) < b := by exact_mod_cast hbpos
    have hb1 : b < (1 : ℚ) := by exact_mod_cast hblt1
    have hmem := hrat b hb0 hb1 hbpos.le hblt1.le
    have hsub := generalPartialBody_testCurve_antitone hbig Γ (σ := par a ha0 ha1)
      (τ := par b hbpos.le hblt1.le) (by
        change a * (s : ℝ) + (1 - a) * (t : ℝ) ≤ (b : ℝ) * (s : ℝ) + (1 - (b : ℝ)) * (t : ℝ)
        nlinarith)
    refine ⟨_, hsub hmem, ?_⟩
    have heq : a • x + (1 - a) • y - ((b : ℝ) • x + (1 - (b : ℝ)) • y) =
        (a - b) • (x - y) := by module
    rw [dist_eq_norm, heq, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith), ← dist_eq_norm]
    have hab : a - b < ε / D := by
      have := min_le_left (ε / D) (min a (1 - a))
      linarith
    calc (a - b) * dist x y ≤ (a - b) * D := by
          apply mul_le_mul_of_nonneg_left (by linarith) (by linarith)
      _ < ε / D * D := by apply mul_lt_mul_of_pos_right hab hDpos
      _ = ε := div_mul_cancel₀ ε hDpos.ne'
  · -- `t ≤ s`: take `b ≥ a`, then `par b ≥ par a`
    obtain ⟨b, hb1, hb2⟩ := exists_rat_btwn (lt_add_of_pos_right a hδ)
    have hblt1 : (b : ℝ) < 1 := by
      have := min_le_right (ε / D) (min a (1 - a))
      have := min_le_right a (1 - a)
      linarith
    have hbpos : (0 : ℝ) < b := by linarith
    have hb0 : (0 : ℚ) < b := by exact_mod_cast hbpos
    have hb1 : b < (1 : ℚ) := by exact_mod_cast hblt1
    have hmem := hrat b hb0 hb1 hbpos.le hblt1.le
    have hsub := generalPartialBody_testCurve_antitone hbig Γ (σ := par a ha0 ha1)
      (τ := par b hbpos.le hblt1.le) (by
        change a * (s : ℝ) + (1 - a) * (t : ℝ) ≤ (b : ℝ) * (s : ℝ) + (1 - (b : ℝ)) * (t : ℝ)
        nlinarith)
    refine ⟨_, hsub hmem, ?_⟩
    have heq : a • x + (1 - a) • y - ((b : ℝ) • x + (1 - (b : ℝ)) • y) =
        ((b : ℝ) - a) • (y - x) := by module
    rw [dist_eq_norm, heq, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith),
      ← dist_eq_norm, dist_comm]
    have hab : (b : ℝ) - a < ε / D := by
      have := min_le_left (ε / D) (min a (1 - a))
      linarith
    calc ((b : ℝ) - a) * dist x y ≤ ((b : ℝ) - a) * D := by
          apply mul_le_mul_of_nonneg_left (by linarith) (by linarith)
      _ < ε / D * D := by apply mul_lt_mul_of_pos_right hab hDpos
      _ = ε := div_mul_cancel₀ ε hDpos.ne'

/-- The Euclidean copy commutes with convex combinations. -/
theorem euclideanImage_convexComb {k : ℕ} {S T : Set (Fin k → ℝ)} (a b : ℝ) :
    a • TranscendentalMain.euclideanImage S + b • TranscendentalMain.euclideanImage T =
      TranscendentalMain.euclideanImage (a • S + b • T) := by
  unfold TranscendentalMain.euclideanImage
  rw [Set.image_add, image_smul_set, image_smul_set]

/-- **`Δ(θ, Γ_τ) → Δ(θ, Γ_{-∞})` as `τ → -∞`** (Hausdorff metric): the increasing net `Γ_τ`
converges in `d_S` to `Γ_{-∞}` (`cor:incseqnppcont`), which has positive mass (`def:testcur`),
and `thm:pobmain` (4). -/
theorem tendsto_partialConvexBody_testCurve [BorelSpace F.carrier]
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    (Γ : SourceTestCurve θ) :
    Tendsto (fun τ : Iio Γ.max => partialConvexBody F (atlasClosedFormToNative θ) (nativeSlice Γ τ))
      atBot (𝓝 (partialConvexBody F (atlasClosedFormToNative θ) (nativeLimit Γ))) := by
  set θn := atlasClosedFormToNative θ
  change Tendsto (fun τ : OrderDual (Iio Γ.max) =>
    partialConvexBody F θn (nativeSlice Γ (OrderDual.ofDual τ))) atTop _
  have : Nonempty (OrderDual (Iio Γ.max)) :=
    ⟨OrderDual.toDual ⟨Γ.max - 1, show Γ.max - 1 < Γ.max by linarith⟩⟩
  have hmono : Monotone fun τ : OrderDual (Iio Γ.max) =>
      (nativeSlice Γ (OrderDual.ofDual τ)).val := by
    intro a b hab x
    exact Γ.antitone x hab
  have hT := SingularCanonicalSingularityIncreasing.tendsto_native_of_monotone_uniformlyBounded
    F.omega θn hbig (fun τ : OrderDual (Iio Γ.max) => nativeSlice Γ (OrderDual.ofDual τ)) hmono
    (C := 0) (fun τ x => by
      have h := Γ.toSourceTestCurvePredata.le_zero (OrderDual.ofDual τ) x
      simpa using h)
  have hU : (⟨uscRegularization (⨆ τ : OrderDual (Iio Γ.max),
      (nativeSlice Γ (OrderDual.ofDual τ)).val),
      IncreasingMixedDirectedNets.isThetaPshPotential_regularized_of_uniformlyBounded
        (fun τ => (nativeSlice Γ (OrderDual.ofDual τ)).property)
        (C := 0) (fun τ x => by
          have h := Γ.toSourceTestCurvePredata.le_zero (OrderDual.ofDual τ) x
          simpa using h)⟩ :
        ThetaPshL1 θn.val) = nativeLimit Γ := by
    apply Subtype.ext
    change uscRegularization _ = SGPT.PSH.uscSup Γ.potential
    unfold SGPT.PSH.uscSup
    congr 1
    funext x
    exact iSup_apply
  rw [hU] at hT
  have hpos : HasPositivePotentialMass θn (nativeLimit Γ).val (nativeLimit Γ).property :=
    Γ.positiveLimitMass
  have h := tendsto_hausdorffDist_generalPartialBody (F := F) F.omega hbig atTop _ _ hpos hT
  refine tendsto_iff_dist_tendsto_zero.mpr (h.congr fun w => ?_)
  exact ConvexBody.hausdorffDist_coe (partialConvexBody F θn _) (partialConvexBody F θn _)

/-- **`thm:Okountescurvex`** (first assertion): for a test curve `Γ ∈ TC(X, θ)_{>0}` (`θ`
representing a big class), `(-∞, Γ_max) ∋ τ ↦ Δ_{Y•}(θ, Γ_τ)` is an Okounkov test curve
(`def:Otc`) relative to `Δ_{Y•}(θ, Γ_{-∞})`. -/
def okounkovTestCurve [BorelSpace F.carrier]
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    (Γ : SourceTestCurve θ) :
    TestCurve (partialConvexBody F (atlasClosedFormToNative θ) (nativeLimit Γ)) where
  max := Γ.max
  body τ := partialConvexBody F (atlasClosedFormToNative θ) (nativeSlice Γ τ)
  antitone s t hst := image_mono (generalPartialBody_testCurve_antitone hbig Γ hst)
  concave s t a ha ha1 := by
    rw [ConvexBody.coe_add, ConvexBody.coe_smul, ConvexBody.coe_smul, coe_partialConvexBody,
      coe_partialConvexBody, coe_partialConvexBody, euclideanImage_convexComb]
    refine image_mono ?_
    rintro _ ⟨_, ⟨x, hx, rfl⟩, _, ⟨y, hy, rfl⟩, rfl⟩
    exact convexComb_mem_generalPartialBody_testCurve hbig Γ s t ha ha1 hx hy
  limit := tendsto_partialConvexBody_testCurve hbig Γ

@[simp] theorem okounkovTestCurve_max [BorelSpace F.carrier]
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    (Γ : SourceTestCurve θ) : (okounkovTestCurve (F := F) hbig Γ).max = Γ.max := rfl

/-- The bodies of `okounkovTestCurve` are the partial Okounkov bodies `Δ_{Y•}(θ, Γ_τ)`. -/
theorem coe_okounkovTestCurve_body [BorelSpace F.carrier]
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    (Γ : SourceTestCurve θ) (τ : Iio Γ.max) :
    ((okounkovTestCurve (F := F) hbig Γ).body τ : Set (EuclideanSpace ℝ (Fin (m + 1)))) =
      TranscendentalMain.euclideanImage
        (generalPartialBody F (atlasClosedFormToNative θ) (Γ.potential τ)) := rfl

/-- **`thm:Okountescurvex`, bounded case**: if `Γ ∈ TC^∞(X, θ; φ)`, the Okounkov test curve
`Δ_{Y•}(θ, Γ)` is bounded (`Δ_{Y•}(θ, Γ_τ) = Δ_{Y•}(θ, Γ_{-∞})` for `τ` small). -/
theorem okounkovTestCurve_isBounded [BorelSpace F.carrier]
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    {φ : F.carrier → EReal} {hφ : SourceModelPotential θ φ} {Γ : SourceTestCurve θ}
    (hΓ : Γ ∈ SourceBoundedTestCurves θ φ hφ) :
    (okounkovTestCurve (F := F) hbig Γ).IsBounded := by
  obtain ⟨hbased, hbdd⟩ := hΓ
  change sourceTestCurveLimit Γ.toSourceTestCurvePredata = φ at hbased
  change ∀ᶠ τ in (atBot : Filter (Iio Γ.max)),
    partialConvexBody F (atlasClosedFormToNative θ) (nativeSlice Γ τ) =
      partialConvexBody F (atlasClosedFormToNative θ) (nativeLimit Γ)
  filter_upwards [hbdd] with τ hτ
  congr 1
  apply Subtype.ext
  change Γ.potential τ = sourceTestCurveLimit Γ.toSourceTestCurvePredata
  rw [hτ, hbased]

end TestCurve

/-! ### Energy -/

section Energy

open SGPT.PSH.VariableComplexAtlas MeasureTheory
open scoped ENNReal

variable {m : ℕ} {F : OriginalFlagGeometry.{u} (m + 1)} [MeasurableSpace F.carrier]
  [BorelSpace F.carrier] {θ : AtlasClosedRealOneOneForm (ofFixedModel (m + 1) F.carrier)}

omit [BorelSpace F.carrier] in
/-- The mass of an `𝓘`-model potential is its volume: `∫ θ_u^n = vol(θ, u)`. -/
theorem iVolume_eq_sourceMass_of_isIModel {u : F.carrier → EReal}
    (hu : (ofFixedModel (m + 1) F.carrier).IsThetaPSH θ u)
    (hI : IEnvelope.IsIModelPotential (atlasClosedFormToNative θ).val u) :
    iVolume (atlasClosedFormToNative θ)
        (LocalPotentials.closedRealOneOne_hasLocalPotentials (atlasClosedFormToNative θ)) u
        ((isThetaPSH_iff_nativeThetaPotential θ u).mp hu) =
      sourcePotentialNonPluripolarMeasure θ u hu univ := by
  have key : ∀ (v w : F.carrier → EReal)
      (hv : IsThetaPshPotential (atlasClosedFormToNative θ).val v)
      (hw : IsThetaPshPotential (atlasClosedFormToNative θ).val w), v = w →
      diagonalPotentialMass (atlasClosedFormToNative θ) v hv =
        diagonalPotentialMass (atlasClosedFormToNative θ) w hw := by
    rintro v w hv hw rfl
    rfl
  exact key _ _ _ _ hI.2.symm

/-- `n! vol Δ(θ, u) = ∫_X θ_u^n` for an `𝓘`-model potential `u` (`thm:pobmain` (1)). -/
theorem factorial_mul_volume_real_eq_of_isIModel {u : F.carrier → EReal}
    (hu : (ofFixedModel (m + 1) F.carrier).IsThetaPSH θ u)
    (hI : IEnvelope.IsIModelPotential (atlasClosedFormToNative θ).val u) :
    ((m + 1).factorial : ℝ) * volume.real (TranscendentalMain.euclideanImage
        (generalPartialBody F (atlasClosedFormToNative θ) u)) =
      (sourcePotentialNonPluripolarMeasure θ u hu univ).toReal := by
  rw [measureReal_def, volume_euclideanImage, volume_generalPartialBody_of_borelSpace
    ((isThetaPSH_iff_nativeThetaPotential θ u).mp hu), iVolume_eq_sourceMass_of_isIModel hu hI,
    ENNReal.toReal_div, ENNReal.toReal_natCast]
  have hf : ((m + 1).factorial : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  field_simp

/-- **`thm:Okountescurvex`, energy, corrected to `𝓘`-model test curves**: if
`Γ ∈ TC(X, θ; φ)` is an `𝓘`-model test curve (`Γ_τ` `𝓘`-model for every `τ`) and `φ = Γ_{-∞}` is
`𝓘`-model, then `E(Δ_{Y•}(θ, Γ)) = E^φ(Γ)` (`eq:Otestcurvenergy`, `eq:tcfiniteenergy`). The
printed statement for all test curves is false (blueprint
`claude-okoun-val:okountescurvex-energy-erratum`). -/
theorem okounkovTestCurve_energy_eq_of_iModel (ω : KahlerBackground (m + 1) F.carrier)
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    {φ : F.carrier → EReal} {hφ : SourceModelPotential θ φ} {Γ : SourceTestCurve θ}
    (hΓ : Γ ∈ SourceIModelTestCurves θ φ hφ)
    (hφI : IEnvelope.IsIModelPotential (atlasClosedFormToNative θ).val φ) :
    (okounkovTestCurve (F := F) hbig Γ).energy = sourceTestCurveEnergy ω hφ Γ hΓ.1 := by
  obtain ⟨hbased, hΓI⟩ := hΓ
  set K := okounkovTestCurve (F := F) hbig Γ with hK
  set c : ℝ := ((m + 1).factorial : ℝ) with hc
  -- the volumes of the bodies are the masses
  have hvolt : ∀ t : ℝ, t < Γ.max →
      c * volume.real ((K.bodyAt t : Set (EuclideanSpace ℝ (Fin (m + 1))))) =
        sourceTestCurveRealMassAt ω Γ t := by
    intro t ht
    have hbody : K.bodyAt t = K.body ⟨t, ht⟩ := by
      rw [TestCurve.bodyAt, dif_pos (show t < K.max from ht)]
    rw [hbody, sourceTestCurveRealMassAt_of_lt ω Γ ht]
    exact factorial_mul_volume_real_eq_of_isIModel (Γ.thetaPSH _) (hΓI _)
  have hvolΔ : c * volume.real ((partialConvexBody F (atlasClosedFormToNative θ) (nativeLimit Γ) :
      Set (EuclideanSpace ℝ (Fin (m + 1))))) =
        (sourcePotentialNonPluripolarMeasure θ φ hφ.thetaPSH univ).toReal := by
    have hlim : sourceTestCurveLimit Γ.toSourceTestCurvePredata = φ := hbased
    rw [coe_partialConvexBody]
    have h := factorial_mul_volume_real_eq_of_isIModel (θ := θ) (F := F) hφ.thetaPSH hφI
    change c * volume.real (TranscendentalMain.euclideanImage (generalPartialBody F
      (atlasClosedFormToNative θ) (sourceTestCurveLimit Γ.toSourceTestCurvePredata))) = _
    rw [hlim]
    exact h
  rw [TestCurve.energy_eq_deficit, sourceTestCurveEnergy]
  congr 1
  · congr 1
    change c * Γ.max * _ = Γ.max * _
    rw [← hvolΔ]
    ring
  · have hcE : ((((m + 1).factorial : ℕ)) : EReal) = ((((m + 1).factorial : ℕ) : ℝ≥0∞) : EReal) := by
      rw [← ENNReal.coe_natCast, EReal.coe_nnreal_eq_coe_real, NNReal.coe_natCast]
      rfl
    rw [hcE, ← EReal.coe_ennreal_mul, ← lintegral_const_mul' _ _ (ENNReal.natCast_ne_top _)]
    congr 1
    refine lintegral_congr_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Iio] with t ht
    have ht' : t < Γ.max := ht
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    congr 1
    change c * (_ - _) = _
    rw [mul_sub, hvolΔ, hvolt t ht']

/-- **`thm:Okountescurvex`, `TC¹` clause, for `𝓘`-model test curves**: if
`Γ ∈ TC¹(X, θ; φ)` is `𝓘`-model with `φ` `𝓘`-model, then `Δ_{Y•}(θ, Γ) ∈ TC¹(Δ_{Y•}(θ, φ))`. -/
theorem okounkovTestCurve_hasFiniteEnergy_of_iModel (ω : KahlerBackground (m + 1) F.carrier)
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    {φ : F.carrier → EReal} {hφ : SourceModelPotential θ φ} {Γ : SourceTestCurve θ}
    (hΓ : Γ ∈ SourceIModelTestCurves θ φ hφ)
    (hφI : IEnvelope.IsIModelPotential (atlasClosedFormToNative θ).val φ)
    (hE : Γ ∈ SourceFiniteEnergyTestCurves ω θ φ hφ) :
    (okounkovTestCurve (F := F) hbig Γ).HasFiniteEnergy := by
  obtain ⟨hb, hpos⟩ := hE
  unfold TestCurve.HasFiniteEnergy
  rw [okounkovTestCurve_energy_eq_of_iModel ω hbig hΓ hφI]
  exact hpos

end Energy

end SGPT.Okounkov.Valuative
