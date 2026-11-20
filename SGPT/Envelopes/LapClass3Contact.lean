import SGPT.Envelopes.LapClass3Hessian
import SGPT.Envelopes.DNTC11Mixed
import SGPT.Envelopes.LapClass2Contact
import SGPT.Envelopes.LapClassKahlerClass

/-!
# The Di Nezza–Trapani contact formula for `f ∈ C^{1,1̄}(X)` (all dimensions)

Lane CZ-LP (`claude-cz-lp`, node `czlp:contact`).  Book `thm:DNTcontact` for obstacles in the book's
class `C^{1,1̄}(X)` (continuous, bounded `ω`-Laplacian), with `θ_fⁿ = lapTopMeasure θ f`
(`LapClass3Measure`), in every dimension `n = m + 1`.

* `lapTopMeasure_restrict_eq_of_le` (**second-order contact**): if `g ≤ f` are in the class, then
  `𝟙_{g = f} θ_gⁿ = 𝟙_{g = f} θ_fⁿ`.  In every chart, `f - g ≥ 0` vanishes to second order at almost
  every point of `{g = f}` (LAP-CLASS2's `HasBoundedMetricLaplacian.ae_isLittleO`), so the Hessian
  density of `f - g` vanishes almost everywhere there (`CZLp.IsHessianDensityOn.ae_eq_zero_of_isLittleO`,
  the Lebesgue-point form of Stampacchia's lemma).
* `diagonalPotentialMeasure_restrict_contact_eq` (**`thm:DNTcontact`, diagonal case**): for
  `φ ∈ PSH(X, θ)` and `f ∈ C^{1,1̄}(X)` with `φ ≤ f`, `𝟙_{φ = f} θ_φⁿ = 𝟙_{φ = f} θ_fⁿ`.  The book's
  Step 3: `g = P_{θ + Aω}(f)` (`θ + Aω` Kähler) is `(θ + Aω)`-psh with bounded `ω`-Laplacian
  (LAP-CLASS, `prop:DR16_C11bar`), hence has bounded complex Hessian (`LapClass3Hessian`);
  `φ ≤ g ≤ f`, the bounded-Hessian contact formula (`DNTC11`) gives `𝟙_{φ = g} θ_φⁿ = 𝟙_{φ = g} θ_gⁿ`
  and second-order contact gives `𝟙_{g = f} θ_gⁿ = 𝟙_{g = f} θ_fⁿ`.
* `sourcePotentialNonPluripolarMeasure_restrict_contact_eq`: the same with the source objects.
* `globalMixedMeasure_restrict_mixedContact_toReal_eq`,
  `sourceMixedNonPluripolarMeasure_restrict_mixedContact_toReal_eq` (**mixed case**): with
  `θ_{1,f₁} ∧ ⋯ ∧ θ_{n,fₙ} := (1/n!) ∑_S (-1)^{n-|S|} (θ_S + ddᶜf_S)ⁿ` (`lapMixedReal`), by the
  book's Step 1 (polarization).
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory Metric
open scoped Topology ContDiff ENNReal

namespace SGPT.Envelopes.LapClass3

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.DiagonalMass SGPT.Foundations.Analysis.Pending.GlobalNonPluripolar
open SGPT.Foundations.Analysis.Pending.ManifoldTubePositivity
open SGPT.Foundations.Analysis.Pending.GlobalMultilinearExpansion
open SGPT.Envelopes.LapClass SGPT.Analysis.CZLp SGPT.Envelopes.DNTC11
open SGPT.Okounkov SGPT.Okounkov.TranscendentalWNReg SGPT.PSH.VariableComplexAtlas
open SGPT.Envelopes.DNT

variable {m : ℕ} {Y : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel (m + 1)) Y]
  [IsComplexManifold (m + 1) Y] [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y]

/-! ### Second-order contact -/

/-- **Second-order contact of two obstacles in `C^{1,1̄}(X)`**: if `g ≤ f`, then
`𝟙_{g = f} θ_gⁿ = 𝟙_{g = f} θ_fⁿ`. -/
theorem lapTopMeasure_restrict_eq_of_le (w : KahlerBackground (m + 1) Y)
    (θ : ClosedRealOneOneForm (m + 1) Y) {f g : Y → ℝ} (hf : HasBoundedMetricLaplacian w f)
    (hg : HasBoundedMetricLaplacian w g) (hle : ∀ x, g x ≤ f x) :
    (lapTopMeasure θ g).restrict {x | g x = f x} = (lapTopMeasure θ f).restrict {x | g x = f x} := by
  classical
  set Z : Set Y := {x | g x = f x} with hZ
  have hZm : MeasurableSet Z := (isClosed_eq hg.1 hf.1).measurableSet
  have hu := hf.sub w hg
  have hu0 : ∀ x, 0 ≤ f x - g x := fun x => sub_nonneg.mpr (hle x)
  have hdf := hasHessianDensities_of_hasBoundedMetricLaplacian w hf
  have hdg := hasHessianDensities_of_hasBoundedMetricLaplacian w hg
  have hpatch : ∀ x : Y, ∃ N : Set Y, IsOpen N ∧ x ∈ N ∧
      ((lapTopMeasure θ g).restrict Z).restrict N = ((lapTopMeasure θ f).restrict Z).restrict N := by
    intro x
    set e := complexChartAt (n := m + 1) x with he
    have hxe : x ∈ e.val.source := mem_complexChartAt_source x
    have hz₀ : e.val x ∈ e.val.target := e.val.map_source hxe
    obtain ⟨W, ψ, hz₀W, hψ⟩ :=
      Pending.LocalPotentials.closedRealOneOne_hasLocalPotentials θ e (e.val x) hz₀
    obtain ⟨hF, hhF⟩ := hdf.exists_add e hψ.1 hψ.2.1 hψ.2.2.1
    obtain ⟨hG, hhG⟩ := hdg.exists_add e hψ.1 hψ.2.1 hψ.2.2.1
    -- the density of `f - g` vanishes almost everywhere on the contact set
    have hdiff : IsHessianDensityOn (fun z => f (e.val.symm z) - g (e.val.symm z))
        (fun z => hF z - hG z) W :=
      (hhF.sub hhG).congr_fun (by funext z; ring)
    have hzero := hdiff.ae_eq_zero_of_isLittleO fun z _ => hu0 _
    have hlo := hu.ae_isLittleO w hu0 e
    have hae : ∀ᵐ z, z ∈ W → f (e.val.symm z) - g (e.val.symm z) = 0 → hF z = hG z := by
      filter_upwards [hzero, hlo] with z h1 h2 hzW hz0
      have := h1 hzW hz0 (h2 (hψ.2.1 hzW) hz0)
      exact sub_eq_zero.mp this
    set N := e.val.source ∩ e.val ⁻¹' W with hN
    refine ⟨N, e.val.isOpen_inter_preimage hψ.1, ⟨hxe, hz₀W⟩, ?_⟩
    ext S hS
    rw [Measure.restrict_apply hS, Measure.restrict_apply hS, Measure.restrict_apply (hS.inter
      (e.val.isOpen_inter_preimage hψ.1).measurableSet), Measure.restrict_apply (hS.inter
      (e.val.isOpen_inter_preimage hψ.1).measurableSet)]
    have hSN : S ∩ N ∩ Z ⊆ e.val.source := fun y hy => hy.1.2.1
    set K := e.val '' (S ∩ N ∩ Z) with hK
    have hKm : MeasurableSet K := by
      have := measurableSet_chart_piece e hψ.1 (hS.inter hZm)
      have hset : (S ∩ Z) ∩ (e.val.source ∩ e.val ⁻¹' W) = S ∩ N ∩ Z := by
        ext y; simp only [mem_inter_iff, hN]; tauto
      rwa [hset] at this
    have hKW : K ⊆ W := by
      rintro _ ⟨y, hy, rfl⟩
      exact hy.1.2.2
    have hSK : S ∩ N ∩ Z = e.val.symm '' K := (e.val.symm_image_image_of_subset_source hSN).symm
    rw [hSK, lapTopMeasure_image_eq w θ hg hψ hhG hKm hKW,
      lapTopMeasure_image_eq w θ hf hψ hhF hKm hKW]
    refine setLIntegral_congr_fun_ae hKm ?_
    filter_upwards [hae] with z hz hzK
    obtain ⟨y, hy, rfl⟩ := hzK
    have hyZ : g y = f y := hy.2
    have hy0 : f (e.val.symm (e.val y)) - g (e.val.symm (e.val y)) = 0 := by
      rw [e.val.left_inv hy.1.2.1, hyZ, sub_self]
    rw [hessDensity, hessDensity, hz (hy.1.2.2) hy0]
  choose N hNo hxN hN using hpatch
  exact GlobalSlotStokes.measure_eq_of_restrict_eq_of_openCover (fun x => N x) hNo
    (fun x => ⟨x, hxN x⟩) hN

/-! ### The contact formula -/

variable [ConnectedSpace Y]

/-- **The Di Nezza–Trapani contact formula** (book `thm:DNTcontact`, diagonal case `θᵢ = θ`,
`φᵢ = φ`, `fᵢ = f`) **for the book's `C^{1,1̄}(X)`**, every dimension: `X` compact connected with a
Kähler form `ω`, `θ` a closed real `(1,1)`-form, `φ ∈ PSH(X, θ)`, `f` continuous with bounded
`ω`-Laplacian, `φ ≤ f`, `E = {φ = f}`: `𝟙_E ⟨(θ + ddᶜφ)ⁿ⟩ = 𝟙_E θ_fⁿ`, `θ_fⁿ = lapTopMeasure θ f`. -/
theorem diagonalPotentialMeasure_restrict_contact_eq (w : KahlerBackground (m + 1) Y)
    (θ : ClosedRealOneOneForm (m + 1) Y) {u : Y → EReal} (hu : IsThetaPshPotential θ.val u)
    {f : Y → ℝ} (hf : HasBoundedMetricLaplacian w f) (hle : ∀ x, u x ≤ (f x : EReal)) :
    (diagonalPotentialMeasure θ u hu).restrict {x | u x = (f x : EReal)} =
      (lapTopMeasure θ f).restrict {x | u x = (f x : EReal)} := by
  classical
  obtain ⟨A, hA, hK⟩ := KahlerDomination.exists_pos_isKahler_add_smul w θ
  set θ' := θ + A • w.form with hθ'
  set B : KahlerBackground (m + 1) Y := ⟨θ', hK⟩ with hB
  have hu' : IsThetaPshPotential θ'.val u :=
    ⟨NefBoundedMixedMass.thetaPlurisubharmonic_add_of_isSemipositive hu.1
      (NefBoundedMixedMass.isSemipositive_smul w.isSemipositive hA.le), hu.2⟩
  -- the envelope `g = P_{θ'}(f)`
  obtain ⟨hreal, hgcls⟩ := envelope_min_hasBoundedMetricLaplacian_gen w B hf hf
  simp only [min_self] at hreal hgcls
  set g : Y → ℝ := envelopeReal B.form f with hgdef
  have hP : IsThetaPshPotential θ'.val (rooftopEnvelope θ'.val fun x => (f x : EReal)) :=
    TranscendentalWNReg.isThetaPshPotential_rooftopEnvelope_of_continuous w θ' hf.1 hu'
  have hgeq : (rooftopEnvelope θ'.val fun x => (f x : EReal)) = fun x => (g x : EReal) :=
    funext hreal
  have hgpsh : IsThetaPshPotential θ'.val (fun x => (g x : EReal)) := hgeq ▸ hP
  have hgf : ∀ x, g x ≤ f x := fun x => by
    have := TranscendentalWNReg.rooftopEnvelope_le_of_isThetaPshPotential hf.1 hP x
    rw [hreal x] at this
    exact EReal.coe_le_coe_iff.mp this
  have hug : ∀ x, u x ≤ (g x : EReal) := fun x => by
    have := le_rooftopEnvelope hu' (quasiEverywhere_of_forall hle) x
    rwa [hreal x] at this
  have hgB : HasBoundedComplexHessian (n := m + 1) g :=
    hasBoundedComplexHessian_of_isThetaPshPotential w θ' hgcls hgpsh
  -- the two contact formulas
  have h1 := DNTC11.diagonalPotentialMeasure_restrict_contact_eq w θ hu hgB hug
  rw [← lapTopMeasure_eq_c11TopMeasure (Nat.succ_pos m) w θ hgB] at h1
  have h2 := lapTopMeasure_restrict_eq_of_le w θ hf hgcls hgf
  set E : Set Y := {x | u x = (f x : EReal)} with hE
  have hE1 : E ⊆ {x | u x = (g x : EReal)} := fun x hx => by
    have h₁ := hug x
    have h₂ : (g x : EReal) ≤ f x := EReal.coe_le_coe_iff.mpr (hgf x)
    exact le_antisymm h₁ (hx ▸ h₂)
  have hE2 : E ⊆ {x | g x = f x} := fun x hx => by
    have h₁ := hug x
    have h₂ : (g x : EReal) ≤ f x := EReal.coe_le_coe_iff.mpr (hgf x)
    have : (g x : EReal) = f x := le_antisymm h₂ (hx ▸ h₁)
    exact EReal.coe_eq_coe_iff.mp this
  calc (diagonalPotentialMeasure θ u hu).restrict E
      = ((diagonalPotentialMeasure θ u hu).restrict {x | u x = (g x : EReal)}).restrict E := by
        rw [Measure.restrict_restrict_of_subset hE1]
    _ = ((lapTopMeasure θ g).restrict {x | u x = (g x : EReal)}).restrict E := by rw [h1]
    _ = ((lapTopMeasure θ g).restrict {x | g x = f x}).restrict E := by
        rw [Measure.restrict_restrict_of_subset hE1, Measure.restrict_restrict_of_subset hE2]
    _ = ((lapTopMeasure θ f).restrict {x | g x = f x}).restrict E := by rw [h2]
    _ = (lapTopMeasure θ f).restrict E := by rw [Measure.restrict_restrict_of_subset hE2]

/-- **`thm:DNTcontact`, diagonal case, source-facing form**, for `f ∈ C^{1,1̄}(X)`, every dimension. -/
theorem sourcePotentialNonPluripolarMeasure_restrict_contact_eq (w : KahlerBackground (m + 1) Y)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel (m + 1) Y)) {u : Y → EReal}
    (hu : (ofFixedModel (m + 1) Y).IsThetaPSH θ u) {f : Y → ℝ}
    (hf : HasBoundedMetricLaplacian w f) (hle : ∀ x, u x ≤ (f x : EReal)) :
    (sourcePotentialNonPluripolarMeasure θ u hu).restrict {x | u x = (f x : EReal)} =
      (lapTopMeasure (atlasClosedFormToNative θ) f).restrict {x | u x = (f x : EReal)} :=
  diagonalPotentialMeasure_restrict_contact_eq w (atlasClosedFormToNative θ)
    ((isThetaPSH_iff_nativeThetaPotential θ u).mp hu) hf hle

/-! ### Mixed products -/

section Mixed

omit [ConnectedSpace Y] in
/-- The class `C^{1,1̄}_ω(X)` is closed under sums. -/
theorem hasBoundedMetricLaplacian_add (w : KahlerBackground (m + 1) Y) {f v : Y → ℝ}
    (hf : HasBoundedMetricLaplacian w f) (hv : HasBoundedMetricLaplacian w v) :
    HasBoundedMetricLaplacian w (fun x => f x + v x) := by
  obtain ⟨hfc, Mf, hfLE, hfGE⟩ := hf
  obtain ⟨hvc, Mv, hvLE, hvGE⟩ := hv
  have hsplit : ∀ χ : Y → ℝ, ChartSmooth (n := m + 1) χ →
      ∫ y, (f y + v y) * KahlerLaplacianChart.laplacian w.form.val χ y
          ∂(IntegrationCurrent.kahlerVolume w) =
        (∫ y, f y * KahlerLaplacianChart.laplacian w.form.val χ y
          ∂(IntegrationCurrent.kahlerVolume w)) +
          ∫ y, v y * KahlerLaplacianChart.laplacian w.form.val χ y
            ∂(IntegrationCurrent.kahlerVolume w) := by
    intro χ hχ
    have hL := continuous_laplacian_of_chartSmooth w.isKahler.1 hχ
    refine Eq.trans ?_ (integral_add (integral_continuous (hfc.mul hL) _)
      (integral_continuous (hvc.mul hL) _))
    exact integral_congr_ae (Eventually.of_forall fun y => by simp only; ring)
  refine ⟨hfc.add hvc, Mf + Mv, fun χ hχ hχ0 => ?_, fun χ hχ hχ0 => ?_⟩
  · rw [hsplit χ hχ, add_mul]
    have := hfLE χ hχ hχ0
    have := hvLE χ hχ hχ0
    linarith
  · rw [hsplit χ hχ, neg_add, add_mul]
    have := hfGE χ hχ hχ0
    have := hvGE χ hχ hχ0
    linarith

omit [ConnectedSpace Y] in
theorem hasBoundedMetricLaplacian_finset_sum (w : KahlerBackground (m + 1) Y) {ι : Type*}
    (S : Finset ι) {f : ι → Y → ℝ} (hf : ∀ i, HasBoundedMetricLaplacian w (f i)) :
    HasBoundedMetricLaplacian w (fun x => ∑ i ∈ S, f i x) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      simpa only [Finset.sum_empty] using
        hasBoundedMetricLaplacian_of_chartSmooth w
          (ProductTestForms.chartSmooth_const (n := m + 1) (M := Y) 0)
  | insert j S hj ih =>
      have h := hasBoundedMetricLaplacian_add w (hf j) ih
      have heq : (fun x => f j x + ∑ i ∈ S, f i x) = fun x => ∑ i ∈ insert j S, f i x := by
        funext x
        rw [Finset.sum_insert hj]
      exact heq ▸ h

/-- **The mixed Monge–Ampère measure `θ_{1,f₁} ∧ ⋯ ∧ θ_{n,fₙ}`** of obstacles in `C^{1,1̄}(X)`, as
a signed measure of the set `A`: the polarization `(1/n!) ∑_S (-1)^{n-|S|} (θ_S + ddᶜf_S)ⁿ(A)` of
the top powers `lapTopMeasure θ_S f_S` (`θ_S = ∑_{i∈S} θᵢ`, `f_S = ∑_{i∈S} fᵢ`). -/
def lapMixedReal (θ : Fin (m + 1) → ClosedRealOneOneForm (m + 1) Y) (f : Fin (m + 1) → Y → ℝ)
    (A : Set Y) : ℝ :=
  (((m + 1).factorial : ℝ))⁻¹ * ∑ S : Finset (Fin (m + 1)), (-1 : ℝ) ^ (m + 1 - S.card) *
    (lapTopMeasure (sumForm S (fun _ => (1 : ℝ)) θ) (fun x => ∑ i ∈ S, f i x) A).toReal

/-- **The Di Nezza–Trapani contact formula for mixed products** (book `thm:DNTcontact`) for obstacles
in `C^{1,1̄}(X)`, every dimension: `⟨θ_{1,φ₁} ∧ ⋯ ∧ θ_{n,φₙ}⟩(A ∩ E) = (θ_{1,f₁} ∧ ⋯ ∧ θ_{n,fₙ})(A ∩ E)`
for every measurable `A`, `E = ⋂ᵢ {φᵢ = fᵢ}`. -/
theorem globalMixedMeasure_restrict_mixedContact_toReal_eq (w : KahlerBackground (m + 1) Y)
    (θ : Fin (m + 1) → ClosedRealOneOneForm (m + 1) Y) {u : Fin (m + 1) → Y → EReal}
    (hu : ∀ i, IsThetaPshPotential (θ i).val (u i)) {f : Fin (m + 1) → Y → ℝ}
    (hf : ∀ i, HasBoundedMetricLaplacian w (f i)) (hle : ∀ i x, u i x ≤ (f i x : EReal))
    {A : Set Y} (hA : MeasurableSet A) :
    ((globalMixedMeasure θ u fun i => (hu i).1).restrict (mixedContactSet u f) A).toReal =
      lapMixedReal θ f (A ∩ mixedContactSet u f) := by
  classical
  set E := mixedContactSet u f with hE
  have hEm : MeasurableSet E := by
    rw [hE, mixedContactSet_eq_iInter]
    exact (isClosed_iInter fun i =>
      isClosed_contact_of_continuous (hu i).1 (hf i).1 (hle i)).measurableSet
  rw [Measure.restrict_apply hA]
  set μ : (Fin (m + 1) → Fin (m + 1)) → Measure Y := fun g =>
    globalMixedMeasure (fun j => θ (g j)) (fun j => u (g j)) (fun j => (hu (g j)).1) with hμ
  have hfin : ∀ g, μ g (A ∩ E) ≠ ⊤ := fun g => by
    have := globalMixedMeasure_isFiniteMeasure w (fun j => (hu (g j)).1)
    exact measure_ne_top _ _
  set d : (Fin (m + 1) → Fin (m + 1)) → ℝ := fun g => (μ g (A ∩ E)).toReal with hd
  have hS : ∀ S : Finset (Fin (m + 1)), ∑ g : Fin (m + 1) → Fin (m + 1) with ∀ j, g j ∈ S, d g =
      (lapTopMeasure (sumForm S (fun _ => (1 : ℝ)) θ) (fun x => ∑ i ∈ S, f i x)
        (A ∩ E)).toReal := by
    intro S
    have hfS := hasBoundedMetricLaplacian_finset_sum w S hf
    have hleS : ∀ x, sumPot S (fun _ => (1 : ℝ)) u x ≤ ((∑ i ∈ S, f i x : ℝ) : EReal) := by
      intro x
      simp only [sumPot, EReal.coe_one, one_mul]
      rw [ereal_coe_finset_sum]
      exact Finset.sum_le_sum fun i _ => hle i x
    have hES : E ⊆ {x | sumPot S (fun _ => (1 : ℝ)) u x = ((∑ i ∈ S, f i x : ℝ) : EReal)} := by
      intro x hx
      simp only [mem_ofPred_eq, sumPot, EReal.coe_one, one_mul]
      rw [ereal_coe_finset_sum]
      exact Finset.sum_congr rfl fun i _ => hx i
    have hdnt := diagonalPotentialMeasure_restrict_contact_eq w (sumForm S (fun _ => (1 : ℝ)) θ)
      (MixedProductIntegralPolarization.isThetaPshPotential_subsetSum hu S) hfS hleS
    have h2 := congrArg (fun ν : Measure Y => ν (A ∩ E)) hdnt
    simp only at h2
    rw [Measure.restrict_apply (hA.inter hEm), Measure.restrict_apply (hA.inter hEm),
      inter_eq_left.mpr (inter_subset_right.trans hES),
      MixedProductIntegralPolarization.diagonal_subsetSum_eq_sum_selected w hu S,
      Measure.finsetSum_apply] at h2
    rw [← h2, ENNReal.toReal_sum fun g _ => hfin g]
  have hperm : ∀ σ : Equiv.Perm (Fin (m + 1)), d σ = d id := by
    intro σ
    have h1 : μ σ = μ id := GlobalSlotPerm.globalMixedMeasure_perm (fun i => (hu i).1) σ
    simp only [hd, h1]
  have hpol := PolarizationAlgebra.sum_powerset_signed_eq_factorial_mul d hperm
  simp only [hS] at hpol
  have hn : (((m + 1).factorial : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (m + 1).factorial_ne_zero
  have hid : d id = (μ id (A ∩ E)).toReal := rfl
  have hμid : μ id = globalMixedMeasure θ u fun i => (hu i).1 := rfl
  rw [← hμid, ← hid, lapMixedReal, hpol, ← mul_assoc, inv_mul_cancel₀ hn, one_mul]

/-- The mixed measure of the obstacles is nonnegative on subsets of the common contact set. -/
theorem lapMixedReal_nonneg_of_mixedContact (w : KahlerBackground (m + 1) Y)
    (θ : Fin (m + 1) → ClosedRealOneOneForm (m + 1) Y) {u : Fin (m + 1) → Y → EReal}
    (hu : ∀ i, IsThetaPshPotential (θ i).val (u i)) {f : Fin (m + 1) → Y → ℝ}
    (hf : ∀ i, HasBoundedMetricLaplacian w (f i)) (hle : ∀ i x, u i x ≤ (f i x : EReal))
    {A : Set Y} (hA : MeasurableSet A) :
    0 ≤ lapMixedReal θ f (A ∩ mixedContactSet u f) := by
  rw [← globalMixedMeasure_restrict_mixedContact_toReal_eq w θ hu hf hle hA]
  exact ENNReal.toReal_nonneg

/-- **`thm:DNTcontact` for mixed products, source-facing form**, obstacles in `C^{1,1̄}(X)`. -/
theorem sourceMixedNonPluripolarMeasure_restrict_mixedContact_toReal_eq
    (w : KahlerBackground (m + 1) Y) (θ : Fin (m + 1) → AtlasClosedRealOneOneForm (ofFixedModel (m + 1) Y))
    {u : Fin (m + 1) → Y → EReal} (hu : ∀ i, (ofFixedModel (m + 1) Y).IsThetaPSH (θ i) (u i))
    {f : Fin (m + 1) → Y → ℝ} (hf : ∀ i, HasBoundedMetricLaplacian w (f i))
    (hle : ∀ i x, u i x ≤ (f i x : EReal)) {A : Set Y} (hA : MeasurableSet A) :
    ((sourceMixedNonPluripolarMeasure θ u hu).restrict (mixedContactSet u f) A).toReal =
      lapMixedReal (fun i => atlasClosedFormToNative (θ i)) f (A ∩ mixedContactSet u f) :=
  globalMixedMeasure_restrict_mixedContact_toReal_eq w (fun i => atlasClosedFormToNative (θ i))
    (fun i => (isThetaPSH_iff_nativeThetaPotential (θ i) (u i)).mp (hu i)) hf hle hA

end Mixed

end SGPT.Envelopes.LapClass3
