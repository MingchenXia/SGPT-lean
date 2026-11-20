import SGPT.Okounkov.TranscendentalWNVolumeBundleStatement
import SGPT.Toric.ProjectiveLineFubiniStudy
import SGPT.Foundations.Analysis.Pending.PluriharmonicLogNorm

/-!
# Local potentials of `θ̃` along the exceptional divisor (package WN-VF4)

Blueprint `claude-tok-wn-vf4`, node `tok-wn-vf4:potential`; source WN21 end of §4
(`θ̃|_ℰ = π_Z^*(θ|_Z) + c dd^c log(1 + |z̃₁|² e^{-g_Z})`, i.e. `θ̃|_ℰ = π^*θ - c dd^c log S₁`).

With `S₁ = strictWeight` (the weight of `𝒪(X')`, `dd^c log S₁ = η_ℰ - (π_{ℙ¹} μ)^* ω_FS` where
`S₁ > 0`, `strictFactorization_closedForm_coeff`),

  `θ̃ = (π_X μ)^*θ + b (π_{ℙ¹} μ)^*ω_FS - c η_ℰ = (π_X μ)^*θ + (b - c)(π_{ℙ¹} μ)^*ω_FS - c dd^c log S₁`

near every point where `S₁ > 0`.  Along any holomorphic `j : V → 𝒳` with `π_{ℙ¹} μ j ≡ 0` (e.g. the
inclusion of `ℰ`) the middle term pulls back to a constant potential, so
`v ↦ ρ_X(π_X μ j e⁻¹ v) - c log S₁(j e⁻¹ v)` is a smooth local potential of `j^*θ̃`
(`isSmoothLocalPotential_pullback_deformationForm`), for every local potential `ρ_X` of `θ`.
-/

set_option autoImplicit false

noncomputable section

universe u

namespace SGPT.Okounkov.TranscendentalWN

open Set Filter
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.HolomorphicMaps
open SGPT.Foundations.Analysis.FirstPass.LocalPotentialPullback
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.FactorizedWeightForm
open SGPT.Okounkov.TranscendentalMain

/-! ### Generalities on local potentials -/

section General

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

omit [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] in
theorem smoothDDC_const (n : ℕ) (K : ℝ) (z : ComplexModel n) :
    smoothDDC (fun _ : ComplexModel n => K) z = 0 :=
  PluriharmonicLogNorm.smoothDDC_eq_zero_of_fderiv_const (L := 0)
    (Eventually.of_forall fun y => by simp)

/-- A function agreeing on the domain with a local potential minus a constant is a local
potential. -/
theorem IsSmoothLocalPotential.of_eqOn_sub_const {θ : SmoothRealForm n M 2} {e : ComplexChart n M}
    {W : Set (ComplexModel n)} {ρ f : ComplexModel n → ℝ} (hρ : IsSmoothLocalPotential θ e W ρ)
    {K : ℝ} (heq : EqOn f (fun z => ρ z - K) W) : IsSmoothLocalPotential θ e W f := by
  refine ⟨hρ.1, hρ.2.1, (hρ.2.2.1.sub contDiffOn_const).congr heq, fun z hz => ?_⟩
  have hev : f =ᶠ[𝓝 z] fun y => ρ y - K := by
    filter_upwards [hρ.1.mem_nhds hz] with y hy
    exact heq hy
  rw [smoothDDC_congr hev, PositiveClasses.smoothDDC_sub hρ.1 hρ.2.2.1 contDiffOn_const hz,
    smoothDDC_const, sub_zero]
  exact hρ.2.2.2 hz

end General

variable {m : ℕ} (F : OriginalFlagGeometry.{u} (m + 1))

variable {𝒳 : Type u} [TopologicalSpace 𝒳] [ChartedSpace (ComplexModel (m + 1 + 1)) 𝒳]
  [IsComplexManifold (m + 1 + 1) 𝒳] {μ : 𝒳 → F.carrier × ProjectiveLine}

/-- The strict weight is smooth on each factorization domain. -/
theorem contDiffOn_strictWeight_comp (hμ : IsNormalConeDeformation F μ)
    {E : MeteredEffectiveQDivisor (m + 1) F.carrier} (hE : IsFirstDivisorUnitMetric F E) (q : 𝒳)
    (e : ComplexChart (m + 1 + 1) 𝒳) :
    ContDiffOn ℝ ∞ (fun u => strictWeight F E μ (e.val.symm u))
      (e.val.target ∩ e.val.symm ⁻¹' (strictFactorization F hμ hE).domain q) := by
  set Fw := strictFactorization F hμ hE
  have h1 := contDiffOn_norm_sq_comp_chart_symm (Fw.isOpen_domain q) (Fw.gen_mdifferentiable q) e
  have h2 := Fw.smooth q e
  refine (h1.mul h2).congr fun u hu => ?_
  rw [Fw.factor q _ hu.2, Complex.normSq_eq_norm_sq]

theorem continuous_strictWeight (hμ : IsNormalConeDeformation F μ)
    {E : MeteredEffectiveQDivisor (m + 1) F.carrier} (hE : IsFirstDivisorUnitMetric F E) :
    Continuous (strictWeight F E μ) :=
  continuous_iff_continuousAt.mpr (WeightFactorization.continuousAt (strictFactorization F hμ hE))

theorem continuous_zStrictWeight (hμ : IsNormalConeDeformation F μ)
    {E : MeteredEffectiveQDivisor (m + 1) F.carrier} (hE : IsFirstDivisorUnitMetric F E) :
    Continuous (zStrictWeight F E μ) :=
  continuous_iff_continuousAt.mpr (WeightFactorization.continuousAt (zStrictFactorization F hμ hE))

/-- The local potential `log (1 + |τ|²)` of `ω_FS` in a native chart of `ℙ¹`. -/
theorem isSmoothLocalPotential_projectiveFSPotential (e : ComplexChart 1 ProjectiveLine) :
    IsSmoothLocalPotential SGPT.Toric.projectiveNativeFSClosedForm.val e e.val.target
      SGPT.Toric.projectiveFSPotential :=
  ⟨e.val.open_target, subset_rfl, SGPT.Toric.contDiff_projectiveFSPotential.contDiffOn,
    fun _ _ => rfl⟩

section Pullback

variable {k : ℕ} {V : Type*} [TopologicalSpace V] [ChartedSpace (ComplexModel k) V]
  [IsComplexManifold k V]

/-- **`tok-wn-vf4:potential`**: along a holomorphic `j : V → 𝒳` with `π_{ℙ¹} μ j ≡ 0`, near a
point where `S₁ > 0`, `v ↦ ρ_X(π_X μ j e⁻¹ v) - c log S₁(j e⁻¹ v)` is a smooth local potential of
`j^*θ̃` for every local potential `ρ_X` of `θ`. -/
theorem isSmoothLocalPotential_pullback_deformationForm (hμ : IsNormalConeDeformation F μ)
    {E : MeteredEffectiveQDivisor (m + 1) F.carrier} (hE : IsFirstDivisorUnitMetric F E)
    {Eℰ : MeteredEffectiveQDivisor (m + 1 + 1) 𝒳} (hEℰ : IsDeformationExceptionalMetric F E hμ Eℰ)
    (θ : ClosedRealOneOneForm (m + 1) F.carrier) (b c : ℝ) {j : V → 𝒳}
    (hj : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel (m + 1 + 1)) ∞ j)
    (hj0 : ∀ y, (μ (j y)).2 = projectiveZero) (e : ComplexChart k V) {y : V}
    (hy : y ∈ e.val.source) (hS : 0 < strictWeight F E μ (j y))
    (dX : ComplexChart (m + 1) F.carrier) {WX : Set (ComplexModel (m + 1))}
    {ρX : ComplexModel (m + 1) → ℝ} (hρX : IsSmoothLocalPotential θ.val dX WX ρX)
    (hyX : (μ (j y)).1 ∈ dX.val.source) (hyW : dX.val (μ (j y)).1 ∈ WX) :
    ∃ D : Set (ComplexModel k), e.val y ∈ D ∧ IsSmoothLocalPotential
      (ClosedRealOneOneForm.pullback hj (deformationForm F hμ.contMDiff θ b c Eℰ)).val e D
      (fun v => ρX (dX.val (μ (j (e.val.symm v))).1) -
        c * Real.log (strictWeight F E μ (j (e.val.symm v)))) := by
  set q := j y with hq
  set d : ComplexChart (m + 1 + 1) 𝒳 := complexChartAt q with hd
  have hqd : q ∈ d.val.source := mem_complexChartAt_source q
  set cP : ComplexChart 1 ProjectiveLine := complexChartAt projectiveZero with hcP
  have h0P : projectiveZero ∈ cP.val.source := mem_complexChartAt_source _
  have hπX := contMDiff_deformationProjX F hμ.contMDiff
  have hπP := contMDiff_deformationProjP1 F hμ.contMDiff
  have hS₁c : Continuous (strictWeight F E μ) := continuous_strictWeight F hμ hE
  -- the three potentials on `𝒳`
  have hP1 := isSmoothLocalPotential_pullback hπX d hρX
  have hP2 := isSmoothLocalPotential_pullback hπP d (isSmoothLocalPotential_projectiveFSPotential cP)
  set V3 : Set 𝒳 := (strictFactorization F hμ hE).domain q ∩ {z | 0 < strictWeight F E μ z}
    with hV3def
  have hV3 : IsOpen V3 :=
    ((strictFactorization F hμ hE).isOpen_domain q).inter (isOpen_lt continuous_const hS₁c)
  set D3 : Set (ComplexModel (m + 1 + 1)) := d.val.target ∩ d.val.symm ⁻¹' V3 with hD3def
  have hD3 : IsOpen D3 := d.val.isOpen_inter_preimage_symm hV3
  have hsm : ∀ e' : ComplexChart (m + 1 + 1) 𝒳,
      ContDiffOn ℝ ∞ (fun u => strictWeight F E μ (e'.val.symm u))
        (e'.val.target ∩ e'.val.symm ⁻¹' V3) :=
    fun e' => (contDiffOn_strictWeight_comp F hμ hE q e').mono fun u hu =>
      ⟨hu.1, mem_preimage.mpr hu.2.1⟩
  have hlog : ContDiffOn ℝ ∞ (fun u => Real.log (strictWeight F E μ (d.val.symm u))) D3 :=
    (hsm d).log fun u hu => (show 0 < strictWeight F E μ (d.val.symm u) from hu.2.2).ne'
  have hcoef3 : ∀ u ∈ D3, smoothDDC (fun u => Real.log (strictWeight F E μ (d.val.symm u))) u =
      (Eℰ.curvature - ClosedRealOneOneForm.pullback hπP
        SGPT.Toric.projectiveNativeFSClosedForm).val.coeff d u := by
    intro u hu
    have h1 := WeightFactorization.closedForm_coeff_eq_of_pos (strictFactorization F hμ hE) hV3
      hsm (fun z hz => hz.2) d hu.1 hu.2
    have h2 := strictFactorization_closedForm_coeff F hμ hE hEℰ.weight_eq hEℰ.support_eq d hu.1
    exact h1.symm.trans h2
  -- the combined potential of `θ̃` on `𝒳`
  set D : Set (ComplexModel (m + 1 + 1)) := potentialDomain (fun z => (μ z).1) d dX WX ∩
    potentialDomain (fun z => (μ z).2) d cP cP.val.target ∩ D3 with hDdef
  have hDo : IsOpen D := (hP1.1.inter hP2.1).inter hD3
  set P : ComplexModel (m + 1 + 1) → ℝ := fun u =>
    (ρX ∘ coordinateMap (fun z => (μ z).1) d dX) u +
      ((b - c) * (SGPT.Toric.projectiveFSPotential ∘ coordinateMap (fun z => (μ z).2) d cP) u -
        c * Real.log (strictWeight F E μ (d.val.symm u))) with hPdef
  have hs1 : ContDiffOn ℝ ∞ (ρX ∘ coordinateMap (fun z => (μ z).1) d dX) D :=
    hP1.2.2.1.mono fun u hu => hu.1.1
  have hs2 : ContDiffOn ℝ ∞
      (fun u => (b - c) * (SGPT.Toric.projectiveFSPotential ∘
        coordinateMap (fun z => (μ z).2) d cP) u) D :=
    contDiffOn_const.mul (hP2.2.2.1.mono fun u hu => hu.1.2)
  have hs3 : ContDiffOn ℝ ∞ (fun u => c * Real.log (strictWeight F E μ (d.val.symm u))) D :=
    contDiffOn_const.mul (hlog.mono fun u hu => hu.2)
  have hP : IsSmoothLocalPotential (deformationForm F hμ.contMDiff θ b c Eℰ).val d D P := by
    refine ⟨hDo, fun u hu => hu.2.1, hs1.add (hs2.sub hs3), fun u hu => ?_⟩
    have e1 := smoothDDC_add hDo hs1 (hs2.sub hs3) hu
    have e2 := PositiveClasses.smoothDDC_sub hDo hs2 hs3 hu
    have e3 := smoothDDC_smul hDo (hP2.2.2.1.mono fun u hu => hu.1.2) (b - c) hu
    have e4 := smoothDDC_smul hDo (hlog.mono fun u hu => hu.2) c hu
    simp only [smul_eq_mul] at e3 e4
    simp only [hPdef]
    rw [e1, e2, e3, e4, hP1.2.2.2 hu.1.1, hP2.2.2.2 hu.1.2, hcoef3 u hu.2]
    simp only [deformationForm, BlowupBigPullback.coeff_sub, ClosedRealOneOneForm.coeff_add,
      ClosedRealOneOneForm.coeff_smul, ClosedRealOneOneForm.pullback_val]
    module
  -- pull back along `j`
  have hPj := isSmoothLocalPotential_pullback hj e hP
  set K : ℝ := SGPT.Toric.projectiveFSPotential (cP.val projectiveZero) with hK
  have hyd : y ∈ e.val.source ∩ e.val ⁻¹' coordinateDomain j e d := by
    refine ⟨hy, e.val.map_source hy, ?_⟩
    change j (e.val.symm (e.val y)) ∈ d.val.source
    rw [e.val.left_inv hy]
    exact hqd
  refine ⟨potentialDomain j e d D, ⟨hyd.2, ?_⟩, IsSmoothLocalPotential.of_eqOn_sub_const hPj (K := (b - c) * K) ?_⟩
  · -- `d q ∈ D`
    change d.val (j (e.val.symm (e.val y))) ∈ D
    rw [e.val.left_inv hy]
    have hqt : d.val q ∈ d.val.target := d.val.map_source hqd
    have hsymm : d.val.symm (d.val q) = q := d.val.left_inv hqd
    refine ⟨⟨⟨⟨hqt, ?_⟩, ?_⟩, ⟨hqt, ?_⟩, ?_⟩, hqt, ?_⟩
    · change (μ (d.val.symm (d.val q))).1 ∈ dX.val.source
      rw [hsymm]; exact hyX
    · change dX.val (μ (d.val.symm (d.val q))).1 ∈ WX
      rw [hsymm]; exact hyW
    · change (μ (d.val.symm (d.val q))).2 ∈ cP.val.source
      rw [hsymm, hq, hj0]; exact h0P
    · change cP.val (μ (d.val.symm (d.val q))).2 ∈ cP.val.target
      rw [hsymm, hq, hj0]; exact cP.val.map_source h0P
    · change d.val.symm (d.val q) ∈ V3
      rw [hsymm]
      exact ⟨(strictFactorization F hμ hE).mem_domain q, hS⟩
  · intro v hv
    have hvd : j (e.val.symm v) ∈ d.val.source := hv.1.2
    have hsymm : d.val.symm (d.val (j (e.val.symm v))) = j (e.val.symm v) := d.val.left_inv hvd
    simp only [Function.comp_apply, coordinateMap, hPdef]
    rw [hsymm, hj0, hK]
    ring

end Pullback

end SGPT.Okounkov.TranscendentalWN
