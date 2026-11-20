import SGPT.Okounkov.TranscendentalWNDeformationMetric
import SGPT.Foundations.Analysis.FirstPass.FormPullbackFunctorial
import SGPT.Okounkov.TranscendentalVolumeConcavityRestricted

/-!
# The class `β` restricted to the fibres and to `X'`

Blueprint `tok-wn:beta` (chapter `claude-tok-wn`): for `θ̃ = (π_X μ)^*θ + b (π_{ℙ¹} μ)^*ω_FS - c η_ℰ`
(`deformationForm`), with the metric of `𝒪(ℰ)` of `ExceptionalMetricStatement`:

* `pullback_deformationForm_centralSection`: `θ̃|_{X'} = θ - c η` (geometric equality of forms
  along the lift `ι' : X ≅ X'`), WN21 §4;
* `ofRepresentative_pullback_deformationForm_fibreSection`: `β|_{X_τ} = ξ` for `τ ≠ 0`
  (equality of classes along the section `s_τ : X ≅ X_τ`); indeed `θ̃|_{X_τ} = θ + c ddᶜ log W(·, τ)`.

The functoriality of pullbacks of forms is recorded for maps between manifolds of different
dimensions (`pullback_comp_geometricallyEq'`, `pullback_const_coeff`).
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
open SGPT.Foundations.Analysis.Pending.ProductComplexManifold
open scoped SGPT.Foundations.Analysis.Pending.ProductComplexManifold
open SGPT.Okounkov.TranscendentalMain

/-! ### Functoriality of pullbacks between manifolds of different dimensions -/

section Functorial

variable {p n₀ n₁ n₂ : ℕ}
  {X : Type*} [TopologicalSpace X] [ChartedSpace (ComplexModel n₀) X] [IsComplexManifold n₀ X]
  {Y : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel n₁) Y] [IsComplexManifold n₁ Y]
  {Z : Type*} [TopologicalSpace Z] [ChartedSpace (ComplexModel n₂) Z] [IsComplexManifold n₂ Z]

/-- **`(f ∘ g)^* a = g^* (f^* a)`** geometrically (dimensions may differ). -/
theorem pullback_comp_geometricallyEq' {f : Y → X} {g : Z → Y}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n₁) 𝓘(ℂ, ComplexModel n₀) ∞ f)
    (hg : ContMDiff 𝓘(ℂ, ComplexModel n₂) 𝓘(ℂ, ComplexModel n₁) ∞ g)
    (a : SmoothRealForm n₀ X p) :
    (SmoothRealForm.pullback (hf.comp hg) a).GeometricallyEq
      (SmoothRealForm.pullback hg (SmoothRealForm.pullback hf a)) := by
  intro e z hz
  set x : Z := e.val.symm z with hx
  set d₂ := complexChartAt (n := n₁) (g x) with hd₂
  set d₁ := complexChartAt (n := n₀) (f (g x)) with hd₁
  have hgx : g x ∈ d₂.val.source := mem_complexChartAt_source _
  have hfgx : f (g x) ∈ d₁.val.source := mem_complexChartAt_source _
  set w : ComplexModel n₁ := coordinateMap g e d₂ z with hw
  have hwx : d₂.val.symm w = g x := by
    rw [hw]
    exact d₂.val.left_inv hgx
  have hzdom : z ∈ coordinateDomain g e d₂ := ⟨hz, by
    simpa only [mem_preimage, ← hx] using hgx⟩
  have hwdom : w ∈ coordinateDomain f d₂ d₁ :=
    ⟨d₂.val.map_source hgx, by simpa only [mem_preimage, hwx] using hfgx⟩
  have heq : coordinateMap (f ∘ g) e d₁ =ᶠ[𝓝 z]
      (coordinateMap f d₂ d₁) ∘ (coordinateMap g e d₂) := by
    filter_upwards [(coordinateDomain_isOpen hg e d₂).mem_nhds hzdom] with y hy
    show d₁.val (f (g (e.val.symm y))) =
      d₁.val (f (d₂.val.symm (d₂.val (g (e.val.symm y)))))
    rw [d₂.val.left_inv hy.2]
  have hchain : fderiv ℝ (coordinateMap (f ∘ g) e d₁) z =
      (fderiv ℝ (coordinateMap f d₂ d₁) w).comp
        (fderiv ℝ (coordinateMap g e d₂) z) := by
    rw [heq.fderiv_eq]
    exact fderiv_comp z
      ((coordinateMap_contDiffAt_real hf d₂ d₁ hwdom).differentiableAt (by simp))
      ((coordinateMap_contDiffAt_real hg e d₂ hzdom).differentiableAt (by simp))
  have hpoint : coordinateMap f d₂ d₁ w = coordinateMap (f ∘ g) e d₁ z := by
    show d₁.val (f (d₂.val.symm w)) = d₁.val (f (g (e.val.symm z)))
    rw [hwx]
  ext v
  show (a.coeff d₁ (coordinateMap (f ∘ g) e d₁ z))
      (fun i => fderiv ℝ (coordinateMap (f ∘ g) e d₁) z (v i)) = _
  rw [hchain]
  show _ = ((SmoothRealForm.pullback hf a).coeff d₂ w)
      (fun i => fderiv ℝ (coordinateMap g e d₂) z (v i))
  have hinner : (SmoothRealForm.pullback hf a).coeff d₂ w =
      (a.coeff d₁ (coordinateMap f d₂ d₁ w)).compContinuousLinearMap
        (fderiv ℝ (coordinateMap f d₂ d₁) w) := by
    show SmoothRealForm.chartPullbackCoeff a f d₂ (complexChartAt (n := n₀) (f (d₂.val.symm w))) w = _
    rw [hwx, ← hd₁]
    rfl
  rw [hinner, hpoint]
  rfl

/-- **The pullback of a form of positive degree along a constant map vanishes.** -/
theorem pullback_const_coeff [NeZero p] (x₀ : X) (a : SmoothRealForm n₀ X p)
    (e : ComplexChart n₂ Z)
    {z : ComplexModel n₂} (hz : z ∈ e.val.target) :
    (SmoothRealForm.pullback (contMDiff_const (c := x₀)) a).coeff e z = 0 := by
  set d := complexChartAt (n := n₀) x₀
  have hzd : z ∈ coordinateDomain (fun _ : Z => x₀) e d := ⟨hz, mem_complexChartAt_source _⟩
  rw [SmoothRealForm.pullback_coeff _ a e d hzd]
  have hconst : coordinateMap (fun _ : Z => x₀) e d = fun _ => d.val x₀ := rfl
  have hfd : fderiv ℝ (fun _ : ComplexModel n₂ => d.val x₀) z = 0 := fderiv_const_apply _
  rw [hconst, hfd]
  have : Nonempty (Fin p) := ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne p)⟩⟩
  ext v
  rw [ContinuousAlternatingMap.compContinuousLinearMap_apply]
  have h0 : (⇑(0 : ComplexModel n₂ →L[ℝ] ComplexModel n₀) ∘ v) = 0 := by
    funext i; simp
  rw [h0]
  exact (a.coeff d (d.val x₀)).map_zero

end Functorial

/-- The pullback depends only on the map. -/
theorem pullback_congr_map {p n₀ n₂ : ℕ}
    {X : Type*} [TopologicalSpace X] [ChartedSpace (ComplexModel n₀) X] [IsComplexManifold n₀ X]
    {Z : Type*} [TopologicalSpace Z] [ChartedSpace (ComplexModel n₂) Z] [IsComplexManifold n₂ Z]
    {f g : Z → X} (h : f = g) (hf : ContMDiff 𝓘(ℂ, ComplexModel n₂) 𝓘(ℂ, ComplexModel n₀) ∞ f)
    (hg : ContMDiff 𝓘(ℂ, ComplexModel n₂) 𝓘(ℂ, ComplexModel n₀) ∞ g) (a : SmoothRealForm n₀ X p) :
    SmoothRealForm.pullback hf a = SmoothRealForm.pullback hg a := by
  subst h
  rfl

/-- The coefficients of a pulled-back linear combination of closed forms. -/
theorem pullback_coeff_add_smul_sub {k n : ℕ}
    {V : Type*} [TopologicalSpace V] [ChartedSpace (ComplexModel k) V] [IsComplexManifold k V]
    {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    {f : V → M} (hf : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ f)
    (A B C : ClosedRealOneOneForm n M) (b c : ℝ) (e : ComplexChart k V) {z : ComplexModel k}
    (hz : z ∈ e.val.target) :
    (ClosedRealOneOneForm.pullback hf (A + b • B - c • C)).val.coeff e z =
      (ClosedRealOneOneForm.pullback hf A).val.coeff e z +
        b • (ClosedRealOneOneForm.pullback hf B).val.coeff e z -
        c • (ClosedRealOneOneForm.pullback hf C).val.coeff e z := by
  set d := complexChartAt (n := n) (f (e.val.symm z))
  have hzd : z ∈ coordinateDomain f e d := ⟨hz, mem_complexChartAt_source _⟩
  simp only [ClosedRealOneOneForm.pullback_val, SmoothRealForm.pullback_coeff hf _ e d hzd]
  ext v
  simp [sub_eq_add_neg, ClosedRealOneOneForm.coeff_add, ClosedRealOneOneForm.coeff_smul]

variable {m : ℕ} (F : OriginalFlagGeometry.{u} (m + 1))
variable {𝒳 : Type u} [TopologicalSpace 𝒳] [ChartedSpace (ComplexModel (m + 1 + 1)) 𝒳]
  [IsComplexManifold (m + 1 + 1) 𝒳] {μ : 𝒳 → F.carrier × ProjectiveLine}

/-- The `X`- and `ℙ¹`-parts of `θ̃` along a section `s` of `μ` over `x ↦ (x, τ)`. -/
theorem pullback_deformationForm_coeff_of_section
    (hμc : ContMDiff 𝓘(ℂ, ComplexModel (m + 1 + 1)) 𝓘(ℂ, ComplexModel (m + 1 + 1)) ∞ μ)
    (θ : ClosedRealOneOneForm (m + 1) F.carrier) (b c : ℝ)
    (Eℰ : MeteredEffectiveQDivisor (m + 1 + 1) 𝒳) {p : ProjectiveLine} {s : F.carrier → 𝒳}
    (hs : ContMDiff 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel (m + 1 + 1)) ∞ s)
    (hμs : ∀ x, μ (s x) = (x, p)) (e : ComplexChart (m + 1) F.carrier)
    {z : ComplexModel (m + 1)} (hz : z ∈ e.val.target) :
    (ClosedRealOneOneForm.pullback hs (deformationForm F hμc θ b c Eℰ)).val.coeff e z =
      θ.val.coeff e z - c • (ClosedRealOneOneForm.pullback hs Eℰ.curvature).val.coeff e z := by
  unfold deformationForm
  rw [pullback_coeff_add_smul_sub hs _ _ _ b c e hz]
  have hX : (fun z => (μ z).1) ∘ s = id := funext fun x => by simp [hμs]
  have hP : (fun z => (μ z).2) ∘ s = fun _ => p := funext fun x => by simp [hμs]
  have h1 : (ClosedRealOneOneForm.pullback hs
      (ClosedRealOneOneForm.pullback (contMDiff_deformationProjX F hμc) θ)).val.coeff e z =
        θ.val.coeff e z := by
    rw [ClosedRealOneOneForm.pullback_val, ClosedRealOneOneForm.pullback_val,
      ← pullback_comp_geometricallyEq' (contMDiff_deformationProjX F hμc) hs θ.val e hz,
      pullback_congr_map hX _ contMDiff_id]
    exact SmoothRealForm.pullback_id_geometricallyEq θ.val e hz
  have h2 : (ClosedRealOneOneForm.pullback hs (ClosedRealOneOneForm.pullback
      (contMDiff_deformationProjP1 F hμc) SGPT.Toric.projectiveNativeFSClosedForm)).val.coeff e z
        = 0 := by
    rw [ClosedRealOneOneForm.pullback_val, ClosedRealOneOneForm.pullback_val,
      ← pullback_comp_geometricallyEq' (contMDiff_deformationProjP1 F hμc) hs _ e hz,
      pullback_congr_map hP _ contMDiff_const]
    exact pullback_const_coeff p _ e hz
  rw [h1, h2, smul_zero, add_zero]

/-- **`θ̃|_{X'} = θ - c η`** (`tok-wn:beta`): along the lift `ι' : X ≅ X'` of `x ↦ (x, 0)`, for a
metric of `𝒪(ℰ)` whose curvature restricts to that of `E` (`ExceptionalMetricStatement`). -/
theorem pullback_deformationForm_centralSection
    (hμc : ContMDiff 𝓘(ℂ, ComplexModel (m + 1 + 1)) 𝓘(ℂ, ComplexModel (m + 1 + 1)) ∞ μ)
    (θ : ClosedRealOneOneForm (m + 1) F.carrier) (b c : ℝ)
    (Eℰ : MeteredEffectiveQDivisor (m + 1 + 1) 𝒳) {E : MeteredEffectiveQDivisor (m + 1) F.carrier}
    {ι : F.carrier → 𝒳}
    (hι : ContMDiff 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel (m + 1 + 1)) ∞ ι)
    (hμι : ∀ x, μ (ι x) = (x, projectiveZero))
    (hcurv : (ClosedRealOneOneForm.pullback hι Eℰ.curvature).val.GeometricallyEq
      E.curvature.val) :
    (ClosedRealOneOneForm.pullback hι (deformationForm F hμc θ b c Eℰ)).val.GeometricallyEq
      (θ - c • E.curvature).val := by
  intro e z hz
  rw [pullback_deformationForm_coeff_of_section F hμc θ b c Eℰ hι hμι e hz, hcurv e hz]
  simp [sub_eq_add_neg, ClosedRealOneOneForm.coeff_add, ClosedRealOneOneForm.coeff_smul]

/-- Off the support of a metered divisor, its curvature pulls back to `-ddᶜ` of the pulled-back
weight (dimensions may differ). -/
theorem pullback_curvature_coeff_of_notMem {k n : ℕ}
    {V : Type*} [TopologicalSpace V] [ChartedSpace (ComplexModel k) V] [IsComplexManifold k V]
    {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    {f : V → M} (hf : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ f)
    (D : MeteredEffectiveQDivisor n M) (e : ComplexChart k V) {z : ComplexModel k}
    (hz : z ∈ e.val.target) (hfz : f (e.val.symm z) ∉ D.support) :
    (ClosedRealOneOneForm.pullback hf D.curvature).val.coeff e z =
      -smoothDDC (fun w => (D.weight (f (e.val.symm w))).toReal) z := by
  set d := complexChartAt (n := n) (f (e.val.symm z))
  have hzd : z ∈ coordinateDomain f e d := ⟨hz, mem_complexChartAt_source _⟩
  obtain ⟨W₁, hW₁, hpot₁⟩ :=
    MeteredDivisorSmoothOffSupport.exists_isSmoothLocalPotential_neg_curvature D hfz d
      (mem_complexChartAt_source _)
  have hpull := isSmoothLocalPotential_pullback hf e hpot₁
  have hzW : z ∈ potentialDomain f e d W₁ := ⟨hzd, hW₁⟩
  have hρ : (fun ζ => (D.weight (d.val.symm ζ)).toReal) ∘ coordinateMap f e d =ᶠ[𝓝 z]
      fun ζ => (D.weight (f (e.val.symm ζ))).toReal := by
    filter_upwards [(coordinateDomain_isOpen hf e d).mem_nhds hzd] with w hw
    show (D.weight (d.val.symm (d.val (f (e.val.symm w))))).toReal = _
    rw [d.val.left_inv hw.2]
  have h1 := hpull.2.2.2 hzW
  rw [smoothDDC_congr hρ] at h1
  have hneg : (SmoothRealForm.pullback hf (-D.curvature).val).coeff e z =
      -(ClosedRealOneOneForm.pullback hf D.curvature).val.coeff e z := by
    rw [ClosedRealOneOneForm.pullback_val, SmoothRealForm.pullback_coeff hf _ e d hzd,
      SmoothRealForm.pullback_coeff hf _ e d hzd]
    ext v
    simp
  rw [hneg] at h1
  rw [h1, neg_neg]

/-- **`β|_{X_τ} = ξ`** (`tok-wn:beta`): for `τ ≠ 0` and a section `s_τ : X ≅ X_τ` of `μ`,
`s_τ^* θ̃ = θ + c ddᶜ log W(·, τ)`, so it represents the class `{θ}`. -/
theorem ofRepresentative_pullback_deformationForm_fibreSection
    (hμ : IsNormalConeDeformation F μ) {E : MeteredEffectiveQDivisor (m + 1) F.carrier}
    (hE : IsFirstDivisorUnitMetric F E) {Eℰ : MeteredEffectiveQDivisor (m + 1 + 1) 𝒳}
    (hweight : ∀ z, Eℰ.weight z = ENNReal.log (ENNReal.ofReal (baseExceptionalWeight F E (μ z))))
    (hsupp : Eℰ.support = exceptionalSet F μ)
    (θ : ClosedRealOneOneForm (m + 1) F.carrier) (b c : ℝ) {p : ProjectiveLine}
    (hp : p ≠ projectiveZero) {s : F.carrier → 𝒳}
    (hs : ContMDiff 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel (m + 1 + 1)) ∞ s)
    (hμs : ∀ x, μ (s x) = (x, p)) :
    RealBottChern.ofRepresentative
        (ClosedRealOneOneForm.pullback hs (deformationForm F hμ.contMDiff θ b c Eℰ)) =
      RealBottChern.ofRepresentative θ := by
  have hnot : ∀ x, (x, p) ∉ deformationCentre F := fun x h =>
    hp ((mem_deformationCentre_iff F).mp h).2
  have hWpos : ∀ x, 0 < baseExceptionalWeight F E (x, p) := fun x =>
    baseExceptionalWeight_pos F hE (hnot x)
  have hsm : ChartSmooth (n := m + 1) (fun x => baseExceptionalWeight F E (x, p)) :=
    ProductTestForms.chartSmooth_comp (contMDiff_slice F p) (chartSmooth_baseExceptionalWeight F hE)
  set h : F.carrier → ℝ := fun x => -c * Real.log (baseExceptionalWeight F E (x, p)) with hh
  have hhs : ChartSmooth (n := m + 1) h := fun e =>
    ((hsm e).log fun w _ => (hWpos _).ne').const_smul (-c)
  refine (RealBottChern.ofRepresentative_eq_iff _ _).mpr ⟨h, hhs, fun e z hz => ?_⟩
  have hsz : s (e.val.symm z) ∉ Eℰ.support := by
    rw [hsupp]
    show μ (s (e.val.symm z)) ∉ deformationCentre F
    rw [hμs]
    exact hnot _
  rw [pullback_deformationForm_coeff_of_section F hμ.contMDiff θ b c Eℰ hs hμs e hz,
    pullback_curvature_coeff_of_notMem hs Eℰ e hz hsz]
  have hw : (fun w => (Eℰ.weight (s (e.val.symm w))).toReal) =
      fun w => Real.log (baseExceptionalWeight F E (e.val.symm w, p)) := by
    funext w
    rw [hweight, hμs, ENNReal.log_ofReal_of_pos (hWpos _)]
    rfl
  rw [hw]
  have hsd : smoothDDC (fun w => h (e.val.symm w)) z =
      (-c) • smoothDDC (fun w => Real.log (baseExceptionalWeight F E (e.val.symm w, p))) z := by
    have := SGPT.Foundations.Analysis.FirstPass.smoothDDC_smul e.val.open_target
      ((hsm e).log fun w _ => (hWpos _).ne') (-c) hz
    simpa [hh, smul_eq_mul] using this
  rw [hsd, smul_neg, sub_neg_eq_add, add_assoc, ← add_smul, add_neg_cancel, zero_smul, add_zero]

/-- **`β` depends only on `ξ = {θ}`** (`tok-wn:beta`): Bott--Chern equivalent representatives
give Bott--Chern equivalent forms `θ̃`. -/
theorem ofRepresentative_deformationForm_eq
    (hμc : ContMDiff 𝓘(ℂ, ComplexModel (m + 1 + 1)) 𝓘(ℂ, ComplexModel (m + 1 + 1)) ∞ μ)
    {θ θ' : ClosedRealOneOneForm (m + 1) F.carrier}
    (h : RealBottChern.ofRepresentative θ = RealBottChern.ofRepresentative θ') (b c : ℝ)
    (Eℰ : MeteredEffectiveQDivisor (m + 1 + 1) 𝒳) :
    RealBottChern.ofRepresentative (deformationForm F hμc θ b c Eℰ) =
      RealBottChern.ofRepresentative (deformationForm F hμc θ' b c Eℰ) := by
  obtain ⟨g, hg, heq⟩ := (RealBottChern.ofRepresentative_eq_iff θ θ').mp h
  have hpull := TranscendentalVolumeConcavity.pullback_coeff_add_ddc
    (contMDiff_deformationProjX F hμc) hg heq
  refine (RealBottChern.ofRepresentative_eq_iff _ _).mpr
    ⟨fun z => g (μ z).1, ProductTestForms.chartSmooth_comp (contMDiff_deformationProjX F hμc) hg,
      fun e z hz => ?_⟩
  unfold deformationForm
  simp only [sub_eq_add_neg, ClosedRealOneOneForm.coeff_add]
  rw [hpull e z hz]
  abel

end SGPT.Okounkov.TranscendentalWN
