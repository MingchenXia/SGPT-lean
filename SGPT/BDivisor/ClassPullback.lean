import SGPT.Foundations.Analysis.FirstPass.FormPullbackFunctorial
import SGPT.Foundations.Analysis.Pending.AdmissiblePresentationPullback
import SGPT.Foundations.Analysis.Pending.KahlerDomination
import SGPT.Foundations.Analysis.Pending.AnalyticModificationPotentialDescent

/-!
# Pullback of real `(1,1)`-classes along holomorphic maps

For a holomorphic map `f : Y → X` between complex manifolds of the same dimension, the
pull-back of smooth closed real `(1,1)`-forms respects Bott--Chern equivalence
(`θ' = θ + ddᶜ h` gives `f^*θ' = f^*θ + ddᶜ (h ∘ f)`), so it descends to a real linear map

`f^* : H^{1,1}(X, ℝ) → H^{1,1}(Y, ℝ)`

on the real Bott--Chern classes `RealBottChern n X`. This is the class pull-back `π^*α` of the
b-divisor chapter (`def:bdiv:L116`: "the class `𝔻_Z` is the pull-back of `α_Y`") and of
`prop:cones_modif`.

Main declarations:

* `SGPT.BDivisor.classPullback` — the pull-back `f^*` on classes, a real linear map;
* `SGPT.BDivisor.classPullback_ofRepresentative` — it is computed by pulling back any smooth
  representative;
* `SGPT.BDivisor.classPullback_id`, `SGPT.BDivisor.classPullback_comp` — functoriality
  `id^* = id`, `(f ∘ g)^* = g^* ∘ f^*`;
* `SGPT.BDivisor.nefWithRespectTo_pullback`, `SGPT.BDivisor.classNef_classPullback` — the
  pull-back of a nef class to a compact manifold is nef (`prop:cones_modif`, item 1): nefness of
  `α` means that for every `ε > 0` some smooth representative of `α` is `≥ -ε ω`;
* `SGPT.BDivisor.classPseudoeffective_classPullback_iff` — along a modification `π`, the class
  `π^*α` is pseudo-effective iff `α` is (pseudo-effectivity: the class carries a closed positive
  current `θ + ddᶜ φ`, i.e. a `θ`-psh potential `φ` for a representative `θ`).
-/

set_option autoImplicit false

noncomputable section

universe u

namespace SGPT.BDivisor

open Set Filter
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.Pending

variable {n : ℕ}
  {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
  {Z : Type u} [TopologicalSpace Z] [ChartedSpace (ComplexModel n) Z] [IsComplexManifold n Z]

/-- Pull-back of closed real `(1,1)`-forms is additive. -/
theorem closedForm_pullback_add {f : Y → X}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ f)
    (a b : ClosedRealOneOneForm n X) :
    ClosedRealOneOneForm.pullback hf (a + b) =
      ClosedRealOneOneForm.pullback hf a + ClosedRealOneOneForm.pullback hf b :=
  ClosedRealOneOneForm.ext fun _ _ => by ext v; rfl

/-- Pull-back of closed real `(1,1)`-forms is homogeneous. -/
theorem closedForm_pullback_smul {f : Y → X}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ f)
    (c : ℝ) (a : ClosedRealOneOneForm n X) :
    ClosedRealOneOneForm.pullback hf (c • a) = c • ClosedRealOneOneForm.pullback hf a :=
  ClosedRealOneOneForm.ext fun _ _ => by ext v; rfl

/-- The pull-back `f^* : H^{1,1}(X,ℝ) → H^{1,1}(Y,ℝ)` of real Bott--Chern `(1,1)`-classes along
a holomorphic map, computed on any smooth closed representative. -/
def classPullback {f : Y → X}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ f) :
    RealBottChern n X →ₗ[ℝ] RealBottChern n Y where
  toFun α := Quotient.liftOn α
    (fun θ => RealBottChern.ofRepresentative (ClosedRealOneOneForm.pullback hf θ))
    (fun a b hab =>
      (Pending.AdmissiblePresentationPullback.ofRepresentative_pullback_congr hf
        ((RealBottChern.ofRepresentative_eq_iff b a).mpr hab.symm)).symm)
  map_add' α β := by
    induction α using Quotient.inductionOn
    induction β using Quotient.inductionOn
    change RealBottChern.ofRepresentative (ClosedRealOneOneForm.pullback hf (_ + _)) = _
    rw [closedForm_pullback_add, RealBottChern.ofRepresentative_add]
    rfl
  map_smul' c α := by
    induction α using Quotient.inductionOn
    change RealBottChern.ofRepresentative (ClosedRealOneOneForm.pullback hf (c • _)) = _
    rw [closedForm_pullback_smul, RealBottChern.ofRepresentative_smul]
    rfl

/-- The class pull-back is computed by pulling back a smooth representative. -/
@[simp] theorem classPullback_ofRepresentative {f : Y → X}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ f)
    (θ : ClosedRealOneOneForm n X) :
    classPullback hf (RealBottChern.ofRepresentative θ) =
      RealBottChern.ofRepresentative (ClosedRealOneOneForm.pullback hf θ) := rfl

/-- Functoriality: `id^* = id` on classes. -/
theorem classPullback_id (α : RealBottChern n X) :
    classPullback (f := (id : X → X)) (contMDiff_id (I := 𝓘(ℂ, ComplexModel n)) (n := ∞)) α =
      α := by
  induction α using Quotient.inductionOn with
  | h θ => exact ClosedRealOneOneForm.ofRepresentative_pullback_id θ

/-- Functoriality: `(f ∘ g)^* = g^* ∘ f^*` on classes. -/
theorem classPullback_comp {f : Y → X} {g : Z → Y}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ f)
    (hg : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ g)
    (α : RealBottChern n X) :
    classPullback (hf.comp hg) α = classPullback hg (classPullback hf α) := by
  induction α using Quotient.inductionOn with
  | h θ => exact ClosedRealOneOneForm.ofRepresentative_pullback_comp hf hg θ

/-- The class pull-back depends only on the map, not on the proof that it is holomorphic. -/
theorem classPullback_congr {f f' : Y → X} (h : f = f')
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ f)
    (hf' : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ f') (α : RealBottChern n X) :
    classPullback hf α = classPullback hf' α := by
  subst h
  rfl

/-- The chart expression of `ddᶜ (h ∘ f)` is the pull-back of the chart expression of `ddᶜ h`. -/
theorem smoothDDC_comp_chart {f : Y → X}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ f)
    {h : X → ℝ} (hh : ChartSmooth (n := n) h) (e : ComplexChart n Y) (d : ComplexChart n X)
    {z : ComplexModel n} (hzd : z ∈ HolomorphicMaps.coordinateDomain f e d) :
    smoothDDC (fun y => h (f (e.val.symm y))) z =
      (smoothDDC (fun w => h (d.val.symm w)) (HolomorphicMaps.coordinateMap f e d z)).compContinuousLinearMap
        (fderiv ℝ (HolomorphicMaps.coordinateMap f e d) z) := by
  have hD := HolomorphicMaps.coordinateDomain_isOpen hf e d
  rw [← HolomorphicDDC.smoothDDC_comp hD d.val.open_target
    (HolomorphicMaps.coordinateMap_contDiffOn hf e d) (hh d)
    (fun _ hy => HolomorphicMaps.coordinateMap_mem_target hy) hzd]
  apply smoothDDC_congr
  filter_upwards [hD.mem_nhds hzd] with y hy
  show h (f (e.val.symm y)) = h (d.val.symm (d.val (f (e.val.symm y))))
  rw [d.val.left_inv hy.2]

/-- **Nefness pulls back** to a compact manifold: if `θ` is nef with respect to a Kähler form
`ω` on `X`, then `f^*θ` is nef with respect to any Kähler form `ω_Y` on the compact
manifold `Y`. -/
theorem nefWithRespectTo_pullback [CompactSpace Y] {f : Y → X}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ f)
    (omega : KahlerBackground n X) (omegaY : KahlerBackground n Y)
    {θ : ClosedRealOneOneForm n X} (hθ : NefWithRespectTo omega θ) :
    NefWithRespectTo omegaY (ClosedRealOneOneForm.pullback hf θ) := by
  obtain ⟨A, hA, hdom⟩ := Pending.KahlerDomination.exists_pos_isSemipositive_add_smul omegaY
    (-ClosedRealOneOneForm.pullback hf omega.form)
  intro ε hε
  obtain ⟨h, hh, hpos⟩ := hθ (ε / A) (div_pos hε hA)
  refine ⟨fun y => h (f y), Pending.AdmissiblePresentationPullback.chartSmooth_comp hf hh, ?_⟩
  intro e z hz v
  set d := complexChartAt (n := n) (f (e.val.symm z))
  have hzd : z ∈ HolomorphicMaps.coordinateDomain f e d := ⟨hz, mem_complexChartAt_source _⟩
  set F := HolomorphicMaps.coordinateMap f e d
  set L := fderiv ℝ F z
  have hFz : F z ∈ d.val.target := HolomorphicMaps.coordinateMap_mem_target hzd
  have hvec (u w : ComplexModel n) : L ∘ ![u, w] = ![L u, L w] := by
    funext i
    fin_cases i <;> rfl
  have hLI : L (Complex.I • v) = Complex.I • L v :=
    HolomorphicMaps.coordinateMap_fderiv_map_smul_complex hf e d hzd Complex.I v
  -- the pulled-back positivity of `θ + ddᶜ h + (ε / A) ω`
  have h1 := hpos d (F z) hFz (L v)
  -- the domination `-f^*ω + A ω_Y ≥ 0`
  have h2 := hdom e z hz v
  have hθc : (ClosedRealOneOneForm.pullback hf θ).val.coeff e z ![v, Complex.I • v] =
      θ.val.coeff d (F z) ![L v, Complex.I • L v] := by
    rw [ClosedRealOneOneForm.pullback_val, SmoothRealForm.pullback_coeff hf _ e d hzd,
      ContinuousAlternatingMap.compContinuousLinearMap_apply, hvec, hLI]
  have hωc : (ClosedRealOneOneForm.pullback hf omega.form).val.coeff e z ![v, Complex.I • v] =
      omega.form.val.coeff d (F z) ![L v, Complex.I • L v] := by
    rw [ClosedRealOneOneForm.pullback_val, SmoothRealForm.pullback_coeff hf _ e d hzd,
      ContinuousAlternatingMap.compContinuousLinearMap_apply, hvec, hLI]
  have hddc : smoothDDC (fun y => h (f (e.val.symm y))) z ![v, Complex.I • v] =
      smoothDDC (fun w => h (d.val.symm w)) (F z) ![L v, Complex.I • L v] := by
    rw [smoothDDC_comp_chart hf hh e d hzd,
      ContinuousAlternatingMap.compContinuousLinearMap_apply, hvec, hLI]
  simp only [ContinuousAlternatingMap.add_apply, ContinuousAlternatingMap.smul_apply,
    smul_eq_mul] at h1 ⊢
  simp only [ClosedRealOneOneForm.coeff_add, ClosedRealOneOneForm.coeff_smul,
    ClosedRealOneOneForm.coeff_neg, ContinuousAlternatingMap.add_apply,
    ContinuousAlternatingMap.smul_apply, ContinuousAlternatingMap.neg_apply,
    smul_eq_mul] at h2
  rw [hθc, hddc]
  rw [hωc] at h2
  have h3 : 0 ≤ (ε / A) * (-omega.form.val.coeff d (F z) ![L v, Complex.I • L v] +
      A * omegaY.form.val.coeff e z ![v, Complex.I • v]) :=
    mul_nonneg (div_pos hε hA).le h2
  have hkey : (ε / A) * (-omega.form.val.coeff d (F z) ![L v, Complex.I • L v] +
      A * omegaY.form.val.coeff e z ![v, Complex.I • v]) =
      -(ε / A * omega.form.val.coeff d (F z) ![L v, Complex.I • L v]) +
        ε * omegaY.form.val.coeff e z ![v, Complex.I • v] := by
    field_simp
  linarith [h1, h3, hkey]

/-- **Nef classes pull back to nef classes** on a compact manifold (`prop:cones_modif`, item 1,
for any holomorphic map from a compact Kähler manifold). -/
theorem classNef_classPullback [CompactSpace Y] {f : Y → X}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ f)
    (omega : KahlerBackground n X) (omegaY : KahlerBackground n Y)
    {α : RealBottChern n X} (hα : ClassNefWithRespectTo omega α) :
    ClassNefWithRespectTo omegaY (classPullback hf α) := by
  induction α using Quotient.inductionOn with
  | h θ => exact nefWithRespectTo_pullback hf omega omegaY hα

/-- Pseudo-effectivity pulls back along a modification. -/
theorem classPseudoeffective_classPullback {π : Y → X}
    (hπ : AnalyticModificationLocalDiscrepancy.IsAnalyticModification (n := n) π)
    {α : RealBottChern n X} (hα : ClassPseudoeffectiveViaPotentials α) :
    ClassPseudoeffectiveViaPotentials (classPullback hπ.1 α) := by
  induction α using Quotient.inductionOn with
  | h θ =>
    obtain ⟨u, hu⟩ := hα
    exact ⟨_, AnalyticModificationStrongPullback.isThetaPshPotential_comp_of_isAnalyticModification
      hπ θ hu⟩

/-- Pseudo-effectivity descends along a modification of a compact manifold: a `π^*θ`-psh
potential is the pull-back of a `θ`-psh potential. -/
theorem classPseudoeffective_of_classPullback [CompactSpace X] {π : Y → X}
    (hπ : AnalyticModificationLocalDiscrepancy.IsAnalyticModification (n := n) π)
    {α : RealBottChern n X} (hα : ClassPseudoeffectiveViaPotentials (classPullback hπ.1 α)) :
    ClassPseudoeffectiveViaPotentials α := by
  induction α using Quotient.inductionOn with
  | h θ =>
    obtain ⟨w, hw⟩ := hα
    obtain ⟨ψ, hψ, _⟩ :=
      AnalyticModificationPotentialDescent.exists_descent_of_isAnalyticModification hπ θ hw
    exact ⟨ψ, hψ⟩

/-- Along a modification of a compact manifold, `π^*α` is pseudo-effective iff `α` is. -/
theorem classPseudoeffective_classPullback_iff [CompactSpace X] {π : Y → X}
    (hπ : AnalyticModificationLocalDiscrepancy.IsAnalyticModification (n := n) π)
    (α : RealBottChern n X) :
    ClassPseudoeffectiveViaPotentials (classPullback hπ.1 α) ↔
      ClassPseudoeffectiveViaPotentials α :=
  ⟨classPseudoeffective_of_classPullback hπ, classPseudoeffective_classPullback hπ⟩

end SGPT.BDivisor
