import SGPT.Projective.NumEqHodgeIndex
import SGPT.Foundations.Analysis.FirstPass.ClosedFormPullback
import SGPT.Foundations.Analysis.FirstPass.FormPullbackFunctorial
import SGPT.Foundations.Analysis.FirstPass.HolomorphicDDC

/-!
# Numerical equivalence of real `(1,1)`-classes: degrees on curves

Lane NUMEQ, blueprint `claude-numeq.tex`.  Source: `prop:Okounonlydepnum` ("`Δ_ν(L)` depends only
on the numerical class of `L`") and `rmk:bdiv:L749` (Dang–Favre's numerical classes).

The **degree** of a closed real `(1,1)`-form `θ` on a complex manifold `X` along a holomorphic map
`g : C → X` from a compact Riemann surface `C` is `∫_C g^*θ` (`degreeAlong`; the integral is the
slot integral of TN, read against any Kähler form `κ` of `C`).  For `θ = c₁(L, h)` the curvature of
a Hermitian line bundle and `g` the normalization of an irreducible curve `Γ ⊆ X`, this is the
intersection number `L · Γ`; a non-constant `g` factors through the normalization of `g(C)`,
multiplying the degree by `deg(C → g(C))`, and a constant `g` has degree `0`.  Hence

* `IsNumericallyTrivial θ` (`∫_C g^*θ = 0` for all compact connected Riemann surfaces `C` and all
  holomorphic `g : C → X`) is the book's "`α · Γ = 0` for every curve `Γ ⊆ X`", and
* `NumericallyEquivalent θ θ'` (equal degrees along every such `g`) is numerical equivalence.

Main results:

* `bottChernRel_pullback`: pullback along holomorphic maps (any dimensions) respects Bott–Chern
  equivalence; hence degrees, numerical triviality and numerical equivalence only depend on the
  real Bott–Chern classes (`degreeAlong_eq_of_bottChernRel`,
  `isNumericallyTrivial_iff_of_bottChernRel`, `numericallyEquivalent_of_ofRepresentative_eq`,
  the easy direction "cohomologous ⇒ numerically equivalent");
* `ofRepresentative_eq_zero_of_slotIntegral_eq_zero_dim_one`,
  `ofRepresentative_eq_of_numericallyEquivalent_dim_one`: **on a compact connected Kähler curve,
  numerically equivalent classes are equal** (the identity map is a curve; a class of degree `0`
  vanishes, via its constant-trace representative);
* `isNumericallyTrivial_iff_dim_one`: on a compact connected Kähler curve, a class is numerically
  trivial iff it is zero.

In dimension `n ≥ 2` the Hodge index theorem (`SGPT.Projective.NumEq.hodgeIndex`) reduces
"numerically trivial ⇒ zero" to the vanishing of `α · {ω}^{n-1}` and `α² · {ω}^{n-2}` for a
Kähler form `ω` of algebraic class; deriving these from the degrees on curves needs
complete-intersection curves (Bertini) and the Lelong–Poincaré formula on them, which is not
formalized.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Manifold ContDiff

universe u

namespace SGPT.Projective.NumEq

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.Pending
  SGPT.Foundations.Analysis.Pending.IntegrationCurrent
  SGPT.Foundations.Analysis.Pending.MixedMassClassInvariance SGPT.Foundations.Analysis.Pending.NefMixedMass

/-! ### Pullback and Bott–Chern equivalence -/

section Pullback

variable {k n : ℕ} {V M : Type*}
  [TopologicalSpace V] [ChartedSpace (ComplexModel k) V] [IsComplexManifold k V]
  [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- Chart-smooth functions pull back to chart-smooth functions along holomorphic maps. -/
theorem chartSmooth_comp_holomorphic {g : V → M}
    (hg : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ g) {h : M → ℝ}
    (hh : ChartSmooth (n := n) h) : ChartSmooth (n := k) (fun z => h (g z)) := by
  intro e u hu
  set d := complexChartAt (n := n) (g (e.val.symm u))
  have hud : u ∈ HolomorphicMaps.coordinateDomain g e d := ⟨hu, mem_complexChartAt_source _⟩
  have h1 := HolomorphicMaps.coordinateMap_contDiffAt_real hg e d hud
  have h2 := (hh d).contDiffAt
    (d.val.open_target.mem_nhds (HolomorphicMaps.coordinateMap_mem_target hud))
  have h3 := ContDiffAt.comp (g := fun z => h (d.val.symm z)) u h2 h1
  refine (h3.congr_of_eventuallyEq ?_).contDiffWithinAt
  filter_upwards [(HolomorphicMaps.coordinateDomain_isOpen hg e d).mem_nhds hud] with u' hu'
  show h (g (e.val.symm u')) = h (d.val.symm (d.val (g (e.val.symm u'))))
  rw [d.val.left_inv hu'.2]

/-- **Pullback respects Bott–Chern equivalence**: `θ' = θ + ddᶜh` gives
`g^*θ' = g^*θ + ddᶜ(h ∘ g)` for every holomorphic map `g` (any dimensions). -/
theorem bottChernRel_pullback {g : V → M}
    (hg : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ g)
    {θ θ' : ClosedRealOneOneForm n M} (h : ClosedRealOneOneForm.BottChernRel θ θ') :
    ClosedRealOneOneForm.BottChernRel (ClosedRealOneOneForm.pullback hg θ)
      (ClosedRealOneOneForm.pullback hg θ') := by
  obtain ⟨h, hh, heq⟩ := h
  refine ⟨fun z => h (g z), chartSmooth_comp_holomorphic hg hh, fun e z hz => ?_⟩
  set d := complexChartAt (n := n) (g (e.val.symm z))
  have hzd : z ∈ HolomorphicMaps.coordinateDomain g e d := ⟨hz, mem_complexChartAt_source _⟩
  have hD := HolomorphicMaps.coordinateDomain_isOpen hg e d
  have hddc : smoothDDC (fun y => h (g (e.val.symm y))) z =
      (smoothDDC (fun w => h (d.val.symm w)) (HolomorphicMaps.coordinateMap g e d z)).compContinuousLinearMap
        (fderiv ℝ (HolomorphicMaps.coordinateMap g e d) z) := by
    rw [← HolomorphicDDC.smoothDDC_comp hD d.val.open_target
      (HolomorphicMaps.coordinateMap_contDiffOn hg e d) (hh d)
      (fun _ hy => HolomorphicMaps.coordinateMap_mem_target hy) hzd]
    apply smoothDDC_congr
    filter_upwards [hD.mem_nhds hzd] with y hy
    show h (g (e.val.symm y)) = h (d.val.symm (d.val (g (e.val.symm y))))
    rw [d.val.left_inv hy.2]
  rw [ClosedRealOneOneForm.pullback_val, ClosedRealOneOneForm.pullback_val,
    SmoothRealForm.pullback_coeff hg _ e d hzd, SmoothRealForm.pullback_coeff hg _ e d hzd,
    hddc, heq d _ (HolomorphicMaps.coordinateMap_mem_target hzd)]
  ext v
  simp

end Pullback

/-! ### Degrees along curves -/

section Degree

variable {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X]

/-- **The degree of `θ` along a curve** `g : C → X` (`C` a compact Riemann surface with a Kähler
form `κ`, `g` holomorphic): `∫_C g^*θ`. For `θ = c₁(L, h)` and `g` the normalization of an
irreducible curve `Γ`, this is `L · Γ`. -/
def degreeAlong {C : Type*} [TopologicalSpace C] [ChartedSpace (ComplexModel 1) C]
    [IsComplexManifold 1 C] [CompactSpace C] (κ : KahlerBackground 1 C) {g : C → X}
    (hg : ContMDiff 𝓘(ℂ, ComplexModel 1) 𝓘(ℂ, ComplexModel n) ∞ g)
    (θ : ClosedRealOneOneForm n X) : ℝ :=
  letI : MeasurableSpace C := borel C
  haveI : BorelSpace C := ⟨rfl⟩
  slotIntegral κ (fun _ => ClosedRealOneOneForm.pullback hg θ)

/-- **Numerical triviality**: `θ` has degree `0` along every holomorphic map from a compact
connected Riemann surface (equivalently, `{θ} · Γ = 0` for every irreducible curve `Γ ⊆ X`). -/
def IsNumericallyTrivial (θ : ClosedRealOneOneForm n X) : Prop :=
  ∀ (C : Type u) [TopologicalSpace C] [ChartedSpace (ComplexModel 1) C] [IsComplexManifold 1 C]
    [CompactSpace C] [ConnectedSpace C] (κ : KahlerBackground 1 C) (g : C → X)
    (hg : ContMDiff 𝓘(ℂ, ComplexModel 1) 𝓘(ℂ, ComplexModel n) ∞ g), degreeAlong κ hg θ = 0

/-- **Numerical equivalence**: `θ` and `θ'` have the same degree along every holomorphic map from a
compact connected Riemann surface (equivalently, `{θ} · Γ = {θ'} · Γ` for every curve `Γ`). -/
def NumericallyEquivalent (θ θ' : ClosedRealOneOneForm n X) : Prop :=
  ∀ (C : Type u) [TopologicalSpace C] [ChartedSpace (ComplexModel 1) C] [IsComplexManifold 1 C]
    [CompactSpace C] [ConnectedSpace C] (κ : KahlerBackground 1 C) (g : C → X)
    (hg : ContMDiff 𝓘(ℂ, ComplexModel 1) 𝓘(ℂ, ComplexModel n) ∞ g),
    degreeAlong κ hg θ = degreeAlong κ hg θ'

theorem numericallyEquivalent_refl (θ : ClosedRealOneOneForm n X) : NumericallyEquivalent θ θ :=
  fun _ _ _ _ _ _ _ _ _ => rfl

theorem NumericallyEquivalent.symm {θ θ' : ClosedRealOneOneForm n X}
    (h : NumericallyEquivalent θ θ') : NumericallyEquivalent θ' θ :=
  fun C _ _ _ _ _ κ g hg => (h C κ g hg).symm

theorem NumericallyEquivalent.trans {θ θ' θ'' : ClosedRealOneOneForm n X}
    (h : NumericallyEquivalent θ θ') (h' : NumericallyEquivalent θ' θ'') :
    NumericallyEquivalent θ θ'' :=
  fun C _ _ _ _ _ κ g hg => (h C κ g hg).trans (h' C κ g hg)

/-- **Degrees only depend on the Bott–Chern class.** -/
theorem degreeAlong_eq_of_bottChernRel {C : Type*} [TopologicalSpace C]
    [ChartedSpace (ComplexModel 1) C] [IsComplexManifold 1 C] [CompactSpace C]
    (κ : KahlerBackground 1 C) {g : C → X}
    (hg : ContMDiff 𝓘(ℂ, ComplexModel 1) 𝓘(ℂ, ComplexModel n) ∞ g)
    {θ θ' : ClosedRealOneOneForm n X} (h : ClosedRealOneOneForm.BottChernRel θ θ') :
    degreeAlong κ hg θ = degreeAlong κ hg θ' := by
  let _ : MeasurableSpace C := borel C
  have _ : BorelSpace C := ⟨rfl⟩
  exact SGPT.Hodge.BDivChain.SourceMixedOrderDraft.slotIntegral_eq_of_bottChernRel κ _ _
    fun _ => bottChernRel_pullback hg h

/-- **Cohomologous forms are numerically equivalent** (the cycle class map is well defined on
numerical classes). -/
theorem numericallyEquivalent_of_ofRepresentative_eq {θ θ' : ClosedRealOneOneForm n X}
    (h : RealBottChern.ofRepresentative θ = RealBottChern.ofRepresentative θ') :
    NumericallyEquivalent θ θ' :=
  fun _ _ _ _ _ _ κ _ hg =>
    degreeAlong_eq_of_bottChernRel κ hg ((RealBottChern.ofRepresentative_eq_iff θ θ').mp h)

theorem isNumericallyTrivial_iff_numericallyEquivalent_zero (θ : ClosedRealOneOneForm n X) :
    IsNumericallyTrivial θ ↔ NumericallyEquivalent θ 0 := by
  have h0 : ∀ {C : Type u} [TopologicalSpace C] [ChartedSpace (ComplexModel 1) C]
      [IsComplexManifold 1 C] [CompactSpace C] (κ : KahlerBackground 1 C) {g : C → X}
      (hg : ContMDiff 𝓘(ℂ, ComplexModel 1) 𝓘(ℂ, ComplexModel n) ∞ g),
      degreeAlong κ hg (0 : ClosedRealOneOneForm n X) = 0 := by
    intro C _ _ _ _ κ g hg
    let _ : MeasurableSpace C := borel C
    have _ : BorelSpace C := ⟨rfl⟩
    have hz : ClosedRealOneOneForm.pullback hg (0 : ClosedRealOneOneForm n X) = 0 := by
      ext e z v
      simp [SmoothRealForm.pullback, SmoothRealForm.pullbackCoeff,
        SmoothRealForm.chartPullbackCoeff]
    unfold degreeAlong
    rw [hz]
    have := SGPT.Hodge.BDivChain.SourceMixedOrderDraft.slotIntegral_update_zero κ
      (fun _ => (0 : ClosedRealOneOneForm 1 C)) 0
    simpa using this
  constructor
  · intro h C _ _ _ _ _ κ g hg
    rw [h C κ g hg, h0 κ hg]
  · intro h C _ _ _ _ _ κ g hg
    rw [h C κ g hg, h0 κ hg]

/-- Numerical triviality only depends on the Bott–Chern class. -/
theorem isNumericallyTrivial_iff_of_bottChernRel {θ θ' : ClosedRealOneOneForm n X}
    (h : ClosedRealOneOneForm.BottChernRel θ θ') :
    IsNumericallyTrivial θ ↔ IsNumericallyTrivial θ' :=
  ⟨fun hθ C _ _ _ _ _ κ g hg => (degreeAlong_eq_of_bottChernRel κ hg h).symm.trans (hθ C κ g hg),
    fun hθ C _ _ _ _ _ κ g hg => (degreeAlong_eq_of_bottChernRel κ hg h).trans (hθ C κ g hg)⟩

/-- **Cohomologically trivial classes are numerically trivial.** -/
theorem isNumericallyTrivial_of_ofRepresentative_eq_zero {θ : ClosedRealOneOneForm n X}
    (h : RealBottChern.ofRepresentative θ = 0) : IsNumericallyTrivial θ :=
  (isNumericallyTrivial_iff_numericallyEquivalent_zero θ).mpr
    (numericallyEquivalent_of_ofRepresentative_eq (h.trans RealBottChern.ofRepresentative_zero.symm))

end Degree

/-! ### Curves: numerical equivalence is cohomological equivalence -/

section DimOne

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel 1) M]
  [IsComplexManifold 1 M]

theorem fun_eq_update_dim_one (w : KahlerBackground 1 M) (η : ClosedRealOneOneForm 1 M) :
    (fun _ : Fin 1 => η) = Function.update (fun _ : Fin 1 => w.form) 0 η := by
  funext i
  rw [Fin.fin_one_eq_zero i, Function.update_self]

/-- A class of degree `0` on a compact connected Kähler curve is zero. -/
theorem ofRepresentative_eq_zero_of_slotIntegral_eq_zero_dim_one [MeasurableSpace M]
    [BorelSpace M] [CompactSpace M] [ConnectedSpace M] (w : KahlerBackground 1 M)
    (θ : ClosedRealOneOneForm 1 M) (h : slotIntegral w (fun _ => θ) = 0) :
    RealBottChern.ofRepresentative θ = 0 := by
  obtain ⟨γ, ⟨c, hc⟩, hrel⟩ := SGPT.Hodge.exists_constantTrace_bottChernRel w θ
  have hγ0 : slotIntegral w (fun _ => γ) = 0 := by
    rw [← SGPT.Hodge.BDivChain.SourceMixedOrderDraft.slotIntegral_eq_of_bottChernRel w
      (fun _ => θ) (fun _ => γ) (fun _ => hrel)]
    exact h
  have htr : ∀ x, topRatio w.form.val (slotForm (fun _ : Fin 1 => γ)) x = c := by
    intro x
    rw [fun_eq_update_dim_one w γ, topRatio_update_zero (m := 0), hc]
    simp
  have hc0 : c = 0 := by
    unfold slotIntegral at hγ0
    simp_rw [htr] at hγ0
    rw [integral_const, smul_eq_mul] at hγ0
    exact (mul_eq_zero.mp hγ0).resolve_left
      (KahlerLaplacianSolvability.kahlerVolume_real_univ_pos w).ne'
  have hpt : ∀ x, pointMatrix γ.val x = 0 := by
    intro x
    have h1 := htr x
    rw [hc0, topRatio_slotForm_eq] at h1
    have hd := SGPT.NPP.LogConcavity.det_re_pos (pointMatrix_posDef w x)
    have hre : (FirstPass.MixedMongeAmpere.mixedCoefficient
        (fun _ : Fin 1 => pointMatrix γ.val x)).re = 0 :=
      (div_eq_zero_iff.mp h1).resolve_right (mul_pos (by positivity) hd).ne'
    rw [FirstPass.MixedMongeAmpere.mixedCoefficient_diagonal, Matrix.det_fin_one] at hre
    simp only [Nat.factorial_one, Nat.cast_one, one_mul] at hre
    have him : (pointMatrix γ.val x 0 0).im = 0 := by
      have := (pointMatrix_isHermitian γ x).apply 0 0
      exact Complex.conj_eq_iff_im.mp this
    ext i j
    rw [Fin.fin_one_eq_zero i, Fin.fin_one_eq_zero j]
    exact Complex.ext hre him
  rw [(RealBottChern.ofRepresentative_eq_iff θ γ).mpr hrel,
    RealBottChern.ofRepresentative_eq_of_geometricallyEq
      (geometricallyEq_zero_of_pointMatrix_eq_zero hpt),
    RealBottChern.ofRepresentative_zero]

/-- Equal degrees along the identity give equal classes on a compact connected Kähler curve. -/
theorem ofRepresentative_eq_of_slotIntegral_pullback_id_eq [MeasurableSpace M] [BorelSpace M]
    [CompactSpace M] [ConnectedSpace M] (w : KahlerBackground 1 M)
    {θ θ' : ClosedRealOneOneForm 1 M}
    (hid : slotIntegral w (fun _ => ClosedRealOneOneForm.pullback
        (contMDiff_id (I := 𝓘(ℂ, ComplexModel 1)) (n := ∞)) θ) =
      slotIntegral w (fun _ => ClosedRealOneOneForm.pullback
        (contMDiff_id (I := 𝓘(ℂ, ComplexModel 1)) (n := ∞)) θ')) :
    RealBottChern.ofRepresentative θ = RealBottChern.ofRepresentative θ' := by
  have hpb : ∀ η : ClosedRealOneOneForm 1 M,
      slotIntegral w (fun _ => ClosedRealOneOneForm.pullback
        (contMDiff_id (I := 𝓘(ℂ, ComplexModel 1)) (n := ∞)) η) = slotIntegral w (fun _ => η) :=
    fun η => SGPT.Hodge.BDivChain.SourceMixedOrderDraft.slotIntegral_eq_of_bottChernRel w _ _
      fun _ => (RealBottChern.ofRepresentative_eq_iff _ _).mp
        (ClosedRealOneOneForm.ofRepresentative_pullback_id η)
  rw [hpb, hpb] at hid
  have hsub : slotIntegral w (fun _ => θ - θ') = 0 := by
    have hm := (SGPT.Hodge.BDivChain.SourceMixedOrderDraft.slotIntegralMultilinear w).map_update_sub
      (fun _ => w.form) 0 θ θ'
    simp only [SGPT.Hodge.BDivChain.SourceMixedOrderDraft.slotIntegralMultilinear,
      MultilinearMap.mk'_apply] at hm
    rw [← fun_eq_update_dim_one, ← fun_eq_update_dim_one, ← fun_eq_update_dim_one] at hm
    rw [hm, hid, sub_self]
  have h0 := ofRepresentative_eq_zero_of_slotIntegral_eq_zero_dim_one w _ hsub
  have hs : RealBottChern.ofRepresentative (θ - θ') =
      RealBottChern.ofRepresentative θ - RealBottChern.ofRepresentative θ' := by
    rw [sub_eq_add_neg, RealBottChern.ofRepresentative_add, RealBottChern.ofRepresentative_neg,
      ← sub_eq_add_neg]
  rw [← sub_eq_zero, ← hs]
  exact h0

/-- **On a compact connected Kähler curve, numerically equivalent classes are equal.** -/
theorem ofRepresentative_eq_of_numericallyEquivalent_dim_one [CompactSpace M] [ConnectedSpace M]
    (w : KahlerBackground 1 M) {θ θ' : ClosedRealOneOneForm 1 M}
    (h : NumericallyEquivalent θ θ') :
    RealBottChern.ofRepresentative θ = RealBottChern.ofRepresentative θ' := by
  have hid := h M w id (contMDiff_id (I := 𝓘(ℂ, ComplexModel 1)) (n := ∞))
  unfold degreeAlong at hid
  let _ : MeasurableSpace M := borel M
  have _ : BorelSpace M := ⟨rfl⟩
  exact ofRepresentative_eq_of_slotIntegral_pullback_id_eq w hid

/-- **On a compact connected Kähler curve, numerical triviality is cohomological triviality.** -/
theorem isNumericallyTrivial_iff_dim_one [CompactSpace M] [ConnectedSpace M]
    (w : KahlerBackground 1 M) (θ : ClosedRealOneOneForm 1 M) :
    IsNumericallyTrivial θ ↔ RealBottChern.ofRepresentative θ = 0 := by
  refine ⟨fun h => ?_, isNumericallyTrivial_of_ofRepresentative_eq_zero⟩
  have := ofRepresentative_eq_of_numericallyEquivalent_dim_one w
    ((isNumericallyTrivial_iff_numericallyEquivalent_zero θ).mp h)
  rwa [RealBottChern.ofRepresentative_zero] at this

end DimOne

end SGPT.Projective.NumEq
