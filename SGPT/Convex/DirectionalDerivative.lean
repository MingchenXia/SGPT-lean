import SGPT.Convex.SubgradientBounds
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Cone.Extension

namespace SGPT.Convex

open Set Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem isConvex_comp_affineMap {W : Type*} [AddCommGroup W] [Module ℝ W]
    {f : E → EReal} (hf : IsConvex f) (L : W →ᵃ[ℝ] E) :
    IsConvex (f ∘ L) := by
  let T := L.prodMap (AffineMap.id ℝ ℝ)
  change Convex ℝ (T ⁻¹' epigraph f)
  exact hf.affine_preimage T

/-- The actual scalar line restriction, using the real values near a finite point. -/
def lineProfile (f : E → EReal) (x v : E) (t : ℝ) : ℝ :=
  (f (x + t • v)).toReal

/-- The actual effective domain of the scalar line restriction. -/
def lineDomain (f : E → EReal) (x v : E) : Set ℝ :=
  {t | x + t • v ∈ effectiveDomain f}

/-- The real right derivative of the actual scalar line profile. -/
noncomputable def realDirectionalDerivative (f : E → EReal) (x v : E) : ℝ :=
  derivWithin (lineProfile f x v) (Ioi 0) 0

theorem convexOn_lineProfile {f : E → EReal} (hf : IsProper f) (x v : E) :
    ConvexOn ℝ (lineDomain f x v) (lineProfile f x v) := by
  let L : ℝ →ᵃ[ℝ] E := AffineMap.lineMap x (x + v)
  have hL (t : ℝ) : L t = x + t • v := by
    simp [L, AffineMap.lineMap_apply_module', add_comm]
  have h := (convexOn_toReal_effectiveDomain hf).comp_affineMap L
  convert! h using 1
  · ext t
    simp only [Set.mem_preimage, lineDomain, Set.mem_ofPred_eq, hL]
  · funext t
    simp only [Function.comp_apply, lineProfile, hL]

theorem zero_mem_interior_lineDomain {f : E → EReal} {x : E}
    (hx : x ∈ interior (effectiveDomain f)) (v : E) :
    (0 : ℝ) ∈ interior (lineDomain f x v) := by
  have hc : ContinuousAt (fun t : ℝ ↦ x + t • v) 0 := by fun_prop
  have hd : effectiveDomain f ∈ 𝓝 (x + (0 : ℝ) • v) := by
    simpa using mem_interior_iff_mem_nhds.mp hx
  exact mem_interior_iff_mem_nhds.mpr (hc.preimage_mem_nhds hd)

theorem hasDerivWithinAt_lineProfile {f : E → EReal} (hf : IsProper f) {x : E}
    (hx : x ∈ interior (effectiveDomain f)) (v : E) :
    HasDerivWithinAt (lineProfile f x v) (realDirectionalDerivative f x v) (Ioi 0) 0 :=
  (convexOn_lineProfile hf x v).hasDerivWithinAt_rightDeriv_of_mem_interior
    (zero_mem_interior_lineDomain hx v)

theorem tendsto_real_directional_secant {f : E → EReal} (hf : IsProper f) {x : E}
    (hx : x ∈ interior (effectiveDomain f)) (v : E) :
    Tendsto (fun t : ℝ ↦ ((f (x + t • v)).toReal - (f x).toReal) / t)
      (𝓝[>] 0) (𝓝 (realDirectionalDerivative f x v)) := by
  have h := (hasDerivWithinAt_iff_tendsto_slope' (by simp : (0 : ℝ) ∉ Ioi 0)).mp
    (hasDerivWithinAt_lineProfile hf hx v)
  convert h using 1
  funext t
  simp [slope, lineProfile, div_eq_mul_inv, smul_eq_mul, mul_comm]

theorem realDirectionalDerivative_zero (f : E → EReal) (x : E) :
    realDirectionalDerivative f x 0 = 0 := by
  have hp : lineProfile f x 0 = fun _ : ℝ ↦ (f x).toReal := by
    funext t
    simp [lineProfile]
  simp [realDirectionalDerivative, hp]

theorem realDirectionalDerivative_pos_smul {f : E → EReal} (hf : IsProper f)
    {x : E} (hx : x ∈ interior (effectiveDomain f)) (a : ℝ) (ha : 0 < a) (v : E) :
    realDirectionalDerivative f x (a • v) = a * realDirectionalDerivative f x v := by
  have hscale : HasDerivWithinAt (fun t : ℝ ↦ a * t) a (Ioi 0) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).const_mul a).hasDerivWithinAt
  have hmaps : MapsTo (fun t : ℝ ↦ a * t) (Ioi 0) (Ioi 0) :=
    fun t ht ↦ mul_pos ha ht
  have hcomp := (hasDerivWithinAt_lineProfile hf hx v).comp_of_eq 0 hscale hmaps
    (by simp)
  have hfun : lineProfile f x (a • v) = lineProfile f x v ∘ (fun t : ℝ ↦ a * t) := by
    funext t
    simp only [lineProfile, Function.comp_apply, smul_smul, mul_comm]
  have h := hfun ▸ hcomp
  have hd := h.derivWithin (uniqueDiffWithinAt_Ioi (0 : ℝ))
  change realDirectionalDerivative f x (a • v) = _ at hd
  rw [hd, mul_comm]

theorem realDirectionalDerivative_add_le {f : E → EReal} (hf : IsProper f)
    {x : E} (hx : x ∈ interior (effectiveDomain f)) (u v : E) :
    realDirectionalDerivative f x (u + v) ≤
      realDirectionalDerivative f x u + realDirectionalDerivative f x v := by
  let q (w : E) (t : ℝ) := ((f (x + t • w)).toReal - (f x).toReal) / t
  have hlim (w : E) : Tendsto (q w) (𝓝[>] 0) (𝓝 (realDirectionalDerivative f x w)) :=
    tendsto_real_directional_secant hf hx w
  have hlim₂ := ((hlim ((2 : ℝ) • u)).add (hlim ((2 : ℝ) • v))).div_const 2
  have hlimright : Tendsto (fun t ↦ (q ((2 : ℝ) • u) t + q ((2 : ℝ) • v) t) / 2)
      (𝓝[>] 0) (𝓝 (realDirectionalDerivative f x u + realDirectionalDerivative f x v)) := by
    convert hlim₂ using 1
    rw [realDirectionalDerivative_pos_smul hf hx 2 (by norm_num),
      realDirectionalDerivative_pos_smul hf hx 2 (by norm_num)]
    congr 1
    ring
  apply le_of_tendsto_of_tendsto (hlim (u + v)) hlimright
  have hdu₀ : ∀ᶠ t in 𝓝 (0 : ℝ), t ∈ lineDomain f x ((2 : ℝ) • u) :=
    mem_interior_iff_mem_nhds.mp (zero_mem_interior_lineDomain hx ((2 : ℝ) • u))
  have hdv₀ : ∀ᶠ t in 𝓝 (0 : ℝ), t ∈ lineDomain f x ((2 : ℝ) • v) :=
    mem_interior_iff_mem_nhds.mp (zero_mem_interior_lineDomain hx ((2 : ℝ) • v))
  have hdu : ∀ᶠ t in 𝓝[>] (0 : ℝ), t ∈ lineDomain f x ((2 : ℝ) • u) :=
    hdu₀.filter_mono nhdsWithin_le_nhds
  have hdv : ∀ᶠ t in 𝓝[>] (0 : ℝ), t ∈ lineDomain f x ((2 : ℝ) • v) :=
    hdv₀.filter_mono nhdsWithin_le_nhds
  filter_upwards [hdu, hdv, self_mem_nhdsWithin] with t htu htv ht
  have hcombo := (convexOn_toReal_effectiveDomain hf).2 htu htv
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  have heq : (1 / 2 : ℝ) • (x + t • ((2 : ℝ) • u)) +
      (1 / 2 : ℝ) • (x + t • ((2 : ℝ) • v)) = x + t • (u + v) := by module
  rw [heq] at hcombo
  simp only [smul_eq_mul] at hcombo
  change (0 : ℝ) < t at ht
  dsimp only [q]
  calc
    ((f (x + t • (u + v))).toReal - (f x).toReal) / t ≤
      (((f (x + t • ((2 : ℝ) • u))).toReal +
        (f (x + t • ((2 : ℝ) • v))).toReal) / 2 - (f x).toReal) / t :=
      div_le_div_of_nonneg_right (by linarith [hcombo]) ht.le
    _ = (((f (x + t • ((2 : ℝ) • u))).toReal - (f x).toReal) / t +
      ((f (x + t • ((2 : ℝ) • v))).toReal - (f x).toReal) / t) / 2 := by ring

theorem realDirectionalDerivative_le_difference {f : E → EReal} (hf : IsProper f)
    {x : E} (hx : x ∈ interior (effectiveDomain f)) {v : E}
    (hv : x + v ∈ effectiveDomain f) :
    realDirectionalDerivative f x v ≤ (f (x + v)).toReal - (f x).toReal := by
  have h := (convexOn_lineProfile hf x v).rightDeriv_le_slope_of_mem_interior
    (zero_mem_interior_lineDomain hx v) (y := 1)
    (by simpa [lineDomain] using hv) (by norm_num)
  simpa [realDirectionalDerivative, slope, lineProfile] using h

/-- Actual Hahn--Banach domination with a prescribed attained sublinear value. -/
theorem exists_linearMap_le_sublinear_eq_of_ne_zero (N : E → ℝ)
    (hzero : N 0 = 0)
    (hhom : ∀ a : ℝ, 0 < a → ∀ w, N (a • w) = a * N w)
    (hadd : ∀ u v, N (u + v) ≤ N u + N v) {v : E} (hv : v ≠ 0) :
    ∃ L : E →ₗ[ℝ] ℝ, (∀ w, L w ≤ N w) ∧ L v = N v := by
  let p : Submodule ℝ E := ℝ ∙ v
  let e : ℝ ≃ₗ[ℝ] p := LinearEquiv.toSpanNonzeroSingleton ℝ E v hv
  let g : p →ₗ[ℝ] ℝ := (N v) • e.symm.toLinearMap
  have hdom (w : p) : g w ≤ N w := by
    let a : ℝ := e.symm w
    have hw : (w : E) = a • v :=
      (LinearEquiv.toSpanNonzeroSingleton_symm_apply_smul ℝ E v hv w).symm
    have hgw : g w = a * N v := by simp [g, a, mul_comm]
    rw [hgw, hw]
    rcases lt_trichotomy a 0 with ha | ha | ha
    · have hneg : 0 ≤ N v + N (-v) := by
        simpa only [add_neg_cancel, hzero] using hadd v (-v)
      have hNv : N (a • v) = (-a) * N (-v) := by
        rw [show a • v = (-a) • (-v) by simp,
          hhom (-a) (by linarith) (-v)]
      rw [hNv]
      nlinarith
    · simp [ha, hzero]
    · rw [hhom a ha v]
  obtain ⟨L, hext, hbound⟩ := exists_extension_of_le_sublinear ⟨p, g⟩ N hhom hadd hdom
  have hvp : v ∈ p := Submodule.mem_span_singleton_self v
  have heone : e 1 = (⟨v, hvp⟩ : p) :=
    LinearEquiv.toSpanNonzeroSingleton_one ℝ E v hv
  have hgv : g ⟨v, hvp⟩ = N v := by
    rw [← heone]
    simp [g]
  exact ⟨L, hbound, (hext ⟨v, hvp⟩).trans hgv⟩

variable [FiniteDimensional ℝ E]

/-- The genuine dominated functional is an actual subgradient attaining the
actual one-sided derivative at an ordinary-interior domain point. -/
theorem exists_subgradient_attaining_realDirectionalDerivative_of_ne_zero
    {f : E → EReal} (hf : IsProper f) {x : E}
    (hx : x ∈ interior (effectiveDomain f)) {v : E} (hv : v ≠ 0) :
    ∃ m ∈ subdifferential continuousDualPairing f x,
      m v = realDirectionalDerivative f x v := by
  obtain ⟨L, hL, hval⟩ := exists_linearMap_le_sublinear_eq_of_ne_zero
    (realDirectionalDerivative f x) (realDirectionalDerivative_zero f x)
    (realDirectionalDerivative_pos_smul hf hx) (realDirectionalDerivative_add_le hf hx) hv
  let m : StrongDual ℝ E := L.toContinuousLinearMap
  have hxD := interior_subset hx
  refine ⟨m, ⟨hxD, ?_⟩, hval⟩
  intro y
  by_cases hy : y ∈ effectiveDomain f
  · have hd : realDirectionalDerivative f x (y - x) ≤
        (f y).toReal - (f x).toReal := by
      simpa using realDirectionalDerivative_le_difference hf hx
        (v := y - x) (by simpa using hy)
    have hbound : L (y - x) ≤ (f y).toReal - (f x).toReal := (hL (y - x)).trans hd
    have hfx : f x = ((f x).toReal : EReal) :=
      (EReal.coe_toReal (ne_of_lt hxD) (hf.2.2 x)).symm
    have hfy : f y = ((f y).toReal : EReal) :=
      (EReal.coe_toReal (ne_of_lt hy) (hf.2.2 y)).symm
    change f x + (L (y - x) : EReal) ≤ f y
    rw [hfx, hfy, ← EReal.coe_add, EReal.coe_le_coe_iff]
    linarith
  · change ¬ f y < ⊤ at hy
    rw [top_unique (le_of_not_gt hy)]
    exact le_top

theorem exists_subgradient_attaining_realDirectionalDerivative
    {f : E → EReal} (hf : IsProper f) {x : E}
    (hx : x ∈ interior (effectiveDomain f)) (v : E) :
    ∃ m ∈ subdifferential continuousDualPairing f x,
      m v = realDirectionalDerivative f x v := by
  by_cases hv : v = 0
  · obtain ⟨m, hm⟩ := subdifferential_nonempty_of_mem_intrinsicInterior
      continuousDualPairing hf (interior_subset_intrinsicInterior hx)
    refine ⟨m, hm, ?_⟩
    simp [hv, realDirectionalDerivative_zero]
  · exact exists_subgradient_attaining_realDirectionalDerivative_of_ne_zero hf hx hv

omit [FiniteDimensional ℝ E] in
theorem subgradient_apply_le_realDirectionalDerivative
    {f : E → EReal} (hf : IsProper f) {x : E}
    (hx : x ∈ interior (effectiveDomain f)) {m : StrongDual ℝ E}
    (hm : m ∈ subdifferential continuousDualPairing f x) (v : E) :
    m v ≤ realDirectionalDerivative f x v := by
  apply ge_of_tendsto (tendsto_real_directional_secant hf hx v)
  have hd₀ : ∀ᶠ t in 𝓝 (0 : ℝ), t ∈ lineDomain f x v :=
    mem_interior_iff_mem_nhds.mp (zero_mem_interior_lineDomain hx v)
  have hd : ∀ᶠ t in 𝓝[>] (0 : ℝ), t ∈ lineDomain f x v :=
    hd₀.filter_mono nhdsWithin_le_nhds
  filter_upwards [hd, self_mem_nhdsWithin] with t htd ht
  change (0 : ℝ) < t at ht
  have h := subgradient_le_toReal_difference hf hm htd
  simp only [add_sub_cancel_left, map_smul, smul_eq_mul] at h
  exact (le_div_iff₀ ht).mpr (by simpa only [mul_comm] using h)

omit [FiniteDimensional ℝ E] in
/-- The actual extended-real right secant; its value is independent of the
arbitrary real projection used to define the finite derivative. -/
noncomputable def directionalSecant (f : E → EReal) (x v : E) (t : ℝ) : EReal :=
  (t : EReal)⁻¹ * (f (x + t • v) - f x)

omit [FiniteDimensional ℝ E] in
/-- Genuine relative interior supplies a line-domain neighborhood in each
actual direction of the domain affine span. -/
theorem zero_mem_interior_lineDomain_of_mem_intrinsicInterior {f : E → EReal}
    {x v : E} (hx : x ∈ intrinsicInterior ℝ (effectiveDomain f))
    (hv : v ∈ (affineSpan ℝ (effectiveDomain f)).direction) :
    (0 : ℝ) ∈ interior (lineDomain f x v) := by
  let A := affineSpan ℝ (effectiveDomain f)
  have hxA : x ∈ A := subset_affineSpan ℝ _ (intrinsicInterior_subset hx)
  let xA : A := ⟨x, hxA⟩
  let F : ℝ → A := fun t ↦ ⟨x + t • v, by
    simpa only [vadd_eq_add, add_comm] using
      A.vadd_mem_of_mem_direction (A.direction.smul_mem t hv) hxA⟩
  have hF : Continuous F :=
    (continuous_const.add (continuous_id.smul continuous_const)).subtype_mk _
  have hF₀ : F 0 = xA := Subtype.ext (by simp [F, xA])
  have hxint : xA ∈ interior ((↑) ⁻¹' effectiveDomain f : Set A) := by
    obtain ⟨y, hy, heq⟩ := mem_intrinsicInterior.mp hx
    have hyx : y = xA := Subtype.ext heq
    simpa only [hyx] using hy
  have hD : ((↑) ⁻¹' effectiveDomain f : Set A) ∈ 𝓝 (F 0) :=
    hF₀ ▸ mem_interior_iff_mem_nhds.mp hxint
  exact mem_interior_iff_mem_nhds.mpr (hF.continuousAt.preimage_mem_nhds hD)

omit [FiniteDimensional ℝ E] in
theorem hasDerivWithinAt_lineProfile_of_mem_intrinsicInterior {f : E → EReal}
    (hf : IsProper f) {x v : E} (hx : x ∈ intrinsicInterior ℝ (effectiveDomain f))
    (hv : v ∈ (affineSpan ℝ (effectiveDomain f)).direction) :
    HasDerivWithinAt (lineProfile f x v) (realDirectionalDerivative f x v) (Ioi 0) 0 :=
  (convexOn_lineProfile hf x v).hasDerivWithinAt_rightDeriv_of_mem_interior
    (zero_mem_interior_lineDomain_of_mem_intrinsicInterior hx hv)

omit [FiniteDimensional ℝ E] in
theorem tendsto_real_directional_secant_of_mem_intrinsicInterior {f : E → EReal}
    (hf : IsProper f) {x v : E} (hx : x ∈ intrinsicInterior ℝ (effectiveDomain f))
    (hv : v ∈ (affineSpan ℝ (effectiveDomain f)).direction) :
    Tendsto (fun t : ℝ ↦ ((f (x + t • v)).toReal - (f x).toReal) / t)
      (𝓝[>] 0) (𝓝 (realDirectionalDerivative f x v)) := by
  have h := (hasDerivWithinAt_iff_tendsto_slope' (by simp : (0 : ℝ) ∉ Ioi 0)).mp
    (hasDerivWithinAt_lineProfile_of_mem_intrinsicInterior hf hx hv)
  convert h using 1
  funext t
  simp [slope, lineProfile, div_eq_mul_inv, smul_eq_mul, mul_comm]

omit [FiniteDimensional ℝ E] in
theorem tendsto_directionalSecant_of_mem_intrinsicInterior {f : E → EReal}
    (hf : IsProper f) {x v : E} (hx : x ∈ intrinsicInterior ℝ (effectiveDomain f))
    (hv : v ∈ (affineSpan ℝ (effectiveDomain f)).direction) :
    Tendsto (directionalSecant f x v) (𝓝[>] 0)
      (𝓝 (realDirectionalDerivative f x v : EReal)) := by
  have hreal := tendsto_real_directional_secant_of_mem_intrinsicInterior hf hx hv
  have h := continuous_coe_real_ereal.continuousAt.tendsto.comp hreal
  apply h.congr'
  have hd₀ : ∀ᶠ t in 𝓝 (0 : ℝ), t ∈ lineDomain f x v :=
    mem_interior_iff_mem_nhds.mp (zero_mem_interior_lineDomain_of_mem_intrinsicInterior hx hv)
  have hd : ∀ᶠ t in 𝓝[>] (0 : ℝ), t ∈ lineDomain f x v :=
    hd₀.filter_mono nhdsWithin_le_nhds
  have hxD : x ∈ effectiveDomain f := intrinsicInterior_subset hx
  filter_upwards [hd] with t ht
  have hfx : f x = ((f x).toReal : EReal) :=
    (EReal.coe_toReal (ne_of_lt hxD) (hf.2.2 x)).symm
  have hft : f (x + t • v) = ((f (x + t • v)).toReal : EReal) :=
    (EReal.coe_toReal (ne_of_lt ht) (hf.2.2 _)).symm
  have heq : directionalSecant f x v t =
      (((f (x + t • v)).toReal - (f x).toReal) / t : ℝ) := by
    rw [directionalSecant, hft, hfx, ← EReal.coe_sub, ← EReal.coe_inv, ← EReal.coe_mul]
    congr 1
    simp only [EReal.toReal_coe, div_eq_mul_inv, mul_comm]
  exact heq.symm

/-- Restriction to the genuine affine-span direction and genuine Hahn--Banach
extension construct an actual derivative-attaining subgradient at every source
relative-interior point, including lower-dimensional domains. -/
theorem exists_subgradient_attaining_realDirectionalDerivative_of_mem_intrinsicInterior
    {f : E → EReal} (hf : IsProper f) {x v : E}
    (hx : x ∈ intrinsicInterior ℝ (effectiveDomain f))
    (hv : v ∈ (affineSpan ℝ (effectiveDomain f)).direction) :
    ∃ m ∈ subdifferential continuousDualPairing f x,
      m v = realDirectionalDerivative f x v := by
  let A := affineSpan ℝ (effectiveDomain f)
  have hxD : x ∈ effectiveDomain f := intrinsicInterior_subset hx
  let xA : A := ⟨x, subset_affineSpan ℝ _ hxD⟩
  let : Nonempty A := ⟨xA⟩
  let e := AffineIsometryEquiv.vaddConst ℝ xA
  let F := A.subtype.comp e.toAffineEquiv.toAffineMap
  let g : A.direction → EReal := f ∘ F
  have hF (w : A.direction) : (F w : E) = x + (w : E) := by
    simp [F, e, xA, AffineSubspace.coe_vadd, vadd_eq_add, add_comm]
  have hF₀ : F 0 = x := by simp only [hF, Submodule.coe_zero, add_zero]
  have hg : IsProper g := by
    refine ⟨isConvex_comp_affineMap hf.1 F, ⟨?_, ?_⟩⟩
    · refine ⟨0, ?_⟩
      change f (F 0) < ⊤
      rw [hF₀]
      exact hxD
    · exact fun w ↦ hf.2.2 (F w)
  have hxint : xA ∈ interior ((↑) ⁻¹' effectiveDomain f : Set A) := by
    obtain ⟨y, hy, heq⟩ := mem_intrinsicInterior.mp hx
    have hyx : y = xA := Subtype.ext heq
    simpa only [hyx] using hy
  have hzero : (0 : A.direction) ∈ interior (effectiveDomain g) := by
    change (0 : A.direction) ∈ interior
      (e.toHomeomorph ⁻¹' ((↑) ⁻¹' effectiveDomain f : Set A))
    rw [← e.toHomeomorph.preimage_interior]
    change e 0 ∈ interior ((↑) ⁻¹' effectiveDomain f : Set A)
    simpa [e] using hxint
  have hprofile (w : A.direction) : lineProfile g 0 w = lineProfile f x (w : E) := by
    funext t
    simp only [lineProfile, g, Function.comp_apply, zero_add, hF, Submodule.coe_smul]
  have hderiv (w : A.direction) :
      realDirectionalDerivative g 0 w = realDirectionalDerivative f x (w : E) := by
    exact congrArg (fun p : ℝ → ℝ ↦ derivWithin p (Ioi 0) 0) (hprofile w)
  let vD : A.direction := ⟨v, hv⟩
  obtain ⟨mD, hmD, hval⟩ := exists_subgradient_attaining_realDirectionalDerivative hg hzero vD
  obtain ⟨m, hm, _⟩ := exists_extension_norm_eq A.direction mD
  refine ⟨m, ⟨hxD, ?_⟩, ?_⟩
  · intro y
    by_cases hy : y ∈ effectiveDomain f
    · let yD : A.direction := ⟨y - x,
        A.vsub_mem_direction (subset_affineSpan ℝ _ hy) xA.property⟩
      have hFy : F yD = y := by simpa [yD] using hF yD
      have hbound := hmD.2 yD
      change g 0 + (mD (yD - 0) : EReal) ≤ g yD at hbound
      rw [sub_zero] at hbound
      change f x + (m (y - x) : EReal) ≤ f y
      rw [show m (y - x) = mD yD from hm yD]
      simpa only [g, Function.comp_apply, hF₀, hFy] using hbound
    · change ¬ f y < ⊤ at hy
      rw [top_unique (le_of_not_gt hy)]
      exact le_top
  · exact (hm vD).trans (hval.trans (hderiv vD))

omit [FiniteDimensional ℝ E] in
/-- Every actual subgradient is bounded by the actual finite right derivative
in each genuine direction of the domain affine span. -/
theorem subgradient_apply_le_realDirectionalDerivative_of_mem_intrinsicInterior
    {f : E → EReal} (hf : IsProper f) {x v : E}
    (hx : x ∈ intrinsicInterior ℝ (effectiveDomain f))
    (hv : v ∈ (affineSpan ℝ (effectiveDomain f)).direction)
    {m : StrongDual ℝ E} (hm : m ∈ subdifferential continuousDualPairing f x) :
    m v ≤ realDirectionalDerivative f x v := by
  apply ge_of_tendsto (tendsto_real_directional_secant_of_mem_intrinsicInterior hf hx hv)
  have hd₀ : ∀ᶠ t in 𝓝 (0 : ℝ), t ∈ lineDomain f x v :=
    mem_interior_iff_mem_nhds.mp
      (zero_mem_interior_lineDomain_of_mem_intrinsicInterior hx hv)
  have hd : ∀ᶠ t in 𝓝[>] (0 : ℝ), t ∈ lineDomain f x v :=
    hd₀.filter_mono nhdsWithin_le_nhds
  filter_upwards [hd, self_mem_nhdsWithin] with t htd ht
  change (0 : ℝ) < t at ht
  have h := subgradient_le_toReal_difference hf hm htd
  simp only [add_sub_cancel_left, map_smul, smul_eq_mul] at h
  exact (le_div_iff₀ ht).mpr (by simpa only [mul_comm] using h)

omit [FiniteDimensional ℝ E] in
/-- Outside the actual affine-span direction, every actual positive ray point
lies outside the effective domain. -/
theorem not_mem_effectiveDomain_add_pos_smul_of_not_mem_direction
    {f : E → EReal} {x v : E} (hx : x ∈ effectiveDomain f)
    (hv : v ∉ (affineSpan ℝ (effectiveDomain f)).direction)
    {t : ℝ} (ht : 0 < t) : x + t • v ∉ effectiveDomain f := by
  intro hy
  let A := affineSpan ℝ (effectiveDomain f)
  have hd : t • v ∈ A.direction := by
    simpa only [vsub_eq_sub, add_sub_cancel_left] using
      A.vsub_mem_direction (subset_affineSpan ℝ _ hy) (subset_affineSpan ℝ _ hx)
  have h := A.direction.smul_mem t⁻¹ hd
  have htv : t⁻¹ • (t • v) = v := by
    rw [smul_smul, inv_mul_cancel₀ ht.ne', one_smul]
  exact hv (htv ▸ h)

omit [FiniteDimensional ℝ E] in
/-- The actual extended-real positive secants are top outside the true span. -/
theorem directionalSecant_eq_top_of_not_mem_direction {f : E → EReal}
    (hf : IsProper f) {x v : E} (hx : x ∈ effectiveDomain f)
    (hv : v ∉ (affineSpan ℝ (effectiveDomain f)).direction)
    {t : ℝ} (ht : 0 < t) : directionalSecant f x v t = ⊤ := by
  have hnot := not_mem_effectiveDomain_add_pos_smul_of_not_mem_direction hx hv ht
  have htop : f (x + t • v) = ⊤ := top_unique (le_of_not_gt hnot)
  have hfx : f x = ((f x).toReal : EReal) :=
    (EReal.coe_toReal (ne_of_lt hx) (hf.2.2 x)).symm
  rw [directionalSecant, htop, hfx, EReal.top_sub_coe, ← EReal.coe_inv]
  exact EReal.coe_mul_top_of_pos (inv_pos.mpr ht)

/-- A genuine continuous annihilator has prescribed value one at every actual
point outside a finite-dimensional subspace. -/
theorem exists_continuous_annihilator_apply_eq_one (V : Submodule ℝ E)
    {v : E} (hv : v ∉ V) :
    ∃ L : StrongDual ℝ E, L v = 1 ∧ ∀ w ∈ V, L w = 0 := by
  obtain ⟨ℓ, hℓ, hker⟩ := V.exists_le_ker_of_notMem hv
  let L : StrongDual ℝ E := (ℓ v)⁻¹ • ℓ.toContinuousLinearMap
  refine ⟨L, ?_, ?_⟩
  · change (ℓ v)⁻¹ * ℓ v = 1
    exact inv_mul_cancel₀ hℓ
  · intro w hw
    have hzero : ℓ w = 0 := hker hw
    change (ℓ v)⁻¹ * ℓ w = 0
    rw [hzero, mul_zero]

/-- Actual annihilator rays make the true subgradient support top in every
direction outside the domain affine span. -/
theorem support_subdifferential_eq_top_of_not_mem_direction {f : E → EReal}
    (hf : IsProper f) {x v : E} (hx : x ∈ intrinsicInterior ℝ (effectiveDomain f))
    (hv : v ∉ (affineSpan ℝ (effectiveDomain f)).direction) :
    support continuousDualPairing.flip (subdifferential continuousDualPairing f x) v = ⊤ := by
  obtain ⟨m, hm⟩ := subdifferential_nonempty_of_mem_intrinsicInterior continuousDualPairing hf hx
  let A := affineSpan ℝ (effectiveDomain f)
  obtain ⟨L, hLv, hL⟩ := exists_continuous_annihilator_apply_eq_one A.direction hv
  have hsupport : ∀ y ∈ effectiveDomain f, L y ≤ L x := by
    intro y hy
    have hd : y - x ∈ A.direction :=
      A.vsub_mem_direction (subset_affineSpan ℝ _ hy) (subset_affineSpan ℝ _ hm.1)
    have h := hL (y - x) hd
    rw [map_sub, sub_eq_zero] at h
    exact h.le
  apply (EReal.eq_top_iff_forall_lt _).mpr
  intro r
  let t : ℝ := max 0 (r - m v) + 1
  have ht : 0 ≤ t := by
    dsimp only [t]
    linarith [le_max_left (0 : ℝ) (r - m v)]
  have hm' := add_normal_mem_subdifferential hm hsupport ht
  have hvalue : (m + t • L) v = m v + t := by
    rw [add_apply, smul_apply, hLv]
    simp only [smul_eq_mul, mul_one]
  have hr : r < (m + t • L) v := by
    rw [hvalue]
    dsimp only [t]
    linarith [le_max_right (0 : ℝ) (r - m v)]
  have hbound : ((m + t • L) v : EReal) ≤
      support continuousDualPairing.flip (subdifferential continuousDualPairing f x) v := by
    apply le_iSup_of_le ⟨m + t • L, hm'⟩
    exact le_rfl
  exact (EReal.coe_lt_coe_iff.mpr hr).trans_le hbound

/-- The true finite derivative is exactly the actual subgradient support in
each genuine affine-span direction. -/
theorem support_subdifferential_eq_realDirectionalDerivative_of_mem_direction
    {f : E → EReal} (hf : IsProper f) {x v : E}
    (hx : x ∈ intrinsicInterior ℝ (effectiveDomain f))
    (hv : v ∈ (affineSpan ℝ (effectiveDomain f)).direction) :
    support continuousDualPairing.flip (subdifferential continuousDualPairing f x) v =
      (realDirectionalDerivative f x v : EReal) := by
  apply le_antisymm
  · apply iSup_le
    intro m
    exact EReal.coe_le_coe_iff.mpr
      (subgradient_apply_le_realDirectionalDerivative_of_mem_intrinsicInterior hf hx hv m.property)
  · obtain ⟨m, hm, hval⟩ :=
      exists_subgradient_attaining_realDirectionalDerivative_of_mem_intrinsicInterior hf hx hv
    rw [← hval]
    apply le_iSup_of_le ⟨m, hm⟩
    exact le_rfl

omit [FiniteDimensional ℝ E] in
/-- The actual extended-real right directional derivative: the genuine right
derivative of the scalar profile on span directions, and top outside that span.
The secant convergence theorem verifies this independently of subgradients. -/
noncomputable def directionalDerivative (f : E → EReal) (x v : E) : EReal := by
  classical
  exact if v ∈ (affineSpan ℝ (effectiveDomain f)).direction then
    (realDirectionalDerivative f x v : EReal) else ⊤

omit [FiniteDimensional ℝ E] in
/-- The independently defined directional derivative is the actual right limit
of the original extended-real directional secants. -/
theorem tendsto_directionalSecant {f : E → EReal} (hf : IsProper f) {x : E}
    (hx : x ∈ intrinsicInterior ℝ (effectiveDomain f)) (v : E) :
    Tendsto (directionalSecant f x v) (𝓝[>] 0) (𝓝 (directionalDerivative f x v)) := by
  by_cases hv : v ∈ (affineSpan ℝ (effectiveDomain f)).direction
  · rw [directionalDerivative, if_pos hv]
    exact tendsto_directionalSecant_of_mem_intrinsicInterior hf hx hv
  · rw [directionalDerivative, if_neg hv]
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact (directionalSecant_eq_top_of_not_mem_direction hf (intrinsicInterior_subset hx)
      hv ht).symm

/-- The actual derivative is the support of the genuine canonical-dual
subdifferential, including the outside-span infinite directions. -/
theorem directionalDerivative_eq_support_subdifferential {f : E → EReal}
    (hf : IsProper f) {x : E} (hx : x ∈ intrinsicInterior ℝ (effectiveDomain f))
    (v : E) : directionalDerivative f x v =
      support continuousDualPairing.flip (subdifferential continuousDualPairing f x) v := by
  by_cases hv : v ∈ (affineSpan ℝ (effectiveDomain f)).direction
  · rw [directionalDerivative, if_pos hv]
    exact (support_subdifferential_eq_realDirectionalDerivative_of_mem_direction hf hx hv).symm
  · rw [directionalDerivative, if_neg hv,
      support_subdifferential_eq_top_of_not_mem_direction hf hx hv]

/-- Canonical-dual source directional derivative formula with the exact raw
displayed source subdifferential. -/
theorem directionalDerivative_eq_support_rawSubdifferential {f : E → EReal}
    (hf : IsProper f) {x : E} (hx : x ∈ intrinsicInterior ℝ (effectiveDomain f))
    (v : E) : directionalDerivative f x v =
      support continuousDualPairing.flip (rawSubdifferential continuousDualPairing f x) v := by
  rw [rawSubdifferential_eq_subdifferential_of_isProper continuousDualPairing hf]
  exact directionalDerivative_eq_support_subdifferential hf hx v

/-- Exact source `thm:nablaF` directional-derivative clause for the original
arbitrary continuous perfect pairing and actual raw source subdifferential. -/
theorem directionalDerivative_eq_support_rawSubdifferential_of_isContPerfPair
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) [B.IsContPerfPair] {f : E → EReal}
    (hf : IsProper f) {x : E} (hx : x ∈ intrinsicInterior ℝ (effectiveDomain f))
    (v : E) : directionalDerivative f x v = support B.flip (rawSubdifferential B f x) v := by
  rw [directionalDerivative_eq_support_rawSubdifferential hf hx v]
  let e : F ≃ₗ[ℝ] StrongDual ℝ E := B.flip.toContPerfPair
  have himage : e '' rawSubdifferential B f x = rawSubdifferential continuousDualPairing f x :=
    rawSubdifferential_image_toContPerfPair B f x
  apply le_antisymm
  · apply iSup_le
    intro m
    have hm : m.val ∈ e '' rawSubdifferential B f x := by
      rw [himage]
      exact m.property
    obtain ⟨q, hq, heq⟩ := hm
    apply le_iSup_of_le ⟨q, hq⟩
    change (m.val v : EReal) ≤ (B v q : EReal)
    rw [← heq]
    exact le_rfl
  · apply iSup_le
    intro q
    have hm : e q.val ∈ rawSubdifferential continuousDualPairing f x := by
      rw [← himage]
      exact mem_image_of_mem e q.property
    apply le_iSup_of_le ⟨e q.val, hm⟩
    exact le_rfl

end SGPT.Convex
