import SGPT.Convex.AffineLegendreTangent

set_option autoImplicit false
noncomputable section
namespace SGPT.Convex
open Set Filter MeasureTheory SGPT.PSH
open scoped Topology NNReal ENNReal RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
local notation "B" => innerₗ E

private theorem hasDerivWithinAt_of_endpoint_sandwich (C I : ℝ → ℝ) (hI : Continuous I)
    (hvar : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      (t - s) * I t ≤ C t - C s ∧ C t - C s ≤ (t - s) * I s)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    HasDerivWithinAt C (I s) (Icc (0 : ℝ) 1) s := by
  apply hasDerivWithinAt_iff_tendsto_slope.mpr
  have hlim : Tendsto I (𝓝[Icc (0 : ℝ) 1 \ {s}] s) (𝓝 (I s)) :=
    hI.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hlo : Tendsto (fun t => min (I s) (I t))
      (𝓝[Icc (0 : ℝ) 1 \ {s}] s) (𝓝 (I s)) := by
    simpa using (tendsto_const_nhds (x := I s)).min hlim
  have hhi : Tendsto (fun t => max (I s) (I t))
      (𝓝[Icc (0 : ℝ) 1 \ {s}] s) (𝓝 (I s)) := by
    simpa using (tendsto_const_nhds (x := I s)).max hlim
  have hb : ∀ᶠ t in 𝓝[Icc (0 : ℝ) 1 \ {s}] s,
      min (I s) (I t) ≤ slope C s t ∧ slope C s t ≤ max (I s) (I t) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    have htne : t ≠ s := by simpa using ht.2
    have hv := hvar s hs t ht.1
    rw [slope_def_field]
    rcases lt_or_gt_of_ne htne with hlt | hgt
    · have hneg : t - s < 0 := sub_neg.mpr hlt
      have h1 : I s ≤ (C t - C s) / (t - s) :=
        (le_div_iff_of_neg hneg).mpr (by simpa only [mul_comm] using hv.2)
      have h2 : (C t - C s) / (t - s) ≤ I t :=
        (div_le_iff_of_neg hneg).mpr (by simpa only [mul_comm] using hv.1)
      exact ⟨(min_le_left _ _).trans h1, h2.trans (le_max_right _ _)⟩
    · have hpos : 0 < t - s := sub_pos.mpr hgt
      have h1 : I t ≤ (C t - C s) / (t - s) :=
        (le_div_iff₀ hpos).mpr (by simpa only [mul_comm] using hv.1)
      have h2 : (C t - C s) / (t - s) ≤ I s :=
        (div_le_iff₀ hpos).mpr (by simpa only [mul_comm] using hv.2)
      exact ⟨(min_le_right _ _).trans h1, h2.trans (le_max_left _ _)⟩
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi (hb.mono fun _ h => h.1)
    (hb.mono fun _ h => h.2)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem convexOn_affineProfile (f g : RealConvexFunction E) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) : ConvexOn ℝ univ (affineProfile f g t) :=
  (ConvexOn.smul (sub_nonneg.mpr ht.2) f.property).add
    (ConvexOn.smul ht.1 g.property)

/-- The actual general-rank affine conjugate integral has its true tangent
within derivative, produced from actual endpoint measures and bounded growth. -/
theorem hasDerivWithinAt_affineLegendreEnergy (μ : Measure E) [μ.IsAddHaarMeasure]
    {n : ℕ} (b : OrthonormalBasis (Fin n) ℝ E) {P : Set E}
    (hP : IsCompact P) (hne : P.Nonempty) (hconv : Convex ℝ P)
    {f g : RealConvexFunction E}
    (hf : (fun x => (f.val x : EReal)) ∈ BoundedGrowthClass B P)
    (hg : (fun x => (g.val x : EReal)) ∈ BoundedGrowthClass B P)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    HasDerivWithinAt (fun s => (n.factorial : ℝ) * ∫ m in P,
        ((conjugate B (fun x => (f.val x : EReal)) m).toReal -
          (conjugate B (fun x => (affineProfile f g s x : EReal)) m).toReal) ∂μ)
      (affineTangentPolynomial μ b f g t) (Icc (0 : ℝ) 1) t := by
  let C : ℝ → ℝ := fun s => (n.factorial : ℝ) * ∫ m in P,
    ((conjugate B (fun x => (f.val x : EReal)) m).toReal -
      (conjugate B (fun x => (affineProfile f g s x : EReal)) m).toReal) ∂μ
  have hfin : Module.finrank ℝ E = n := by
    simpa using Module.finrank_eq_card_basis b.toBasis
  have hif := integrable_conjugateToReal_of_mem_boundedGrowthClass μ hP hne hconv hf
  have hi (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
      Integrable (fun m =>
        (conjugate B (fun x => (affineProfile f g s x : EReal)) m).toReal) (μ.restrict P) :=
    integrable_conjugateToReal_of_mem_boundedGrowthClass μ hP hne hconv
      (f := ⟨affineProfile f g s, convexOn_affineProfile f g hs⟩)
      (boundedGrowthClass_affineProfile hf hg hs)
  have hvar (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1)
      (r : ℝ) (hr : r ∈ Icc (0 : ℝ) 1) :
      (r - s) * affineTangentPolynomial μ b f g r ≤ C r - C s ∧
        C r - C s ≤ (r - s) * affineTangentPolynomial μ b f g s := by
    have hv := integral_conjugate_variation_bounds μ hP hne hconv
      (f := ⟨affineProfile f g s, convexOn_affineProfile f g hs⟩)
      (g := ⟨affineProfile f g r, convexOn_affineProfile f g hr⟩)
      (boundedGrowthClass_affineProfile hf hg hs) (boundedGrowthClass_affineProfile hf hg hr)
    have hgap : (fun x => affineProfile f g r x - affineProfile f g s x) =
        (fun x => (r - s) * (g.val x - f.val x)) := by
      funext x
      dsimp only [affineProfile]
      ring
    have hdiff : (n.factorial : ℝ) * (∫ m in P,
        ((conjugate B (fun x => (affineProfile f g s x : EReal)) m).toReal -
          (conjugate B (fun x => (affineProfile f g r x : EReal)) m).toReal) ∂μ) = C r - C s := by
      rw [integral_sub (hi s hs) (hi r hr)]
      dsimp only [C]
      rw [integral_sub hif (hi r hr), integral_sub hif (hi s hs)]
      ring
    dsimp only at hv
    rw [hfin, hgap, integral_const_mul, integral_const_mul,
      integral_gap_affineProfile_eq_tangentPolynomial μ b hP hne hconv hf hg hr,
      integral_gap_affineProfile_eq_tangentPolynomial μ b hP hne hconv hf hg hs, hdiff] at hv
    exact hv
  exact hasDerivWithinAt_of_endpoint_sandwich C (affineTangentPolynomial μ b f g)
    (continuous_affineTangentPolynomial μ b f g) hvar ht

/-- Genuine FTC consumes the manufactured tangent derivative and identifies
bounded Legendre energy in arbitrary real rank with the actual affine path. -/
theorem integral_conjugate_difference_eq_affinePathEnergy (μ : Measure E) [μ.IsAddHaarMeasure]
    {n : ℕ} (b : OrthonormalBasis (Fin n) ℝ E) {P : Set E}
    (hP : IsCompact P) (hne : P.Nonempty) (hconv : Convex ℝ P)
    {f g : RealConvexFunction E}
    (hf : (fun x => (f.val x : EReal)) ∈ BoundedGrowthClass B P)
    (hg : (fun x => (g.val x : EReal)) ∈ BoundedGrowthClass B P) :
    (n.factorial : ℝ) * (∫ m in P,
        ((conjugate B (fun x => (f.val x : EReal)) m).toReal -
          (conjugate B (fun x => (g.val x : EReal)) m).toReal) ∂μ) =
      ∫ t in (0 : ℝ)..1, affineTangentPolynomial μ b f g t := by
  let C : ℝ → ℝ := fun s => (n.factorial : ℝ) * ∫ m in P,
    ((conjugate B (fun x => (f.val x : EReal)) m).toReal -
      (conjugate B (fun x => (affineProfile f g s x : EReal)) m).toReal) ∂μ
  have he := intervalIntegral.integral_deriv_mul_eq_sub_of_hasDerivWithinAt
    (a := (0 : ℝ)) (b := (1 : ℝ))
    (u := C) (u' := affineTangentPolynomial μ b f g)
    (v := fun _ : ℝ => (1 : ℝ)) (v' := fun _ : ℝ => (0 : ℝ))
    (fun t ht => by
      have h := hasDerivWithinAt_affineLegendreEnergy μ b hP hne hconv hf hg
        (by simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using ht)
      simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using h)
    (fun t _ => hasDerivWithinAt_const t (uIcc (0 : ℝ) 1) (1 : ℝ))
    ((continuous_affineTangentPolynomial μ b f g).intervalIntegrable 0 1)
    (continuous_const.intervalIntegrable 0 1)
  simp only [mul_one, mul_zero, add_zero] at he
  dsimp only [C, affineProfile] at he
  simp only [sub_zero, one_mul, zero_mul, add_zero, sub_self, zero_add,
    integral_zero, mul_zero] at he
  exact he.symm
end SGPT.Convex
