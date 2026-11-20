import SGPT.PSH.NativeLogSingularities
import SGPT.PSH.CanonicalCartierFaithfulness
import SGPT.PSH.LocalRationalDenominatorMultiple
import SGPT.PSH.NativeCartierGeneratorUnits

set_option autoImplicit false
noncomputable section
namespace SGPT.PSH
open Set Filter TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending HironakaEffectiveDivisorSum
open scoped Topology Manifold ContDiff Classical

variable {m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]

private theorem finite_prime_coefficient_cast {r : ℕ}
    (W : Fin r → GeometricPrimeCarrier (m + 1) M) (a : Fin r → ℕ)
    (P : GeometricPrimeCarrier (m + 1) M) :
    (cartierGeometricPrimeCoefficient (∑ i, a i • geometricPrimeCarrierEffectiveDivisor (W i)) P : ℚ) =
      ∑ i, if W i = P then (a i : ℚ) else 0 := by
  classical
  have h := cartierGeometricPrimeCoefficient_finset_sum Finset.univ
    (fun i => geometricPrimeCarrierEffectiveDivisor (W i)) a P
  rw [h, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Nat.cast_mul, cartierGeometricPrimeCoefficient_reduced]
  by_cases hi : W i = P
  · simp only [if_pos hi, if_pos hi.symm, Nat.cast_one, mul_one]
  · simp only [if_neg hi, if_neg (Ne.symm hi), Nat.cast_zero, mul_zero]

private theorem scaled_cartier_stalk_comparison {r : ℕ}
    (D : EffectiveGeometricQDivisor (m + 1) M) (F : EffectiveDivisor (m + 1) M)
    (V : Set M) (d k : ℕ) (hd : 0 < d) (hk : 0 < k) (U : Opens M)
    (W : Fin r → GeometricPrimeCarrier (m + 1) U) (w : Fin r → ℚ) (a : Fin r → ℕ)
    (ha : ∀ i, w i = (a i : ℚ) / ((d * k : ℕ) : ℚ))
    (hsource : ∀ P, (geometricQDivisorOpenRestriction D U).coefficient P =
      ∑ i, if W i = P then w i else 0)
    (hreader : ∀ P : GeometricPrimeCarrier (m + 1) U,
      (P.val ∩ (Subtype.val : U → M) ⁻¹' V).Nonempty →
      (geometricQDivisorOpenRestriction D U).coefficient P =
        (cartierGeometricPrimeCoefficient (cartierOpenRestriction F U) P : ℚ) / (d : ℚ)) :
    ∀ y : U, (y : M) ∈ V → ∀ b,
      (cartierOpenRestriction (k • F) U).ideal.mem y b ↔
        (∑ i, a i • geometricPrimeCarrierEffectiveDivisor (W i)).ideal.mem y b := by
  classical
  let E := ∑ i, a i • geometricPrimeCarrierEffectiveDivisor (W i)
  let K := cartierOpenRestriction (k • F) U
  have hcoeff (P : GeometricPrimeCarrier (m + 1) U)
      (hP : (P.val ∩ (Subtype.val : U → M) ⁻¹' V).Nonempty) :
      cartierGeometricPrimeCoefficient E P = cartierGeometricPrimeCoefficient K P := by
    have hE : (cartierGeometricPrimeCoefficient E P : ℚ) / ((d * k : ℕ) : ℚ) =
        (geometricQDivisorOpenRestriction D U).coefficient P := by
      rw [finite_prime_coefficient_cast, Finset.sum_div, hsource]
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : W i = P
      · simp only [if_pos hi, ← ha i]
      · simp only [if_neg hi, zero_div]
    rw [hreader P hP] at hE
    have hdQ : (d : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
    have hdkQ : ((d * k : ℕ) : ℚ) ≠ 0 := by exact_mod_cast Nat.mul_ne_zero hd.ne' hk.ne'
    have hcross := (div_eq_div_iff hdkQ hdQ).mp hE
    have hnat : cartierGeometricPrimeCoefficient E P =
        k * cartierGeometricPrimeCoefficient (cartierOpenRestriction F U) P := by
      apply Nat.cast_injective (R := ℚ)
      rw [Nat.cast_mul]
      apply mul_right_cancel₀ hdQ
      calc
        (cartierGeometricPrimeCoefficient E P : ℚ) * (d : ℚ) =
            (cartierGeometricPrimeCoefficient (cartierOpenRestriction F U) P : ℚ) *
              ((d * k : ℕ) : ℚ) := hcross
        _ = _ := by push_cast; ring
    have hKU : K = k • cartierOpenRestriction F U :=
      (map_nsmul (cartierOpenRestrictionHom U) k F)
    rw [hKU, cartierGeometricPrimeCoefficient_nsmul]
    exact hnat
  intro y hy b
  exact ⟨cartierIdeal_le_on_of_geometricPrimeCoefficient_le E K
      ((Subtype.val : U → M) ⁻¹' V) (fun P hP => (hcoeff P hP).le) y hy b,
    cartierIdeal_le_on_of_geometricPrimeCoefficient_le K E
      ((Subtype.val : U → M) ⁻¹' V) (fun P hP => (hcoeff P hP).symm.le) y hy b⟩

private theorem nsmul_generator_power {n : ℕ} {X : Type*} [TopologicalSpace X]
    [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
    (F : EffectiveDivisor n X) (x : X) (g : X → ℂ) (hg : HolomorphicAt n g x)
    (hgen : ∀ b, F.ideal.mem x b ↔ IsInSpanAt (n := n) (· = g) x b) (k : ℕ) (b : X → ℂ) :
    (k • F).ideal.mem x b ↔ IsInSpanAt (n := n) (· = fun y => g y ^ k) x b := by
  rw [ideal_nsmul]
  exact HironakaSNCComponentCoefficients.idealPow_mem_iff_of_generator hg hgen k b

/-- ORIGINAL D,u,x ALONE retain the SAME internally chosen local integral
Cartier divisor and produce its actual nearby full ideal generator together
with the genuine bounded remainder for u=(1/d)log|g|². -/
theorem NativeHasLogSingularitiesAlong.exists_original_integral_equation
    {D : EffectiveGeometricQDivisor (m + 1) M} {u : M → EReal}
    (hu : NativeHasLogSingularitiesAlong D u) (x : M) :
    ∃ V : Opens M, x ∈ V ∧
      ∃ (s : Finset {P // 0 < D.coefficient P}) (d : ℕ)
        (a : {P // 0 < D.coefficient P} → ℕ),
        (∀ P, P ∈ s ↔ (P.val.val ∩ (V : Set M)).Nonempty) ∧ 0 < d ∧
        (∀ P ∈ s, 0 < a P ∧ D.coefficient P.val = (a P : ℚ) / (d : ℚ)) ∧
        let F := ∑ P ∈ s, a P • geometricPrimeCarrierEffectiveDivisor P.val
        ∃ g : M → ℂ,
          (∀ᶠ y in 𝓝 x, HolomorphicAt (m + 1) g y ∧ ∀ b,
            F.ideal.mem y b ↔ IsInSpanAt (n := m + 1) (· = g) y b) ∧
          ∃ b : M → ℝ, BoundedRealGermAt b x ∧
            u =ᶠ[𝓝 x] fun y => (((1 / (d : ℚ) : ℚ) : ℝ) : EReal) *
              logNormSq (g y) + (b y : EReal) := by
  classical
  obtain ⟨V, hxV, s, d, a, hs, hd, ha, hreader⟩ :=
    exists_geometric_q_local_integral_open_coefficients D x
  let F := ∑ P ∈ s, a P • geometricPrimeCarrierEffectiveDivisor P.val
  obtain ⟨g, _hfg, _hFg, hgen, _hzero⟩ := exists_cartier_centered_stalk_generator F x
  obtain ⟨U, hxU, r, W, w, p, R, C, _hW, hw, hp, hideal, hsource, hC, hR, heq⟩ := hu.2 x
  obtain ⟨k, A, hk, hA, hlog⟩ := exists_finite_rational_logarithmic_product_grouping_multiple
    (Finset.univ : Finset (Fin r)) w (fun i _ => hw i) d hd
  have hweights (i : Fin r) : w i = (A i : ℚ) / ((d * k : ℕ) : ℚ) :=
    (hA i (Finset.mem_univ i)).2
  let z : U := ⟨x, hxU⟩
  let E := ∑ i, A i • geometricPrimeCarrierEffectiveDivisor (W i)
  let K := cartierOpenRestriction (k • F) U
  let P : U → ℂ := fun y => ∏ i, p i y ^ A i
  let G : U → ℂ := fun y => g y ^ k
  have hcompare := scaled_cartier_stalk_comparison D F (V : Set M) d k hd hk U W w A
    hweights hsource (hreader U)
  have hPhol : HolomorphicAt (m + 1) P z := MonomialPart.holomorphicAt_finset_prod Finset.univ
    (fun i _ => CompanionReduction.holomorphicAt_pow_of (hp i z) (A i))
  have hPgen (b : U → ℂ) : K.ideal.mem z b ↔ IsInSpanAt (n := m + 1) (· = P) z b := by
    rw [hcompare z hxV b]
    apply finite_cartier_sum_generator_product Finset.univ
      (fun i => geometricPrimeCarrierEffectiveDivisor (W i)) A p z
      (fun i _ => hp i z)
    intro i _ b
    rw [geometricPrimeCarrierEffectiveDivisor_ideal]
    exact hideal i z b
  have hg : HolomorphicAt (m + 1) g x := hgen.self_of_nhds.1
  have hgpow : HolomorphicAt (m + 1) (fun y => g y ^ k) x :=
    CompanionReduction.holomorphicAt_pow_of hg k
  have hGhol : HolomorphicAt (m + 1) G z := by
    change HolomorphicAt (m + 1) ((fun y : M => g y ^ k) ∘ (Subtype.val : U → M)) z
    exact (holomorphicAt_comp_val_iff U).mpr hgpow
  have hGgen (b : U → ℂ) : K.ideal.mem z b ↔ IsInSpanAt (n := m + 1) (· = G) z b :=
    cartierOpenRestriction_generator (k • F) U z (fun y => g y ^ k) hgpow
      (nsmul_generator_power F x g hg hgen.self_of_nhds.2 k) b
  have hlogP (y : U) : (∑ i, ((w i : ℝ) : EReal) * logNormSq (p i y)) =
      (((1 / ((d * k : ℕ) : ℚ) : ℚ) : ℝ) : EReal) * logNormSq (P y) := by
    simpa [Finset.sum_coe_sort, Finset.prod_coe_sort, P] using hlog (fun i => p i y)
  have huP : (u ∘ Subtype.val) =ᶠ[𝓝 z] fun y =>
      (((1 / ((d * k : ℕ) : ℚ) : ℚ) : ℝ) : EReal) * logNormSq (P y) + (R y : EReal) :=
    Eventually.of_forall fun y => (heq y).trans
      (congrArg (fun t => t + (R y : EReal)) (hlogP y))
  obtain ⟨bU, hbU, huG⟩ := exists_native_bounded_logarithmic_generator_transition
    K z P G hPhol hGhol hPgen hGgen (1 / ((d * k : ℕ) : ℚ)) (by positivity)
    (u ∘ Subtype.val) R ⟨C, hC, Eventually.of_forall hR⟩ huP
  have hpower (v : ℂ) : logNormSq (v ^ k) = ((k : ℝ) : EReal) * logNormSq v := by
    simpa [logNormSq] using logNormSq_geometric_product (fun _ : Fin 1 => v) (fun _ => k) 1
  have hscale : (((1 / ((d * k : ℕ) : ℚ) : ℚ) : ℝ) : EReal) * ((k : ℝ) : EReal) =
      (((1 / (d : ℚ) : ℚ) : ℝ) : EReal) := by
    rw [← EReal.coe_mul]
    congr 1
    have hQ : (1 / ((d * k : ℕ) : ℚ)) * (k : ℚ) = 1 / (d : ℚ) := by
      have hdQ : (d : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
      have hkQ : (k : ℚ) ≠ 0 := by exact_mod_cast hk.ne'
      push_cast
      field_simp
    exact_mod_cast hQ
  have huU : (u ∘ Subtype.val) =ᶠ[𝓝 z] fun y =>
      (((1 / (d : ℚ) : ℚ) : ℝ) : EReal) * logNormSq (g y) + (bU y : EReal) := by
    filter_upwards [huG] with y hy
    change u y = _ at hy ⊢
    change u y = (((1 / ((d * k : ℕ) : ℚ) : ℚ) : ℝ) : EReal) *
      logNormSq (g y ^ k) + (bU y : EReal) at hy
    simpa only [hpower, ← mul_assoc, hscale] using hy
  let b : M → ℝ := fun y => if hy : y ∈ U then bU ⟨y, hy⟩ else 0
  have hbval (y : U) : b y = bU y := by
    dsimp only [b]
    rw [dif_pos y.2]
  have hb : BoundedRealGermAt b x := by
    obtain ⟨B, hB, hbound⟩ := hbU
    refine ⟨B, hB, (eventually_nhds_val_iff U (x := z)).mpr ?_⟩
    filter_upwards [hbound] with y hy
    simpa only [hbval] using hy
  refine ⟨V, hxV, s, d, a, hs, hd, ha, g, hgen, b, hb, ?_⟩
  apply (eventually_nhds_val_iff U (x := z)).mpr
  filter_upwards [huU] with y hy
  rw [hbval]
  exact hy

end SGPT.PSH
