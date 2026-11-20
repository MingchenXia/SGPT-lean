import SGPT.Projective.OkoNov16AttributedCompactCartierReuse
import SGPT.PSH.NativeLogSingularities
import SGPT.PSH.GeometricQOpenCartierCompatibility
import SGPT.PSH.CanonicalCartierFaithfulness
import SGPT.PSH.NativeCartierGeneratorUnits
import SGPT.PSH.LocalRationalDenominatorMultiple

/-! Complete native original log data give the SAME genuine GLOBAL Cartier
generator equation with an internally produced bounded real remainder. -/
/-! Exact attributed proof reuse of GlobalCartierLogGerm.lean; ZERO new mathematical/source credit.
Blueprint oko-nov16-attributed-geometric-log-reuse.tex. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.Okounkov.OkoNov16.AttributedGeometricLogReuse
open Set Filter TopologicalSpace
open SGPT.PSH
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending
open scoped Topology Manifold ContDiff Classical
universe u
variable {m : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m+1)) M] [IsComplexManifold (m+1) M]

private theorem finite_prime_coefficient_cast {r : ℕ}
    (W : Fin r → GeometricPrimeCarrier (m+1) M) (a : Fin r → ℕ)
    (P : GeometricPrimeCarrier (m+1) M) :
    (cartierGeometricPrimeCoefficient (∑ i,a i • geometricPrimeCarrierEffectiveDivisor (W i)) P : ℚ)=
      ∑ i,if W i=P then (a i : ℚ) else 0 := by
  rw [cartierGeometricPrimeCoefficient_finset_sum,Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Nat.cast_mul,cartierGeometricPrimeCoefficient_reduced]
  by_cases hi : W i=P
  · simp [hi]
  · simp [hi,Ne.symm hi]

private theorem nsmul_generator_power (F : EffectiveDivisor (m+1) M) (x : M) (g : M → ℂ)
    (hg : HolomorphicAt (m+1) g x)
    (hgen : ∀ b,F.ideal.mem x b ↔ IsInSpanAt (n := m+1) (· = g) x b)
    (k : ℕ) (b : M → ℂ) :
    (k • F).ideal.mem x b ↔ IsInSpanAt (n := m+1) (· = fun y => g y ^ k) x b := by
  rw [HironakaEffectiveDivisorSum.ideal_nsmul]
  exact HironakaSNCComponentCoefficients.idealPow_mem_iff_of_generator hg hgen k b

/-- Actual native source logarithms and the genuine global Cartier coefficient
dictionary produce u=(1/d)log|g|²+b for ANY actual generator of SAME F at x.
Full ideals and a bounded unit transition are proved internally; no local
logarithmic equation or remainder certificate is an input. -/
theorem exists_log_germ_of_global_cartier_coefficients
    {D : EffectiveGeometricQDivisor (m+1) M} {u : M → EReal}
    (hu : NativeHasLogSingularitiesAlong D u)
    (F : EffectiveDivisor (m+1) M) (d : ℕ) (hd : 0<d)
    (hcoeff : ∀ Q,D.coefficient Q=(cartierGeometricPrimeCoefficient F Q : ℚ)/(d : ℚ))
    (x : M) (g : M → ℂ) (hg : HolomorphicAt (m+1) g x)
    (hgen : ∀ b,F.ideal.mem x b ↔ IsInSpanAt (n := m+1) (· = g) x b) :
    ∃ b : M → ℝ,BoundedRealGermAt b x ∧
      u =ᶠ[𝓝 x] fun y => (((1/(d : ℚ) : ℚ) : ℝ) : EReal)*logNormSq (g y)+(b y : EReal) := by
  obtain ⟨O,hxO,r,W,w,p,R,C,_hW,hw,hp,hideal,hsource,hC,hR,heq⟩ := hu.2 x
  obtain ⟨k,A,hk,hA,hlog⟩ := exists_finite_rational_logarithmic_product_grouping_multiple
    (Finset.univ : Finset (Fin r)) w (fun i _ => hw i) d hd
  have hweights (i : Fin r) : w i=(A i : ℚ)/((d*k : ℕ) : ℚ) := (hA i (Finset.mem_univ i)).2
  let z : O := ⟨x,hxO⟩
  let H := ∑ i,A i • geometricPrimeCarrierEffectiveDivisor (W i)
  let K := k • cartierOpenRestriction F O
  let P : O → ℂ := fun y => ∏ i,p i y ^ A i
  let G : O → ℂ := fun y => g y ^ k
  have hdQ : (d : ℚ)≠0 := by exact_mod_cast hd.ne'
  have hdkQ : ((d*k : ℕ) : ℚ)≠0 := by exact_mod_cast Nat.mul_ne_zero hd.ne' hk.ne'
  have hreader (Q : GeometricPrimeCarrier (m+1) O) :
      (geometricQDivisorOpenRestriction D O).coefficient Q=
        (cartierGeometricPrimeCoefficient (cartierOpenRestriction F O) Q : ℚ)/(d : ℚ) := by
    have hQ : (Q.val ∩ (Subtype.val : O → M) ⁻¹' (univ : Set M)).Nonempty := by
      obtain ⟨q,hq⟩ := Q.nonempty
      exact ⟨q,hq,mem_univ _⟩
    have hr := geometricQDivisorOpenRestriction_coefficient_of_local_cartier_coefficients
      D F (1/(d : ℚ)) (by positivity) univ (fun Q _ => by rw [hcoeff Q];ring) O Q hQ
    exact hr.trans (by ring)
  have hCartier : H=K := by
    apply cartier_eq_of_geometricPrimeCoefficient_eq
    intro Q
    have hH : (cartierGeometricPrimeCoefficient H Q : ℚ)/((d*k : ℕ) : ℚ)=
        (geometricQDivisorOpenRestriction D O).coefficient Q := by
      rw [finite_prime_coefficient_cast,Finset.sum_div,hsource]
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : W i=Q
      · simp only [if_pos hi,←hweights i]
      · simp only [if_neg hi,zero_div]
    rw [hreader Q] at hH
    have hcross := (div_eq_div_iff hdkQ hdQ).mp hH
    change cartierGeometricPrimeCoefficient H Q=cartierGeometricPrimeCoefficient
      (k • cartierOpenRestriction F O) Q
    rw [cartierGeometricPrimeCoefficient_nsmul]
    apply Nat.cast_injective (R := ℚ)
    rw [Nat.cast_mul]
    apply mul_right_cancel₀ hdQ
    calc
      (cartierGeometricPrimeCoefficient H Q : ℚ)*(d : ℚ)=
        (cartierGeometricPrimeCoefficient (cartierOpenRestriction F O) Q : ℚ)*((d*k : ℕ) : ℚ) := hcross
      _ = _ := by push_cast;ring
  have hPhol : HolomorphicAt (m+1) P z := MonomialPart.holomorphicAt_finset_prod Finset.univ
    (fun i _ => CompanionReduction.holomorphicAt_pow_of (hp i z) (A i))
  have hPgen (b : O → ℂ) : K.ideal.mem z b ↔ IsInSpanAt (n := m+1) (· = P) z b := by
    rw [←hCartier]
    apply finite_cartier_sum_generator_product Finset.univ
      (fun i => geometricPrimeCarrierEffectiveDivisor (W i)) A p z (fun i _ => hp i z)
    intro i _ b
    rw [geometricPrimeCarrierEffectiveDivisor_ideal]
    exact hideal i z b
  have hgpow : HolomorphicAt (m+1) (fun y => g y ^ k) x := CompanionReduction.holomorphicAt_pow_of hg k
  have hGhol : HolomorphicAt (m+1) G z := by
    change HolomorphicAt (m+1) ((fun y : M => g y ^ k) ∘ Subtype.val) z
    exact (holomorphicAt_comp_val_iff O).mpr hgpow
  have hGgen (b : O → ℂ) : K.ideal.mem z b ↔ IsInSpanAt (n := m+1) (· = G) z b := by
    have hKO : cartierOpenRestriction (k • F) O=K := map_nsmul (cartierOpenRestrictionHom O) k F
    rw [←hKO]
    exact cartierOpenRestriction_generator (k • F) O z (fun y => g y ^ k) hgpow
      (nsmul_generator_power F x g hg hgen k) b
  have hlogP (y : O) : (∑ i,((w i : ℝ) : EReal)*logNormSq (p i y))=
      (((1/((d*k : ℕ) : ℚ) : ℚ) : ℝ) : EReal)*logNormSq (P y) := by
    simpa [Finset.sum_coe_sort,Finset.prod_coe_sort,P] using hlog (fun i => p i y)
  have huP : (u ∘ Subtype.val) =ᶠ[𝓝 z] fun y =>
      (((1/((d*k : ℕ) : ℚ) : ℚ) : ℝ) : EReal)*logNormSq (P y)+(R y : EReal) :=
    Eventually.of_forall fun y => (heq y).trans
      (congrArg (fun t => t+(R y : EReal)) (hlogP y))
  obtain ⟨bO,hbO,huG⟩ := exists_native_bounded_logarithmic_generator_transition K z P G
    hPhol hGhol hPgen hGgen (1/((d*k : ℕ) : ℚ)) (by positivity)
    (u ∘ Subtype.val) R ⟨C,hC,Eventually.of_forall hR⟩ huP
  have hpower (v : ℂ) : logNormSq (v ^ k)=((k : ℝ) : EReal)*logNormSq v := by
    simpa [logNormSq] using logNormSq_geometric_product (fun _ : Fin 1 => v) (fun _ => k) 1
  have hscale : (((1/((d*k : ℕ) : ℚ) : ℚ) : ℝ) : EReal)*((k : ℝ) : EReal)=
      (((1/(d : ℚ) : ℚ) : ℝ) : EReal) := by
    rw [←EReal.coe_mul]
    congr 1
    have hQ : (1/((d*k : ℕ) : ℚ))*(k : ℚ)=1/(d : ℚ) := by
      have hkQ : (k : ℚ)≠0 := by exact_mod_cast hk.ne'
      push_cast
      field_simp
    exact_mod_cast hQ
  have huO : (u ∘ Subtype.val) =ᶠ[𝓝 z] fun y =>
      (((1/(d : ℚ) : ℚ) : ℝ) : EReal)*logNormSq (g y)+(bO y : EReal) := by
    filter_upwards [huG] with y hy
    change u y=(((1/((d*k : ℕ) : ℚ) : ℚ) : ℝ) : EReal)*logNormSq (g y ^ k)+(bO y : EReal) at hy
    simpa only [Function.comp_apply,hpower,←mul_assoc,hscale] using hy
  let b : M → ℝ := fun y => if hy : y∈O then bO ⟨y,hy⟩ else 0
  have hbval (y : O) : b y=bO y := by simp only [b,dif_pos y.property]
  have hb : BoundedRealGermAt b x := by
    obtain ⟨B,hB,hbound⟩ := hbO
    refine ⟨B,hB,(eventually_nhds_val_iff O (x := z)).mpr ?_⟩
    filter_upwards [hbound] with y hy
    simpa only [hbval] using hy
  refine ⟨b,hb,(eventually_nhds_val_iff O (x := z)).mpr ?_⟩
  filter_upwards [huO] with y hy
  rw [hbval]
  exact hy

end SGPT.Okounkov.OkoNov16.AttributedGeometricLogReuse
