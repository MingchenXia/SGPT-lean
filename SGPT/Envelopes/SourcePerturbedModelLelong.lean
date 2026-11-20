import SGPT.Envelopes.SourcePerturbedModelLimits
import SGPT.Envelopes.SourcePositiveAffineEnvelopes
import SGPT.PSH.BookDeep2LelongBound
import SGPT.PSH.CompactPrimeNumerical
import SGPT.Foundations.Analysis.Pending.DivisorialRooftopLelongEstimate

set_option autoImplicit false
noncomputable section
universe u
namespace SGPT.PSH.SourcePerturbedModelLelongDraft
open Set Filter MeasureTheory
open scoped Topology ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses
  SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus SGPT.Foundations.Analysis.Pending
  SGPT.Foundations.Analysis.Pending.DiagonalMass
  SGPT.Foundations.Analysis.Pending.ThetaPshConvexCombination
  SGPT.PSH.VariableComplexAtlas SGPT.PSH.CompactPrimeOver

/-- Actual admissibility of every fixed coefficient is eventually produced
from the genuine positive mass limit, without an admissibility certificate. -/
theorem eventual_admissibleWeight {I : Type*} {F : Filter I} {n : ℕ}
    {p q : I → ENNReal} {m : ENNReal} (hm : 0 < m) (hmfin : m ≠ ⊤)
    (hp : ∀ i, m ≤ p i) (hpq : ∀ i, p i ≤ q i)
    (hq : Tendsto q F (𝓝 m)) {a : ℝ} (ha : 1 < a) :
    ∀ᶠ i in F, ConvexCombEnvelopeMass.IsAdmissibleWeight n (p i) (q i) a := by
  have hsub : Tendsto (fun i => q i - m) F (𝓝 0) := by
    simpa only [tsub_self] using ENNReal.Tendsto.sub hq tendsto_const_nhds (Or.inr hmfin)
  have hmul : Tendsto (fun i => ENNReal.ofReal (a^n) * (q i-m)) F (𝓝 0) := by
    simpa only [mul_zero] using ENNReal.Tendsto.const_mul hsub (Or.inr ENNReal.ofReal_ne_top)
  filter_upwards [hmul.eventually (gt_mem_nhds hm)] with i hi
  have hh : ENNReal.ofReal (a^n)*(q i-p i) ≤ ENNReal.ofReal (a^n)*(q i-m) := by
    simpa only [mul_comm] using
      (mul_le_mul_left (tsub_le_tsub_left (hp i) (q i)) (ENNReal.ofReal (a^n)))
  exact ⟨ha,hh.trans_lt (hi.trans_le ((hp i).trans (hpq i)))⟩

/-- Clear the genuine inverse-coefficient convex combination, INCLUDING poles. -/
theorem clear_inverse_convexComb {M : Type*} {η ψ φ : M → EReal} {C : ℕ}
    (hC : 2 ≤ C) (hbar : convexComb (C : ℝ)⁻¹ η ψ ≤ φ) :
    ∀ x, η x + (((C-1 : ℕ) : ℝ) : EReal) * ψ x ≤ ((C : ℝ) : EReal) * φ x := by
  have hCp : 0 < (C : ℝ) := by exact_mod_cast (by omega : 0 < C)
  have hC0 : (C : ℝ) ≠ 0 := hCp.ne'
  have hc : (C : ℝ) * (1-(C : ℝ)⁻¹) = ((C-1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega : 1 ≤ C),Nat.cast_one]
    field_simp
  intro x
  have h := mul_le_mul_of_nonneg_left (hbar x)
    (show (0 : EReal) ≤ ((C : ℝ) : EReal) by exact_mod_cast hCp.le)
  rw [convexComb_apply,EReal.left_distrib_of_nonneg_of_ne_top
    (by exact_mod_cast hCp.le) (EReal.coe_ne_top _),
    ← mul_assoc,← EReal.coe_mul,mul_inv_cancel₀ hC0,EReal.coe_one,one_mul,
    ← mul_assoc,← EReal.coe_mul,hc] at h
  exact h

/-- Finite actual reader limits are uniquely forced by all true integer
rooftop estimates; no limiting reader equality is supplied. -/
theorem eq_of_all_integer_rooftop_estimates {L M : ENNReal} (hL : L ≠ ⊤) (hM : M ≠ ⊤)
    (hLM : L ≤ M) {B : ℝ} (hB : 0 ≤ B)
    (he : ∀ C : ℕ, 2 ≤ C → ENNReal.ofReal (C : ℝ)*M ≤
      ENNReal.ofReal B+ENNReal.ofReal ((C-1 : ℕ) : ℝ)*L) : L = M := by
  by_contra hne
  have hlt : L < M := lt_of_le_of_ne hLM hne
  have hltR : L.toReal < M.toReal := (ENNReal.toReal_lt_toReal hL hM).mpr hlt
  obtain ⟨C,hC⟩ := exists_nat_gt (max (2 : ℝ) (B/(M.toReal-L.toReal)))
  have hC2 : 2 ≤ C := by
    have h := (le_max_left (2 : ℝ) (B/(M.toReal-L.toReal))).trans_lt hC
    exact_mod_cast h.le
  have hCgap : B < (C : ℝ)*(M.toReal-L.toReal) := by
    have h := (le_max_right (2 : ℝ) (B/(M.toReal-L.toReal))).trans_lt hC
    exact (div_lt_iff₀ (sub_pos.mpr hltR)).mp h
  have hprod : ENNReal.ofReal ((C-1 : ℕ) : ℝ)*L ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hL
  have hr := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top,hprod⟩) (he C hC2)
  simp only [ENNReal.toReal_add ENNReal.ofReal_ne_top hprod,ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (Nat.cast_nonneg C),
    ENNReal.toReal_ofReal (Nat.cast_nonneg (C-1)),ENNReal.toReal_ofReal hB] at hr
  rw [Nat.cast_sub (by omega : 1 ≤ C),Nat.cast_one] at hr
  nlinarith [ENNReal.toReal_nonneg (a := L)]

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [ConnectedSpace X]

omit [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [ConnectedSpace X] in
private theorem actualPerturbedPSH (ω : KahlerBackground n X)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n X)} {u : X → EReal}
    (hu : (ofFixedModel n X).IsThetaPSH θ u) {ε : ℝ} (hε : 0 ≤ ε) :
    (ofFixedModel n X).IsThetaPSH
      (nativeClosedFormToAtlas (atlasClosedFormToNative θ+ε•ω.form)) u := by
  apply (isThetaPSH_iff_nativeThetaPotential _ _).mpr
  rw [sourceNativeAtlasForm_roundTrip]
  exact LocalPotentials.isThetaPshPotential_add_of_semipositive
    ((isThetaPSH_iff_nativeThetaPotential _ _).mp hu)
    (KahlerDomination.isSemipositive_smul ω.isSemipositive hε)

omit [ConnectedSpace X] in
/-- Actual original mass monotonicity for the SAME potential under every
nonnegative Kähler background perturbation, including the literal zero error. -/
theorem sourceMass_le_perturbed (ω : KahlerBackground n X)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n X)} {u : X → EReal}
    (hu : (ofFixedModel n X).IsThetaPSH θ u) {ε : ℝ} (hε : 0 ≤ ε) :
    sourcePotentialNonPluripolarMeasure θ u hu univ ≤
      sourcePotentialNonPluripolarMeasure
        (nativeClosedFormToAtlas (atlasClosedFormToNative θ+ε•ω.form)) u
        (actualPerturbedPSH ω hu hε) univ := by
  have hn := (isThetaPSH_iff_nativeThetaPotential _ _).mp hu
  have hp := (isThetaPSH_iff_nativeThetaPotential _ _).mp (actualPerturbedPSH ω hu hε)
  rw [sourceNativeAtlasForm_roundTrip] at hp
  have hz : IsThetaPshPotential (atlasClosedFormToNative θ+(0 : ℝ)•ω.form).val u := by
    simpa only [zero_smul,add_zero] using hn
  have h := TraceFreeLimit.diagonalPotentialMeasure_le_of_le ω hε hz hp univ
  simpa only [sourcePotentialNonPluripolarMeasure,sourceNativeAtlasForm_roundTrip,
    zero_smul,add_zero] using h

/-- Positive actual original limiting mass and the actual varying-background
stage mass limit PRODUCE the entire original affine barrier family eventually.
No admissible coefficient or desired affine barrier is supplied by callers. -/
theorem eventual_actual_affineBarrier {I : Type*} {F : Filter I}
    (ω : KahlerBackground n X) (θ : AtlasClosedRealOneOneForm (ofFixedModel n X))
    (ε : I → ℝ) (hε : ∀ i,0 ≤ ε i) (φ : I → X → EReal) (u : X → EReal)
    (hu : (ofFixedModel n X).IsThetaPSH θ u)
    (hφ : ∀ i,(ofFixedModel n X).IsThetaPSH
      (nativeClosedFormToAtlas (atlasClosedFormToNative θ+ε i•ω.form)) (φ i))
    (hle : ∀ i,u ≤ φ i)
    (hm : 0 < sourcePotentialNonPluripolarMeasure θ u hu univ)
    (hlim : Tendsto (fun i => sourcePotentialNonPluripolarMeasure
      (nativeClosedFormToAtlas (atlasClosedFormToNative θ+ε i•ω.form)) (φ i) (hφ i) univ)
      F (𝓝 (sourcePotentialNonPluripolarMeasure θ u hu univ)))
    {a : ℝ} (ha : 1 < a) :
    ∀ᶠ i in F, ∃ η : X → EReal,
      (ofFixedModel n X).IsThetaPSH
        (nativeClosedFormToAtlas (atlasClosedFormToNative θ+ε i•ω.form)) η ∧
      convexComb a⁻¹ η (φ i) ≤ u := by
  let Γ i := nativeClosedFormToAtlas (atlasClosedFormToNative θ+ε i•ω.form)
  have hup i : (ofFixedModel n X).IsThetaPSH (Γ i) u := actualPerturbedPSH ω hu (hε i)
  let p i := sourcePotentialNonPluripolarMeasure (Γ i) u (hup i) univ
  let q i := sourcePotentialNonPluripolarMeasure (Γ i) (φ i) (hφ i) univ
  have hmp i : sourcePotentialNonPluripolarMeasure θ u hu univ ≤ p i := sourceMass_le_perturbed ω hu (hε i)
  have hpq i : p i ≤ q i := sourcePotentialNonPluripolarMass_mono ω (hup i) (hφ i)
    (MoreSingularOn.of_le fun x _ => hle i x)
  have hadm := eventual_admissibleWeight hm (sourceAffine_mass_lt_top ω hu).ne hmp hpq hlim (n := n) ha
  filter_upwards [hadm] with i hi
  have hpos := hm.trans_le (hmp i)
  have hc := (sourceAffineCoefficient_iff hpos (hpq i) (sourceAffine_mass_lt_top ω (hφ i)).ne).mpr hi
  obtain ⟨hE,_,hbar,_⟩ := sourcePositiveAffineEnvelope ω (hup i) (hφ i)
    (MoreSingularOn.of_le fun x _ => hle i x) hpos hc
  exact ⟨_,hE,hbar⟩

private theorem sourceGenericLelong_eq_half_native
    {m : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (ComplexModel (m+1)) M] [IsComplexManifold (m+1) M]
    (a : M → EReal) (E : Set M) :
    (ofFixedModel (m+1) M).sourceGenericLelong a E =
      (2 : ENNReal)⁻¹ * DemaillyApproximantDivisorialLelong.divisorialLelongNumber m a E := by
  simp only [sourceGenericLelong,sourceLelong_ofFixedModel_eq]
  rw [DemaillyApproximantDivisorialLelong.divisorialLelongNumber,
    SquaredLogLelongSourceNormalization.iInf_lelongNumber_eq_two_mul_squaredLog (Nat.succ_ne_zero m)]
  symm
  exact ENNReal.inv_mul_cancel_left (by norm_num) (by norm_num)

/-- Actual varying-background mass convergence and the original positive
limiting mass imply true Lelong convergence on EVERY original proper prime
model. All barriers, uniform finite bounds and reader-limit identification
are produced internally; no original I-goodness or model condition is needed. -/
theorem tendsto_presentationReader_of_actual_mass_limit
    {I : Type*} [Preorder I] [IsDirectedOrder I] [Nonempty I]
    (ω : KahlerBackground n X) (θ : AtlasClosedRealOneOneForm (ofFixedModel n X))
    (ε : I → ℝ) (hε : ∀ i,0 ≤ ε i) (hεanti : Antitone ε)
    (φ : I → X → EReal) (u : X → EReal) (hanti : Antitone φ)
    (hu : (ofFixedModel n X).IsThetaPSH θ u)
    (hφ : ∀ i,(ofFixedModel n X).IsThetaPSH
      (nativeClosedFormToAtlas (atlasClosedFormToNative θ+ε i•ω.form)) (φ i))
    (hle : ∀ i,u ≤ φ i)
    (hm : 0 < sourcePotentialNonPluripolarMeasure θ u hu univ)
    (hlim : Tendsto (fun i => sourcePotentialNonPluripolarMeasure
      (nativeClosedFormToAtlas (atlasClosedFormToNative θ+ε i•ω.form)) (φ i) (hφ i) univ)
      atTop (𝓝 (sourcePotentialNonPluripolarMeasure θ u hu univ)))
    (p : PrimePresentation n X) :
    Tendsto (fun i => presentationReader (φ i) p) atTop (𝓝 (presentationReader u p)) := by
  cases n with
  | zero => have hp := p.dimension_pos; omega
  | succ m =>
    let i₀ : I := Classical.arbitrary I
    let Θ : ClosedRealOneOneForm (m+1) X := atlasClosedFormToNative θ+ε i₀•ω.form
    have hup : IsThetaPshPotential Θ.val u := by
      have h := (isThetaPSH_iff_nativeThetaPotential _ _).mp (actualPerturbedPSH ω hu (hε i₀))
      simpa only [sourceNativeAtlasForm_roundTrip] using h
    have hφup (i : I) (hi : i₀ ≤ i) : IsThetaPshPotential Θ.val (φ i) := by
      have h := (isThetaPSH_iff_nativeThetaPotential _ _).mp (hφ i)
      rw [sourceNativeAtlasForm_roundTrip] at h
      exact SGPT.Envelopes.PerturbedModelLimit.isThetaPshPotential_perturb_mono ω (hεanti hi) h
    let : CompactSpace p.model :=
      AnalyticModificationStrongPullback.compactSpace_of_isAnalyticModification p.modification
    let ΘY := ClosedRealOneOneForm.pullback p.modification.1 Θ
    have huY : IsThetaPshPotential ΘY.val (u ∘ p.projection) :=
      AnalyticModificationStrongPullback.isThetaPshPotential_comp_of_isAnalyticModification
        p.modification Θ hup
    let ν (v : X → EReal) :=
      DemaillyApproximantDivisorialLelong.divisorialLelongNumber m (v ∘ p.projection) p.divisor
    have hνanti {f g : X → EReal} (h : f ≤ g) : ν g ≤ ν f := by
      change ν g ≤ ⨅ y ∈ p.divisor, lelongNumber (n := m+1) (f ∘ p.projection) y
      refine le_iInf fun y => le_iInf fun hy => ?_
      exact (DemaillyApproximantDivisorialLelong.divisorialLelongNumber_le hy).trans
        (KahlerCurrentMax.lelongNumber_le_of_eventually_le
          (Eventually.of_forall fun y => h (p.projection y)))
    have hνmono : Monotone (fun i => ν (φ i)) := fun i j hij => hνanti (hanti hij)
    let L : ENNReal := ⨆ i,ν (φ i)
    have hLM : L ≤ ν u := iSup_le fun i => hνanti (hle i)
    have hMfin : ν u ≠ ⊤ := by
      obtain ⟨N,hN⟩ := UniformLelongBound.hasUniformLelongBound (Nat.succ_pos m) ΘY
      obtain ⟨y,hy⟩ := p.smooth.2.1.nonempty
      exact (lt_of_le_of_lt
        ((DemaillyApproximantDivisorialLelong.divisorialLelongNumber_le hy).trans
          (hN _ huY y)) ENNReal.ofReal_lt_top).ne
    have hLfin : L ≠ ⊤ := ne_top_of_le_ne_top hMfin hLM
    have hνlim : Tendsto (fun i => ν (φ i)) atTop (𝓝 L) := tendsto_atTop_iSup hνmono
    obtain ⟨B,hB,hroof⟩ :=
      DivisorialRooftopLelongEstimate.exists_uniform_divisorial_rooftop_estimate ΘY
    have he (C : ℕ) (hC : 2 ≤ C) :
        ENNReal.ofReal (C : ℝ)*ν u ≤ ENNReal.ofReal B+ENNReal.ofReal ((C-1 : ℕ) : ℝ)*L := by
      have hCp : 1 < (C : ℝ) := by exact_mod_cast (by omega : 1 < C)
      have hbar := eventual_actual_affineBarrier ω θ ε hε φ u hu hφ hle hm hlim hCp
      have hev : ∀ᶠ i in atTop, ENNReal.ofReal (C : ℝ)*ν u ≤
          ENNReal.ofReal B+ENNReal.ofReal ((C-1 : ℕ) : ℝ)*ν (φ i) := by
        filter_upwards [hbar,eventually_ge_atTop i₀] with i hi hi₀
        obtain ⟨η,hη,hηbar⟩ := hi
        have hηn := (isThetaPSH_iff_nativeThetaPotential _ _).mp hη
        rw [sourceNativeAtlasForm_roundTrip] at hηn
        have hηup := SGPT.Envelopes.PerturbedModelLimit.isThetaPshPotential_perturb_mono
          ω (hεanti hi₀) hηn
        have hηY := AnalyticModificationStrongPullback.isThetaPshPotential_comp_of_isAnalyticModification
          p.modification Θ hηup
        have hφY := AnalyticModificationStrongPullback.isThetaPshPotential_comp_of_isAnalyticModification
          p.modification Θ (hφup i hi₀)
        have hc := clear_inverse_convexComb hC hηbar
        exact hroof hηY hφY hC (fun y => hc (p.projection y)) p.divisor
      have hr : Tendsto (fun i => ENNReal.ofReal B+
          ENNReal.ofReal ((C-1 : ℕ) : ℝ)*ν (φ i)) atTop
          (𝓝 (ENNReal.ofReal B+ENNReal.ofReal ((C-1 : ℕ) : ℝ)*L)) :=
        tendsto_const_nhds.add (ENNReal.Tendsto.const_mul hνlim (Or.inr ENNReal.ofReal_ne_top))
      exact ge_of_tendsto hr hev
    have hL : L = ν u := eq_of_all_integer_rooftop_estimates hLfin hMfin hLM hB he
    rw [hL] at hνlim
    have hh := ENNReal.Tendsto.const_mul hνlim
      (a := (2 : ENNReal)⁻¹) (Or.inr (by norm_num))
    simpa only [presentationReader,sourceGenericLelong_eq_half_native,ν] using hh

/-- WHOLE original prop:vol_limit_model, all natural dimensions and original
arbitrary directed nets. The exact original infimum's source PSH membership,
ordinary-envelope fixed point, actual varying-background mass limit, and
conditional Lelong convergence on the ORIGINAL direct prime quotient are
all internally produced. Only the printed positive infimum mass is required
for the last clause; stage mass positivity and all other auxiliary data are outputs. -/
theorem source_vol_limit_model
    (ω : KahlerBackground n X) (θ : AtlasClosedRealOneOneForm (ofFixedModel n X))
    {I : Type*} [Preorder I] [IsDirectedOrder I] [Nonempty I]
    {ε : I → ℝ} (hε0 : ∀ i,0 ≤ ε i) (hεanti : Antitone ε) (hεlim : Tendsto ε atTop (𝓝 0))
    {φ : I → X → EReal} (hφanti : Antitone φ)
    (hφ : ∀ i,(ofFixedModel n X).IsThetaPSH
      (nativeClosedFormToAtlas (atlasClosedFormToNative θ+ε i•ω.form)) (φ i))
    (hfix : ∀ i,sourceSingularityEnvelope
      (nativeClosedFormToAtlas (atlasClosedFormToNative θ+ε i•ω.form)) (φ i) = φ i) :
    ∃ hinf : (ofFixedModel n X).IsThetaPSH θ (fun x => ⨅ i,φ i x),
      sourceSingularityEnvelope θ (fun x => ⨅ i,φ i x) = (fun x => ⨅ i,φ i x) ∧
      Tendsto (fun i => sourcePotentialNonPluripolarMeasure
          (nativeClosedFormToAtlas (atlasClosedFormToNative θ+ε i•ω.form)) (φ i) (hφ i) univ)
        atTop (𝓝 (sourcePotentialNonPluripolarMeasure θ (fun x => ⨅ i,φ i x) hinf univ)) ∧
      (0 < sourcePotentialNonPluripolarMeasure θ (fun x => ⨅ i,φ i x) hinf univ →
        ∀ q : DirectPrimeOver n X,
          Tendsto (fun i => CompactPrimeNumerical.directSourceQPSHReader (φ i)
            ⟨nativeClosedFormToAtlas (atlasClosedFormToNative θ+ε i•ω.form),hφ i⟩ q) atTop
            (𝓝 (CompactPrimeNumerical.directSourceQPSHReader (fun x => ⨅ i,φ i x) ⟨θ,hinf⟩ q))) := by
  obtain ⟨hinf,hmodel,hmass⟩ := sourcePerturbedModel_iInf ω θ hε0 hεanti hεlim hφanti hφ hfix
  refine ⟨hinf,hmodel,hmass,?_⟩
  intro hpos q
  refine Quot.inductionOn q ?_
  intro p
  exact tendsto_presentationReader_of_actual_mass_limit ω θ ε hε0 hεanti φ
    (fun x => ⨅ i,φ i x) hφanti hinf hφ (fun i x => iInf_le (fun j => φ j x) i) hpos hmass p

end SGPT.PSH.SourcePerturbedModelLelongDraft
