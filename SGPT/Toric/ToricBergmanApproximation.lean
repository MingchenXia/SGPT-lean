/- Canonical staging of the immutable whole-original toric Bergman proof.
   Exact retained fragments/providers are recorded in fragment-provider-map.json.gz. -/
import SGPT.PSH.QuasiEquisingular
import SGPT.Toric.StrictPhysicalBergman


/- BEGIN SGPT.Toric.ToricPhysicalInputMonotonicity; source SHA256 88733b35431c7d140e656cfc87572de816ef2b385db7a221741505a1bca12443 -/
section ToricCanonicalFragment083

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric
open Set Filter Bundle MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.PSH SGPT.PSH.VariableComplexAtlas
open SGPT.Bergman.TensorDictionaryDraft
open SGPT.Foundations.Analysis.Pending.IntegrationCurrent
open SGPT.Bergman.NativeSingularPhi SGPT.Bergman.MultiplierSectionsDraft
open scoped Topology BigOperators ENNReal
variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin n → ℤ} {hs : latticePolytopeEdgeSmooth γ}

/-- True monotonicity of the SAME original physical product kernel in its
arbitrary singular input. It follows from inclusion of actual integral
unit balls, with the full original global section carrier unchanged. -/
theorem toricNativeStrictPhiProductPotential_mono_input {D : ToricDivisor γ hs}
    (h : BigToricMetric D) (q : ℕ) (hq : 0 < q)
    {φ ψ : PolytopeToricVariety γ hs → EReal}
    (hφ : (ofFixedModel n (PolytopeToricVariety γ hs)).IsQPSH φ)
    (hψ : (ofFixedModel n (PolytopeToricVariety γ hs)).IsQPSH ψ)
    (hφinv : PolytopeToricInvariant γ hs φ) (hψinv : PolytopeToricInvariant γ hs ψ)
    (hle : ∀ p, φ p ≤ ψ p) (p : PolytopeToricVariety γ hs) :
    toricNativeStrictPhiProductPotential h q hq hφ hφinv p ≤
      toricNativeStrictPhiProductPotential h q hq hψ hψinv p := by
  have hdens : toricNativeFiniteSectionDensity h q
      (toricNativeStrictPhiProductSections h q hq hφ hφinv) p ≤
      toricNativeFiniteSectionDensity h q (toricNativeStrictPhiProductSections h q hq hψ hψinv) p := by
    rw [toricNativeStrictPhiProductDensity_eq_original_kernel,
      toricNativeStrictPhiProductDensity_eq_original_kernel]
    simp only [nativePhiOriginalBergmanDensity, Nat.cast_one]
    apply iSup_le
    intro s
    apply iSup_le
    intro hsint
    apply le_iSup_of_le s
    have hint : (∫⁻ y, originalSectionDensity
        ((toricNativeHermitianLineBundle (toricNativeNegativeTwistMetric h q)).twistedPower
          HermitianHolomorphicLineBundle.unit 1).Fiber
        (fun x => ((q : ℝ) : EReal) * ψ x) 1 s y
        ∂(kahlerVolume (polytopeToricKahlerBackground γ hs))) ≤ 1 := by
      apply (lintegral_mono ?_).trans hsint
      intro y
      apply mul_le_mul_of_nonneg_left ?_ zero_le
      apply multiplierWeight_antitone (by norm_num : (0 : ℝ) ≤ 1)
      exact monotone_eReal_const_mul (c := (q : ℝ)) (Nat.cast_nonneg q) (hle y)
    exact le_iSup_of_le hint le_rfl
  exact monotone_eReal_const_mul (c := (q : ℝ)⁻¹) (by positivity) (ENNReal.log_monotone hdens)

end SGPT.Toric

end
end ToricCanonicalFragment083
/- END SGPT.Toric.ToricPhysicalInputMonotonicity -/

/- BEGIN SGPT.Toric.ToricShiftedPhysicalStage; source SHA256 34166e2b6fa8c3f7d00e0c22f0b17d6efd89ddadd0499ad1fd93e0026e8aa805 -/
section ToricCanonicalFragment084

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric
open Set Filter
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
open SGPT.Foundations.Analysis.FirstPass.NumericalRestrictedVolumeScaffold
open SGPT.PSH SGPT.PSH.VariableComplexAtlas
open scoped Topology BigOperators
variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin n → ℤ} {hs : latticePolytopeEdgeSmooth γ}

/-- Every prescribed positive small shift is eventually sufficient for the
actual physical kernel to lie above its arbitrary original input. Actual
same-theta toric strictness is produced at the same degrees. -/
theorem exists_toricNativeStrict_shifted_physical_properties {D : ToricDivisor γ hs}
    (h : BigToricMetric D) {w : PolytopeToricVariety γ hs → EReal}
    (hwmem : w ∈ h.PSHTor) (hwstrict : IsKahlerCurrentPotential h.form w)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, 0 < N ∧ ∀ q : ℕ, N ≤ q → ∀ hq : 0 < q,
      let hw : (ofFixedModel n (PolytopeToricVariety γ hs)).IsQPSH w := ⟨h.atlasForm, hwmem.1⟩
      let U := toricNativeFiniteSectionPotential h q
        (toricNativeFiniteSectionShift h q (toricNativeStrictPhiProductSections h q hq hw hwmem.2) ε)
      (∀ p, w p ≤ U p) ∧ U ∈ h.PSHTor ∧ IsKahlerCurrentPotential h.form U := by
  have hw : (ofFixedModel n (PolytopeToricVariety γ hs)).IsQPSH w := ⟨h.atlasForm, hwmem.1⟩
  obtain ⟨N₀, C, hN₀, _, hlower⟩ := toricNativeStrictPhiProductPotential_lower h hw hwmem.2 hwstrict
  obtain ⟨Nθ, _, hθ⟩ := toricNativeStrictPhiProductPotential_mem_PSHTor_eventually h hw hwmem.2 hwstrict
  obtain ⟨NK, _, hK⟩ := toricNativeStrictPhiProductPotential_isKahlerCurrent_eventually h hw hwmem.2 hwstrict
  obtain ⟨m, hm⟩ := exists_nat_ge (Real.log C / ε)
  let N := max N₀ (max Nθ (max NK m))
  refine ⟨N, by dsimp only [N]; omega, fun q hN hq => ?_⟩
  dsimp only
  rw [toricNativeFiniteSectionShift_potential h q hq]
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hmq : m ≤ q := by dsimp only [N] at hN; omega
  have herr : Real.log C / q ≤ ε := by
    apply (div_le_iff₀ hqR).mpr
    have hh : Real.log C / ε ≤ (q : ℝ) := hm.trans (by exact_mod_cast hmq)
    have hh' := (div_le_iff₀ hε).mp hh
    nlinarith
  refine ⟨fun p => ?_, ?_, ?_⟩
  · calc
      w p = (w p - ((Real.log C / q : ℝ) : EReal)) + ((Real.log C / q : ℝ) : EReal) := EReal.sub_add_cancel.symm
      _ ≤ toricNativeStrictPhiProductPotential h q hq hw hwmem.2 p + (ε : EReal) :=
        add_le_add (hlower q (by dsimp only [N] at hN; omega) hq p) (EReal.coe_le_coe_iff.mpr herr)
  · exact BigToricMetric.mem_PSHTor_add_const h (hθ q (by dsimp only [N] at hN; omega) hq) ε
  · obtain ⟨omega, hp⟩ := hK q (by dsimp only [N] at hN; omega) hq
    exact ⟨omega, hp.add_const ε⟩

end SGPT.Toric

end
end ToricCanonicalFragment084
/- END SGPT.Toric.ToricShiftedPhysicalStage -/

/- BEGIN SGPT.Toric.ToricDecreasingPhysicalStep; source SHA256 7905e19a7c7de50f2a464171075af7f60d6b3fe0b459bb17116871905b239151 -/
section ToricCanonicalFragment085

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric
open Set Filter
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
open SGPT.Foundations.Analysis.FirstPass.NumericalRestrictedVolumeScaffold
open SGPT.PSH SGPT.PSH.VariableComplexAtlas
open scoped Topology BigOperators
variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin n → ℤ} {hs : latticePolytopeEdgeSmooth γ}

/-- One genuine decreasing PHYSICAL step at an arbitrarily large original
degree. Every order, strictness, analytic and eigensection ingredient is
produced from actual original sections and the new arbitrary singular input. -/
theorem exists_toricNativeStrict_decreasing_physical_step {D : ToricDivisor γ hs}
    (h : BigToricMetric D) (q₀ : ℕ) (hq₀ : 0 < q₀) {d : ℕ}
    (a : Fin d → ToricNativePlainPowerSections h q₀)
    (humem : toricNativeFiniteSectionPotential h q₀ a ∈ h.PSHTor)
    {w : PolytopeToricVariety γ hs → EReal} (hwmem : w ∈ h.PSHTor)
    (hwstrict : IsKahlerCurrentPotential h.form w)
    {r B δ ε : ℝ} (hr : 1 < r) (hδ : 0 < δ) (hε : 0 < ε) (hεδ : ε ≤ δ / 4)
    (hcomp : ∀ p, w p ≤ (r : EReal) * toricNativeFiniteSectionPotential h q₀ a p + (B : EReal))
    (hgap : ∀ p, w p ≤ toricNativeFiniteSectionPotential h q₀ a p - (δ : EReal))
    (L : ℕ) :
    ∃ (q : ℕ) (hq : 0 < q) (b : ℕ) (s : Fin b → ToricNativePlainPowerSections h q),
      L ≤ q ∧ (∀ p, w p ≤ toricNativeFiniteSectionPotential h q s p) ∧
      toricNativeFiniteSectionPotential h q s ∈ h.PSHTor ∧
      IsKahlerCurrentPotential h.form (toricNativeFiniteSectionPotential h q s) ∧
      (∀ p, toricNativeFiniteSectionPotential h q s p ≤
        toricNativeFiniteSectionPotential h q₀ a p - ((δ / 4 : ℝ) : EReal)) ∧
      toricNativeFiniteSectionPotential h q s =
        (fun p => toricNativeStrictPhiProductPotential h q hq
          (show (ofFixedModel n (PolytopeToricVariety γ hs)).IsQPSH w from ⟨h.atlasForm, hwmem.1⟩) hwmem.2 p + (ε : EReal)) ∧
      ∀ i : Fin b, ∃ m : Fin n → ℤ, ∀ t : Fin n → ℂˣ,
        toricNativePlainSectionTranslation h q t (s i) = (latticeCharacter m t : ℂ) • s i := by
  have hw : (ofFixedModel n (PolytopeToricVariety γ hs)).IsQPSH w := ⟨h.atlasForm, hwmem.1⟩
  obtain ⟨M, hM, horder⟩ := exists_toricNativeStrict_below_previousPhysical h q₀ hq₀ a humem hwmem hr hδ hcomp hgap
  obtain ⟨NO, _, hNO⟩ := horder M le_rfl
  obtain ⟨NS, _, hNS⟩ := exists_toricNativeStrict_shifted_physical_properties h hwmem hwstrict ε hε
  let k : ℕ := max NO (max NS L)
  let q : ℕ := 2 ^ k * M
  have hq : 0 < q := Nat.mul_pos (pow_pos (by norm_num) k) hM
  have hkq : k ≤ q := (show k < 2 ^ k from Nat.lt_two_pow_self).le.trans
    (le_mul_of_one_le_right (Nat.zero_le _) (show 1 ≤ M by omega))
  have hNOq : NO ≤ q := (le_max_left _ _).trans hkq
  have hNSq : NS ≤ q := ((le_max_left _ _).trans (le_max_right _ _)).trans hkq
  have hLq : L ≤ q := ((le_max_right _ _).trans (le_max_right _ _)).trans hkq
  let s := toricNativeFiniteSectionShift h q (toricNativeStrictPhiProductSections h q hq hw hwmem.2) ε
  obtain ⟨hlower, hmem, hstrict⟩ := hNS q hNSq hq
  refine ⟨q, hq, _, s, hLq, hlower, hmem, hstrict, ?_, ?_, ?_⟩
  · intro p
    change toricNativeFiniteSectionPotential h q
      (toricNativeFiniteSectionShift h q (toricNativeStrictPhiProductSections h q hq hw hwmem.2) ε) p ≤ _
    rw [toricNativeFiniteSectionShift_potential h q hq]
    have hh := add_le_add (hNO k hNOq hq p) (le_refl (ε : EReal))
    apply hh.trans
    rw [sub_eq_add_neg, ← EReal.coe_neg, add_assoc, ← EReal.coe_add,
      sub_eq_add_neg, ← EReal.coe_neg]
    exact add_le_add le_rfl (EReal.coe_le_coe_iff.mpr (by linarith))
  · exact toricNativeFiniteSectionShift_potential h q hq _ ε
  · exact toricNativeFiniteSectionShift_eigen h q _ ε
      (fun i => toricNativeStrictPhiProductSections_complexTorus_eigen h q hq hw hwmem.2 i)

end SGPT.Toric

end
end ToricCanonicalFragment085
/- END SGPT.Toric.ToricDecreasingPhysicalStep -/

/- BEGIN SGPT.Toric.ToricNormalizedScalingInputs; source SHA256 0e8235446c2d4a7b5e63ed9db0cedebde774ab793671f4ac2aba5064fcfbacbb -/
section ToricCanonicalFragment086

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric
open Set Filter
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
open SGPT.Foundations.Analysis.FirstPass.NumericalRestrictedVolumeScaffold
open SGPT.PSH SGPT.PSH.VariableComplexAtlas
open scoped Topology
variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin n → ℤ} {hs : latticePolytopeEdgeSmooth γ}

/-- A literal finite constant normalizes the original singular potential
below minus one, preserving the SAME original toric strict class. -/
theorem exists_toricNativeStrict_normalized_input {D : ToricDivisor γ hs}
    (h : BigToricMetric D) {φ : PolytopeToricVariety γ hs → EReal}
    (hmem : φ ∈ h.PSHTor) (hstrict : IsKahlerCurrentPotential h.form φ) :
    ∃ (v : PolytopeToricVariety γ hs → EReal) (C : ℝ),
      v ∈ h.PSHTor ∧ IsKahlerCurrentPotential h.form v ∧
      (∀ p, v p ≤ (-1 : EReal)) ∧ ∀ p, φ p = v p + (C : EReal) := by
  obtain ⟨B, _, hB⟩ := SGPT.PSH.GlobalL2.exists_nonneg_upper_bound
    (toricNativePhi_globalQpsh (show (ofFixedModel n (PolytopeToricVariety γ hs)).IsQPSH φ from ⟨h.atlasForm, hmem.1⟩))
  let C := B + 1
  let v : PolytopeToricVariety γ hs → EReal := fun p => φ p + ((-C : ℝ) : EReal)
  refine ⟨v, C, BigToricMetric.mem_PSHTor_add_const h hmem (-C), ?_, ?_, ?_⟩
  · obtain ⟨omega, hp⟩ := hstrict
    exact ⟨omega, hp.add_const (-C)⟩
  · intro p
    have hh := add_le_add (hB p) (le_refl ((-C : ℝ) : EReal))
    have heq : ((B : EReal) + ((-C : ℝ) : EReal)) = (-1 : EReal) := by
      rw [← EReal.coe_add]
      norm_num [C]
    exact hh.trans heq.le
  · intro p
    dsimp only [v]
    rw [EReal.coe_neg, ← sub_eq_add_neg, EReal.sub_add_cancel]

/-- Explicit separated scaling coefficients stay in the internally
produced strict interval and increase to one. -/
theorem exists_strict_scaling_coefficients (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    ∃ c : ℕ → ℝ, (∀ j, 0 < c j ∧ 1 - ε ≤ c j ∧ c j < 1) ∧
      StrictMono c ∧ Tendsto c atTop (𝓝 1) := by
  let c : ℕ → ℝ := fun j => 1 - ε * (1 / 2 : ℝ) ^ (j + 1)
  refine ⟨c, ?_, strictMono_nat_of_lt_succ ?_, ?_⟩
  · intro j
    have hp : 0 < (1 / 2 : ℝ) ^ (j + 1) := pow_pos (by norm_num) _
    have hp1 : (1 / 2 : ℝ) ^ (j + 1) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    dsimp only [c]
    constructor
    · nlinarith
    constructor <;> nlinarith
  · intro j
    dsimp only [c]
    have hpow : (1 / 2 : ℝ) ^ (j + 1 + 1) = (1 / 2 : ℝ) ^ (j + 1) * (1 / 2) := pow_succ _ _
    rw [hpow]
    have hp : 0 < (1 / 2 : ℝ) ^ (j + 1) := pow_pos (by norm_num) _
    nlinarith
  · have ht := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
    have ht' := ht.comp (tendsto_add_atTop_nat 1)
    simpa only [c, mul_zero, sub_zero, Function.comp_def] using
      ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub
        ((tendsto_const_nhds : Tendsto (fun _ : ℕ => ε) atTop (𝓝 ε)).mul ht'))

/-- The normalized original input INTERNALLY supplies both a strict
scalar comparison and a uniform additive gap for the next recursion step. -/
theorem scaled_normalized_input_previous_comparison
    {X : Type*} {φ u : X → EReal} {c d : ℝ}
    (hc : 0 < c) (hcd : c < d) (hφ : ∀ p, φ p ≤ (-1 : EReal))
    (hlower : ∀ p, (c : EReal) * φ p ≤ u p) :
    1 < d / c ∧
      (∀ p, (d : EReal) * φ p ≤ ((d / c : ℝ) : EReal) * u p + (0 : EReal)) ∧
      ∀ p, (d : EReal) * φ p ≤ u p - ((d - c : ℝ) : EReal) := by
  have hd : 0 < d := hc.trans hcd
  have hr : 1 < d / c := (one_lt_div hc).mpr hcd
  refine ⟨hr, ?_, ?_⟩
  · intro p
    rw [add_zero]
    calc
      (d : EReal) * φ p = ((d / c : ℝ) : EReal) * ((c : EReal) * φ p) := by
        rw [← mul_assoc, ← EReal.coe_mul, div_mul_cancel₀ _ hc.ne']
      _ ≤ ((d / c : ℝ) : EReal) * u p :=
        monotone_eReal_const_mul (c := d / c) (le_of_lt (div_pos hd hc)) (hlower p)
  · intro p
    by_cases hp : φ p = ⊥
    · rw [hp, EReal.coe_mul_bot_of_pos hd]
      exact bot_le
    · have hminus : (-1 : EReal) ≠ ⊤ := by
        simpa only [EReal.coe_neg, EReal.coe_one] using EReal.coe_ne_top (-1 : ℝ)
      have htop : φ p ≠ ⊤ := ne_top_of_le_ne_top hminus (hφ p)
      have heq : φ p = ((φ p).toReal : EReal) := (EReal.coe_toReal htop hp).symm
      have hφR : (φ p).toReal ≤ -1 := by
        have hh := hφ p
        rw [heq] at hh
        exact EReal.coe_le_coe_iff.mp hh
      have hh : (d : EReal) * φ p ≤ (c : EReal) * φ p - ((d - c : ℝ) : EReal) := by
        rw [heq, ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_sub]
        apply EReal.coe_le_coe_iff.mpr
        nlinarith
      exact hh.trans (by
        rw [sub_eq_add_neg, sub_eq_add_neg]
        exact add_le_add (hlower p) le_rfl)

end SGPT.Toric

end
end ToricCanonicalFragment086
/- END SGPT.Toric.ToricNormalizedScalingInputs -/

/- BEGIN SGPT.Toric.ToricDecreasingPhysicalFamily; source SHA256 347f911c04fc9bbf27c254bfeb8f9ce746fc63203423601c0874645102ac1544 -/
section ToricCanonicalFragment087

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric
open Set Filter
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
open SGPT.Foundations.Analysis.FirstPass.NumericalRestrictedVolumeScaffold
open SGPT.PSH SGPT.PSH.VariableComplexAtlas
open scoped Topology BigOperators
variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin n → ℤ} {hs : latticePolytopeEdgeSmooth γ}

/-- Internal object carrier; all mathematical properties are proved in
this module, never supplied as a recursion or extraction certificate. -/
private structure PhysicalStage {D : ToricDivisor γ hs} (h : BigToricMetric D) where
  degree : ℕ
  degree_pos : 0 < degree
  size : ℕ
  sections : Fin size → ToricNativePlainPowerSections h degree
  shift : ℝ

private def PhysicalStage.potential {D : ToricDivisor γ hs} {h : BigToricMetric D}
    (s : PhysicalStage h) : PolytopeToricVariety γ hs → EReal :=
  toricNativeFiniteSectionPotential h s.degree s.sections

/-- Actual normalized original data produce a genuinely decreasing
physical family by successive global degree choices. The coefficients,
small scalar-section shifts, original degrees and sections are ALL chosen
internally. Moving-input convergence and separated ideals are assembled
in the next module. -/
theorem exists_toricNativeStrict_decreasingPhysical_normalized {D : ToricDivisor γ hs}
    (h : BigToricMetric D) {φ : PolytopeToricVariety γ hs → EReal}
    (hmem : φ ∈ h.PSHTor) (hstrict : IsKahlerCurrentPotential h.form φ)
    (hnegative : ∀ p, φ p ≤ (-1 : EReal)) :
    ∃ (c η : ℕ → ℝ)
      (hwmem : ∀ j, (fun p => (c j : EReal) * φ p) ∈ h.PSHTor)
      (Q : ℕ → ℕ) (hQpos : ∀ j, 0 < Q j)
      (U : ℕ → PolytopeToricVariety γ hs → EReal),
      (∀ j, 0 < c j ∧ c j < 1) ∧ StrictMono c ∧ Tendsto c atTop (𝓝 1) ∧
      (∀ j, IsKahlerCurrentPotential h.form (fun p => (c j : EReal) * φ p)) ∧
      (∀ j, 0 < η j ∧ η j ≤ 1 / ((j : ℝ) + 1)) ∧ StrictMono Q ∧
      (∀ j, U j ∈ h.PSHTor) ∧ (∀ j, IsKahlerCurrentPotential h.form (U j)) ∧
      (∀ p, Antitone fun j => U j p) ∧
      (∀ j p, (c j : EReal) * φ p ≤ U j p) ∧
      (∀ j, U j = fun p => toricNativeStrictPhiProductPotential h (Q j) (hQpos j)
        (show (ofFixedModel n (PolytopeToricVariety γ hs)).IsQPSH (fun x => (c j : EReal) * φ x)
          from ⟨h.atlasForm, (hwmem j).1⟩) (hwmem j).2 p + (η j : EReal)) ∧
      ∀ j, ∃ b : ℕ, ∃ s : Fin b → ToricNativePlainPowerSections h (Q j),
        U j = toricNativeFiniteSectionPotential h (Q j) s ∧
        ∀ i : Fin b, ∃ m : Fin n → ℤ, ∀ t : Fin n → ℂˣ,
          toricNativePlainSectionTranslation h (Q j) t (s i) = (latticeCharacter m t : ℂ) • s i := by
  classical
  obtain ⟨ε, hε, hε1, hscaled⟩ := exists_toricNative_sameTheta_strict_scaling_interval h hmem hstrict
  obtain ⟨c, hc, hcmono, hclim⟩ := exists_strict_scaling_coefficients ε hε hε1
  let w : ℕ → PolytopeToricVariety γ hs → EReal := fun j p => (c j : EReal) * φ p
  have hinput j := hscaled (c j) (hc j).2.1 (hc j).2.2.le
  have hwm : ∀ j, w j ∈ h.PSHTor := fun j => (hinput j).1
  have hwK : ∀ j, IsKahlerCurrentPotential h.form (w j) := fun j => (hinput j).2
  let hw : ∀ j, (ofFixedModel n (PolytopeToricVariety γ hs)).IsQPSH (w j) :=
    fun j => ⟨h.atlasForm, (hwm j).1⟩
  let P : ℕ → PhysicalStage h → Prop := fun j s =>
    0 < s.shift ∧ s.shift ≤ 1 / ((j : ℝ) + 1) ∧
    s.potential ∈ h.PSHTor ∧ IsKahlerCurrentPotential h.form s.potential ∧
    (∀ p, w j p ≤ s.potential p) ∧
    s.potential = (fun p => toricNativeStrictPhiProductPotential h s.degree s.degree_pos
      (hw j) (hwm j).2 p + (s.shift : EReal)) ∧
    ∀ i : Fin s.size, ∃ m : Fin n → ℤ, ∀ t : Fin n → ℂˣ,
      toricNativePlainSectionTranslation h s.degree t (s.sections i) = (latticeCharacter m t : ℂ) • s.sections i
  obtain ⟨N, hN, hbase⟩ := exists_toricNativeStrict_shifted_physical_properties h (hwm 0) (hwK 0) (1 / 2) (by norm_num)
  let a₀ := toricNativeFiniteSectionShift h N (toricNativeStrictPhiProductSections h N hN (hw 0) (hwm 0).2) (1 / 2)
  let s₀ : PhysicalStage h := ⟨N, hN, _, a₀, 1 / 2⟩
  obtain ⟨hbaselow, hbasemem, hbaseK⟩ := hbase N le_rfl hN
  have hP₀ : P 0 s₀ := by
    refine ⟨by norm_num [s₀], by norm_num [s₀], hbasemem, hbaseK, hbaselow, ?_, ?_⟩
    · exact toricNativeFiniteSectionShift_potential h N hN _ (1 / 2)
    · exact toricNativeFiniteSectionShift_eigen h N _ (1 / 2)
        (fun i => toricNativeStrictPhiProductSections_complexTorus_eigen h N hN (hw 0) (hwm 0).2 i)
  have hstep (j : ℕ) (s : {s : PhysicalStage h // P j s}) :
      ∃ t : {t : PhysicalStage h // P (j + 1) t},
        s.val.degree < t.val.degree ∧ ∀ p, t.val.potential p ≤ s.val.potential p := by
    let δ := c (j + 1) - c j
    have hδ : 0 < δ := sub_pos.mpr (hcmono (Nat.lt_succ_self j))
    let η := min (δ / 8) (1 / ((j : ℝ) + 2))
    have hη : 0 < η := lt_min (by positivity) (by positivity)
    have hηδ : η ≤ δ / 4 := (min_le_left _ _).trans (by linarith)
    have hs := s.property
    obtain ⟨hr, hcomp, hgap⟩ := scaled_normalized_input_previous_comparison
      (hc j).1 (hcmono (Nat.lt_succ_self j)) hnegative hs.2.2.2.2.1
    obtain ⟨q, hq, b, a, hqL, hlower, hmemq, hstrictq, hupper, heq, heigen⟩ :=
      exists_toricNativeStrict_decreasing_physical_step h s.val.degree s.val.degree_pos s.val.sections
        hs.2.2.1 (hwm (j + 1)) (hwK (j + 1)) hr hδ hη hηδ hcomp hgap (s.val.degree + 1)
    let t : PhysicalStage h := ⟨q, hq, b, a, η⟩
    have ht : P (j + 1) t := by
      refine ⟨hη, ?_, hmemq, hstrictq, hlower, heq, heigen⟩
      change η ≤ 1 / (((j + 1 : ℕ) : ℝ) + 1)
      simpa only [Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two] using
        (min_le_right (δ / 8) (1 / ((j : ℝ) + 2)))
    refine ⟨⟨t, ht⟩, by dsimp only [t]; omega, fun p => ?_⟩
    apply (hupper p).trans
    have hn : (0 : EReal) ≤ ((δ / 4 : ℝ) : EReal) := EReal.coe_nonneg.mpr (by positivity)
    calc
      s.val.potential p - ((δ / 4 : ℝ) : EReal) ≤ s.val.potential p - 0 := EReal.sub_le_sub le_rfl hn
      _ = s.val.potential p := sub_zero _
  let next := fun j s => Classical.choose (hstep j s)
  have hnext j s := Classical.choose_spec (hstep j s)
  let F : ∀ j, {s : PhysicalStage h // P j s} := Nat.rec ⟨s₀, hP₀⟩ next
  let Q : ℕ → ℕ := fun j => (F j).val.degree
  let η : ℕ → ℝ := fun j => (F j).val.shift
  let U : ℕ → PolytopeToricVariety γ hs → EReal := fun j => (F j).val.potential
  have hF j : P j (F j).val := (F j).property
  have hsucc j : (F j).val.degree < (F (j + 1)).val.degree ∧
      ∀ p, (F (j + 1)).val.potential p ≤ (F j).val.potential p := by
    exact hnext j (F j)
  refine ⟨c, η, hwm, Q, (fun j => (F j).val.degree_pos), U,
    (fun j => ⟨(hc j).1, (hc j).2.2⟩), hcmono, hclim, hwK,
    (fun j => ⟨(hF j).1, (hF j).2.1⟩), strictMono_nat_of_lt_succ (fun j => (hsucc j).1),
    (fun j => (hF j).2.2.1), (fun j => (hF j).2.2.2.1),
    (fun p => antitone_nat_of_succ_le (fun j => (hsucc j).2 p)),
    (fun j => (hF j).2.2.2.2.1), (fun j => (hF j).2.2.2.2.2.1), ?_⟩
  intro j
  exact ⟨(F j).val.size, (F j).val.sections, rfl, (hF j).2.2.2.2.2.2⟩

end SGPT.Toric

end
end ToricCanonicalFragment087
/- END SGPT.Toric.ToricDecreasingPhysicalFamily -/

/- BEGIN SGPT.Toric.ToricDecreasingPhysicalConvergence; source SHA256 d08074bb3d8aa0da86d4ce0528cd8f0e042dfb90daa0a61730f38847e2a618ec -/
section ToricCanonicalFragment088

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric
open Set Filter MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
open SGPT.Foundations.Analysis.FirstPass.NumericalRestrictedVolumeScaffold
open SGPT.Foundations.Analysis.FirstPass.QuasiEquisingularApproximation
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.IntegrationCurrent
open SGPT.PSH SGPT.PSH.VariableComplexAtlas
open scoped Topology BigOperators ENNReal
variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin n → ℤ} {hs : latticePolytopeEdgeSmooth γ}

private theorem multiplierIdealIncluded_unscale_target
    {X : Type*} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
    {u φ : X → EReal} {t c d : ℝ} (ht : 0 < t) (hc : 0 < c)
    (hI : MultiplierIdealIncluded (n := n) u d (fun x => (t : EReal) * φ x) (c / t)) :
    MultiplierIdealIncluded (n := n) u d φ c := by
  let : MeasurableSpace (ComplexModel n) := borel _
  let : BorelSpace (ComplexModel n) := ⟨rfl⟩
  intro e z hz f hf hmem
  obtain ⟨_, V, hV, hzV, hfV, hL2⟩ := hI e z hz f hf hmem
  have hdensity : multiplierDensity (chartFunction (fun x => (t : EReal) * φ x) e) (c / t) f =
      multiplierDensity (chartFunction φ e) c f := by
    funext y
    unfold multiplierDensity multiplierWeight chartFunction
    rw [← mul_assoc, ← EReal.coe_mul, div_mul_cancel₀ _ ht.ne']
  have hL2' : WeightedL2On (chartFunction φ e) c f V volume := by
    simpa only [WeightedL2On, hdensity] using hL2
  exact ⟨hc, V, hV, hzV, hfV, hL2'⟩

/-- Actual normalized original input produces the COMPLETE original QEA,
with genuine decreasing pointwise convergence, every separated pair and
actual same-theta strict toric finite original eigensection sums. No
approximation, convergence, strictness or extraction certificate is input. -/
theorem exists_toricNativeStrict_sourceQEA_normalized {D : ToricDivisor γ hs}
    (h : BigToricMetric D) {φ : PolytopeToricVariety γ hs → EReal}
    (hmem : φ ∈ h.PSHTor) (hstrict : IsKahlerCurrentPotential h.form φ)
    (hnegative : ∀ p, φ p ≤ (-1 : EReal)) :
    ∃ (Q : ℕ → ℕ) (_hQpos : ∀ j, 0 < Q j) (U : ℕ → PolytopeToricVariety γ hs → EReal),
      SourceQuasiEquisingularApproximation h.form φ U ∧ StrictMono Q ∧
      (∀ j, U j ∈ h.PSHTor) ∧ (∀ j, IsKahlerCurrentPotential h.form (U j)) ∧
      ∀ j, ∃ b : ℕ, ∃ s : Fin b → ToricNativePlainPowerSections h (Q j),
        U j = toricNativeFiniteSectionPotential h (Q j) s ∧
        ∀ i : Fin b, ∃ m : Fin n → ℤ, ∀ t : Fin n → ℂˣ,
          toricNativePlainSectionTranslation h (Q j) t (s i) = (latticeCharacter m t : ℂ) • s i := by
  obtain ⟨c, η, hwm, Q, hQpos, U, hc, hcmono, hclim, hwK, hη, hQmono, hUm, hUK,
    hanti, hlower, hEq, hsections⟩ := exists_toricNativeStrict_decreasingPhysical_normalized h hmem hstrict hnegative
  have hφ : (ofFixedModel n (PolytopeToricVariety γ hs)).IsQPSH φ := ⟨h.atlasForm, hmem.1⟩
  let hw : ∀ j, (ofFixedModel n (PolytopeToricVariety γ hs)).IsQPSH (fun p => (c j : EReal) * φ p) :=
    fun j => ⟨h.atlasForm, (hwm j).1⟩
  have hηlim : Tendsto η atTop (𝓝 0) := squeeze_zero
    (fun j => (hη j).1.le) (fun j => (hη j).2) tendsto_one_div_add_atTop_nhds_zero_nat
  have hηE : Tendsto (fun j => (η j : EReal)) atTop (𝓝 0) := by
    simpa only [EReal.coe_zero, Function.comp_def] using continuous_coe_real_ereal.continuousAt.tendsto.comp hηlim
  have hinputlim (p : PolytopeToricVariety γ hs) :
      Tendsto (fun j => (c j : EReal) * φ p) atTop (𝓝 (φ p)) := by
    by_cases hp : φ p = ⊥
    · have heq : (fun j => (c j : EReal) * φ p) = fun _ : ℕ => (⊥ : EReal) := by
        funext j
        rw [hp, EReal.coe_mul_bot_of_pos (hc j).1]
      rw [heq, hp]
      exact tendsto_const_nhds
    · have ht := continuous_coe_real_ereal.continuousAt.tendsto.comp (hclim.mul_const (φ p).toReal)
      simp only [Function.comp_def] at ht
      convert ht using 1
      · funext j
        rw [EReal.coe_mul, EReal.coe_toReal (hφ.ne_top p) hp]
      · rw [one_mul, EReal.coe_toReal (hφ.ne_top p) hp]
  have hinputanti (p : PolytopeToricVariety γ hs) : Antitone (fun j => (c j : EReal) * φ p) := by
    intro i j hij
    dsimp only
    by_cases hp : φ p = ⊥
    · rw [hp, EReal.coe_mul_bot_of_pos (hc j).1, EReal.coe_mul_bot_of_pos (hc i).1]
    · have heq := EReal.coe_toReal (hφ.ne_top p) hp
      have hpneg : (φ p).toReal ≤ -1 := by
        have hh := hnegative p
        rw [← heq] at hh
        exact EReal.coe_le_coe_iff.mp hh
      rw [← heq, ← EReal.coe_mul, ← EReal.coe_mul]
      apply EReal.coe_le_coe_iff.mpr
      have hh := hcmono.monotone hij
      nlinarith
  have hφU (j : ℕ) (p : PolytopeToricVariety γ hs) : φ p ≤ U j p := by
    have hφc : φ p ≤ (c j : EReal) * φ p :=
      le_of_tendsto (hinputlim p) ((eventually_ge_atTop j).mono (fun k hk => hinputanti p hk))
    exact hφc.trans (hlower j p)
  have hUlim (p : PolytopeToricVariety γ hs) :
      Tendsto (fun j => U j p) atTop (𝓝 (φ p)) := by
    have hlim := tendsto_atTop_iInf (hanti p)
    have hl : φ p ≤ ⨅ j, U j p := le_iInf (fun j => hφU j p)
    have hupper (N : ℕ) : (⨅ j, U j p) ≤ (c N : EReal) * φ p := by
      have hker := toricNativeStrictPhiProductPotential_tendsto_cofinal h (hw N) (hwm N).2 (hwK N)
        Q hQpos hQmono.tendsto_atTop p
      have hadd := (EReal.continuousAt_add
        (p := ((c N : EReal) * φ p, (0 : EReal)))
        (Or.inr (by simp)) (Or.inr (by simp))).tendsto.comp (hker.prodMk_nhds hηE)
      have hadd' : Tendsto (fun j => toricNativeStrictPhiProductPotential h (Q j) (hQpos j)
          (hw N) (hwm N).2 p + (η j : EReal)) atTop (𝓝 ((c N : EReal) * φ p)) := by
        simpa only [add_zero, Function.comp_def] using hadd
      apply le_of_tendsto_of_tendsto hlim hadd'
      filter_upwards [eventually_ge_atTop N] with j hj
      rw [hEq j]
      exact add_le_add
        (toricNativeStrictPhiProductPotential_mono_input h (Q j) (hQpos j)
          (hw j) (hw N) (hwm j).2 (hwm N).2 (fun x => hinputanti x hj) p) le_rfl
    have hu : (⨅ j, U j p) ≤ φ p :=
      le_of_tendsto_of_tendsto tendsto_const_nhds (hinputlim p) (Eventually.of_forall hupper)
    rwa [le_antisymm hu hl] at hlim
  have hI : ∀ a d : ℝ, 0 < a → a < d → ∃ j,
      MultiplierIdealIncluded (n := n) (U j) d φ a := by
    intro a d ha had
    have hd : 0 < d := ha.trans had
    let α := (a + d) / (2 * d)
    have hα : α < 1 := by dsimp only [α]; apply (div_lt_one (by positivity)).mpr; linarith
    have hc_event : ∀ᶠ j in atTop, α < c j := hclim.eventually (lt_mem_nhds hα)
    obtain ⟨m, hm⟩ := exists_nat_ge (2 * a * d / (d - a))
    have hQevent : ∀ᶠ j in atTop, m ≤ Q j := hQmono.tendsto_atTop.eventually (eventually_ge_atTop m)
    obtain ⟨j, hjc, hjQ⟩ := (hc_event.and hQevent).exists
    have hdc : (d - a) / 2 < d * c j - a := by
      have hh := (div_lt_iff₀ (show 0 < 2 * d by positivity)).mp hjc
      nlinarith
    have hqB : 2 * a * d / (d - a) ≤ (Q j : ℝ) := hm.trans (by exact_mod_cast hjQ)
    have hsep0 : a * d ≤ (Q j : ℝ) * (d * c j - a) := by
      have hh := (div_le_iff₀ (sub_pos.mpr had)).mp hqB
      have hprod := mul_le_mul_of_nonneg_left hdc.le (Nat.cast_nonneg (Q j))
      nlinarith [hprod]
    have hsep : (a / c j) * d ≤ (Q j : ℝ) * (d - a / c j) := by
      calc
        (a / c j) * d = (a * d) / c j := by ring
        _ ≤ ((Q j : ℝ) * (d * c j - a)) / c j :=
          (div_le_div_iff_of_pos_right (hc j).1).mpr hsep0
        _ = (Q j : ℝ) * (d - a / c j) := by field_simp [(hc j).1.ne']
    have hac : 0 < a / c j := div_pos ha (hc j).1
    have hacd : a / c j < d := (div_lt_iff₀ (hc j).1).mpr (by nlinarith)
    have hUmq : (ofFixedModel n (PolytopeToricVariety γ hs)).IsQPSH (U j) := ⟨h.atlasForm, (hUm j).1⟩
    have hmass : (∫⁻ p, EReal.exp (((Q j : ℝ) : EReal) * U j p) *
        multiplierWeight (Q j : ℝ) ((c j : EReal) * φ p)
        ∂(kahlerVolume (polytopeToricKahlerBackground γ hs))) < ⊤ := by
      rw [hEq j]
      exact toricNativeStrictPhiProductPotential_shifted_mass h (Q j) (hQpos j) (hw j) (hwm j).2 (η j)
    have hIj := multiplierIdealIncluded_of_finite_mixed_mass
      (KahlerVolumeSmoothPositive.isSmoothPositiveVolume_kahlerVolume (polytopeToricKahlerBackground γ hs))
      (toricNativePhi_globalQpsh (hw j)) (toricNativePhi_globalQpsh hUmq).1.upperSemicontinuous.measurable
      (hlower j) (Q j) (hQpos j) hmass hac hacd hsep
    exact ⟨j, multiplierIdealIncluded_unscale_target (hc j).1 ha hIj⟩
  refine ⟨Q, hQpos, U, ?_, hQmono, hUm, hUK, hsections⟩
  refine ⟨(isThetaPSH_iff_nativeThetaPotential h.atlasForm φ).mp hmem.1, ?_, ⟨hanti, hUlim⟩, ?_, hI⟩
  · intro j
    obtain ⟨b, s, heq, _⟩ := hsections j
    rw [heq]
    exact toricNativeFiniteSectionPotential_rationalAnalytic h (Q j) (hQpos j) s
  · refine ⟨polytopeToricKahlerBackground γ hs, fun _ => 0, ?_, ?_⟩
    · exact ⟨fun _ => le_rfl, antitone_const, tendsto_const_nhds⟩
    · intro j
      have hj : IsThetaPshPotential h.form.val (U j) :=
        (isThetaPSH_iff_nativeThetaPotential h.atlasForm (U j)).mp (hUm j).1
      simpa only [zero_smul, add_zero] using hj

end SGPT.Toric

end
end ToricCanonicalFragment088
/- END SGPT.Toric.ToricDecreasingPhysicalConvergence -/

/- BEGIN SGPT.Toric.ToricBergmanApproximation; source SHA256 a9fc94e77f22b6921721e9e57a9899efd7770315acc39e776665a473b752a821 -/
section ToricCanonicalFragment089

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric
open Set Filter MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
open SGPT.Foundations.Analysis.FirstPass.NumericalRestrictedVolumeScaffold
open SGPT.Foundations.Analysis.FirstPass.QuasiEquisingularApproximation
open SGPT.Foundations.Analysis.Pending.QuasiEquisingularComparison
open SGPT.PSH SGPT.PSH.VariableComplexAtlas
open scoped Topology BigOperators ENNReal
variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin n → ℤ} {hs : latticePolytopeEdgeSmooth γ}

private theorem sourceQEA_translate {X : Type*} [TopologicalSpace X]
    [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
    {θ : ClosedRealOneOneForm n X} {v : X → EReal} {U : ℕ → X → EReal}
    (h : SourceQuasiEquisingularApproximation θ v U) (C : ℝ) :
    SourceQuasiEquisingularApproximation θ (fun p => v p + (C : EReal))
      (fun j p => U j p + (C : EReal)) := by
  obtain ⟨hv, han, ⟨hanti, hlim⟩, ⟨omega, ε, hε, hθ⟩, hI⟩ := h
  refine ⟨hv.add_const C, (fun j => hasManifoldAnalyticSingularityType_add_const (han j) C),
    ⟨(fun p i j hij => add_le_add (hanti p hij) le_rfl), ?_⟩,
    ⟨omega, ε, hε, fun j => (hθ j).add_const C⟩, ?_⟩
  · intro p
    exact (EReal.continuousAt_add (p := (v p, (C : EReal)))
      (Or.inr (EReal.coe_ne_bot C)) (Or.inr (EReal.coe_ne_top C))).tendsto.comp
      ((hlim p).prodMk_nhds tendsto_const_nhds)
  · intro c d hc hcd
    obtain ⟨j, hj⟩ := hI c d hc hcd
    refine ⟨j, ?_⟩
    intro e z hz f hf hmem
    let : MeasurableSpace (ComplexModel n) := borel _
    let : BorelSpace (ComplexModel n) := ⟨rfl⟩
    have hmem' := (multiplierIntegrableAt_chartFunction_add_const_iff C e d f z volume).mp hmem
    exact (multiplierIntegrableAt_chartFunction_add_const_iff C e c f z volume).mpr (hj e z hz f hf hmem')

/-- SGPT `lma:toricBergmanapprox`, with a stronger EXACT physical finite
original H0(L^q) formula. The whole pointwise decreasing QEA, same-theta
toric Kähler currents, original positive cofinal degrees and whole complex
torus eigensections are INTERNALLY PRODUCED from ONLY the original input.
The original singular potential has no analytic-type hypothesis. -/
theorem exists_toricNativeStrict_Bergman_quasiEquisingular {D : ToricDivisor γ hs}
    (h : BigToricMetric D) {φ : PolytopeToricVariety γ hs → EReal}
    (hmem : φ ∈ h.PSHTor) (hstrict : IsKahlerCurrentPotential h.form φ) :
    ∃ (Q : ℕ → ℕ) (_hQpos : ∀ j, 0 < Q j) (U : ℕ → PolytopeToricVariety γ hs → EReal),
      SourceQuasiEquisingularApproximation h.form φ U ∧ StrictMono Q ∧
      (∀ j, U j ∈ h.PSHTor) ∧ (∀ j, IsKahlerCurrentPotential h.form (U j)) ∧
      ∀ j, ∃ b : ℕ, ∃ s : Fin b → ToricNativePlainPowerSections h (Q j),
        U j = toricNativeFiniteSectionPotential h (Q j) s ∧
        ∀ i : Fin b, ∃ m : Fin n → ℤ, ∀ t : Fin n → ℂˣ,
          toricNativePlainSectionTranslation h (Q j) t (s i) = (latticeCharacter m t : ℂ) • s i := by
  obtain ⟨v, C, hvmem, hvstrict, hvnegative, hφeq⟩ := exists_toricNativeStrict_normalized_input h hmem hstrict
  obtain ⟨Q, hQpos, U, hQEA, hQmono, hUm, hUK, hsections⟩ :=
    exists_toricNativeStrict_sourceQEA_normalized h hvmem hvstrict hvnegative
  let V : ℕ → PolytopeToricVariety γ hs → EReal := fun j p => U j p + (C : EReal)
  have hfun : (fun p => v p + (C : EReal)) = φ := funext (fun p => (hφeq p).symm)
  refine ⟨Q, hQpos, V, ?_, hQmono, ?_, ?_, ?_⟩
  · have hh := sourceQEA_translate hQEA C
    rwa [hfun] at hh
  · exact fun j => BigToricMetric.mem_PSHTor_add_const h (hUm j) C
  · intro j
    obtain ⟨omega, hp⟩ := hUK j
    exact ⟨omega, hp.add_const C⟩
  · intro j
    obtain ⟨b, s, heq, heigen⟩ := hsections j
    refine ⟨b, toricNativeFiniteSectionShift h (Q j) s C, ?_,
      toricNativeFiniteSectionShift_eigen h (Q j) s C heigen⟩
    dsimp only [V]
    rw [heq, toricNativeFiniteSectionShift_potential h (Q j) (hQpos j)]

end SGPT.Toric

end
end ToricCanonicalFragment089
/- END SGPT.Toric.ToricBergmanApproximation -/
