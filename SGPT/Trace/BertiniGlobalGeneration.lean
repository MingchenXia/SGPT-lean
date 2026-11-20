import SGPT.Trace.ProductMultiplierRestriction
import SGPT.NAPotential.SiuGenMain
import SGPT.Bergman.SourceNativeDegreeChern
import SGPT.Foundations.Analysis.Pending.KahlerDomination
import SGPT.Bergman.SiuUniformGenerationMain
import SGPT.Bergman.SiuKodairaNativeSection

/-!
# Native global generation after constant-product restriction

The actual all-frame section/stalk meaning of the global-generation clause E5'
in `thm:Bert`. The proof plan is
`work/sgpt-resume-20261114/bert-e5/blueprint/bert-e5-global-generation.tex`.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.Trace.BertiniGlobalGeneration

open Set Filter Bundle
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.ChartwiseGlobalL1
open scoped ProductComplexManifold
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.PolynomialH0Growth
open SGPT.PSH.GlobalL2
open HermitianHolomorphicLineBundle
open SGPT.PSH.LineBundleMetric SGPT.PSH.SiuL2 SGPT.NAPotential.NAGaga
open SGPT.NAPotential.SiuGen SGPT.Trace.ProductMultiplierRestriction

variable {n : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X]

/-- Actual global holomorphic sections whose coefficients in every native
atlas frame belong to the specified ideal at every point of its frame domain. -/
def IsBaseSectionIn (E : HermitianHolomorphicLineBundle.{0, 0} n X) (𝓘 : GermIdeal n X)
    (s : (x : X) → E.Fiber x) : Prop :=
  IsHolomorphicSectionOn (n := n) E.Fiber s univ ∧
    ∀ (x : X) (e : AtlasFrame E), x ∈ e.val.baseSet →
      𝓘.mem x (fun z => e.val.continuousLinearMapAt ℂ z (s z))

/-- Generation of the entire native ideal stalk, in every atlas frame, by
coefficients of actual global ideal-valued holomorphic bundle sections. -/
def IsBaseGloballyGenerated (E : HermitianHolomorphicLineBundle.{0, 0} n X)
    (𝓘 : GermIdeal n X) : Prop :=
  ∀ (x : X) (e : AtlasFrame E), x ∈ e.val.baseSet →
    ∀ g : X → ℂ, 𝓘.mem x g →
      IsInSpanAt (n := n) (fun h => ∃ s : (x : X) → E.Fiber x,
        IsBaseSectionIn E 𝓘 s ∧ h = fun z => e.val.continuousLinearMapAt ℂ z (s z)) x g

/-- Native product holomorphy gives native bundle holomorphy on a constant slice. -/
theorem isHolomorphicSectionOn_restrict
    (E : HermitianHolomorphicLineBundle.{0, 0} n X)
    {S : (q : X × unitDisc) → E.Fiber q.1}
    (hS : IsHolomorphicProdSectionOn E S univ) (t : unitDisc) :
    IsHolomorphicSectionOn (n := n) E.Fiber (fun x => S (x, t)) univ := by
  have hi : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel (n + 1)) ∞
      (fun z : X => (z, t)) :=
    ProductComplexManifold.contMDiff_prodMk contMDiff_id contMDiff_const
  intro x _
  let e : AtlasFrame E := ⟨trivializationAt ℂ E.Fiber x, inferInstance⟩
  let := e.property
  have hx : x ∈ e.val.baseSet := mem_baseSet_trivializationAt ℂ E.Fiber x
  have hcoef : HolomorphicAt n (fun z => e.val.continuousLinearMapAt ℂ z (S (z, t))) x :=
    (hS (x, t) (mem_univ _) e hx).comp_contMDiff (f := fun z : X => (z, t))
      (Eventually.of_forall fun _ => hi.contMDiffAt)
  apply ((e.val.mdifferentiableAt_section_iff (IB := 𝓘(ℂ, ComplexModel n))
    (fun z => S (z, t)) hx).mpr ?_).mdifferentiableWithinAt
  apply hcoef.self_of_nhds.congr_of_eventuallyEq
  filter_upwards [e.val.open_baseSet.mem_nhds hx] with z hz
  exact (Trivialization.continuousLinearMapAt_apply_of_mem (R := ℂ) e.val hz _).symm

/-- A genuine global product section in the constant multiplier ideal restricts
with both its holomorphy and its entire ideal membership retained. -/
theorem isBaseSectionIn_restrict (E : HermitianHolomorphicLineBundle.{0, 0} n X)
    {φ : X → EReal} (hφ : ManifoldQuasiPlurisubharmonic (n := n) φ)
    {c : ℝ} (hc : 0 < c) {S : (q : X × unitDisc) → E.Fiber q.1}
    (hS : IsProdSectionIn E (multiplierIdeal (n := n + 1) c (fun q : X × unitDisc => φ q.1)) S)
    (t : unitDisc) :
    IsBaseSectionIn E (multiplierIdeal (n := n) c φ) (fun x => S (x, t)) := by
  refine ⟨isHolomorphicSectionOn_restrict E hS.1 t, fun x e hx => ?_⟩
  exact multiplierIdeal_mem_restrict hφ hc t (hS.2 (x, t) e hx)

/-- Restrict the actual global product generators to obtain actual base generators. -/
theorem isBaseGloballyGenerated_of_prod
    (E : HermitianHolomorphicLineBundle.{0, 0} n X) {φ : X → EReal}
    (hφ : ManifoldQuasiPlurisubharmonic (n := n) φ) {c : ℝ} (hc : 0 < c)
    (hgen : IsProdGloballyGenerated E
      (multiplierIdeal (n := n + 1) c (fun q : X × unitDisc => φ q.1))) :
    IsBaseGloballyGenerated E (multiplierIdeal (n := n) c φ) := by
  intro x e hx g hg
  have hi : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel (n + 1)) ∞
      (fun z : X => (z, discOrigin)) :=
    ProductComplexManifold.contMDiff_prodMk contMDiff_id contMDiff_const
  apply SGPT.PSH.MultiplierPullback.isInSpanAt_comp (h := fun z : X => (z, discOrigin))
    rfl (Eventually.of_forall fun _ => hi.contMDiffAt) ?_
    (hgen (x, discOrigin) e hx (fun q => g q.1) (multiplierIdeal_mem_comp_fst hφ discOrigin hg))
  rintro h ⟨S, hS, rfl⟩
  exact ⟨fun z => e.val.continuousLinearMapAt ℂ z (S (z, discOrigin)),
    ⟨fun z => S (z, discOrigin), isBaseSectionIn_restrict E hφ hc hS discOrigin, rfl⟩,
    EventuallyEq.refl _ _⟩

/-- Fixed-line-bundle Siu generation on the base, with the original native
bundle powers, all ideal germs, and an exponent independent of the weight. -/
theorem siuGlobalGeneration_base_of_le [CompactSpace X]
    (G : HermitianHolomorphicLineBundle.{0, 0} n X) (hG : IsSourceSmoothHermitianMetric G)
    (θG : ClosedRealOneOneForm n X) (hθG : IsOwnFirstChernForm G θG) (hKah : θG.val.IsKahler)
    (L : HermitianHolomorphicLineBundle.{0, 0} n X) (hL : IsSourceSmoothHermitianMetric L)
    (θ : ClosedRealOneOneForm n X) (hθ : IsOwnFirstChernForm L θ) :
    ∃ k₀ : ℕ, 0 < k₀ ∧ ∀ k : ℕ, k₀ ≤ k →
    ∀ φ : X → EReal, IsThetaPshPotential θ.val φ →
    ∀ m : ℕ, 0 < m →
      IsBaseGloballyGenerated (twistedPower L (positivePower G (k - 1)) m)
        (multiplierIdeal (n := n) (m : ℝ) φ) := by
  obtain ⟨k₀, hk₀, hgen⟩ := siuGlobalGeneration_prod_of_le G hG θG hθG hKah L hL θ hθ
  refine ⟨k₀, hk₀, fun k hk φ hφ m hm => ?_⟩
  exact isBaseGloballyGenerated_of_prod _ hφ.1.quasiPlurisubharmonic (by positivity)
    (hgen k hk (fun q => φ q.1) (isThetaPshPotential_comp_fst θ hφ) m hm)

/-- Compact Kähler geometry produces an integer twist that dominates the
fixed difference of two smooth curvatures, uniformly at every larger degree. -/
theorem exists_nat_curvature_domination [CompactSpace X]
    (θ θE θG : ClosedRealOneOneForm n X) (hKah : θG.val.IsKahler) :
    ∃ b : ℕ, 0 < b ∧ ∀ a : ℕ, b ≤ a →
      (θE + (a : ℝ) • θG - θ).val.IsSemipositive := by
  let omega : KahlerBackground n X := ⟨θG, hKah⟩
  obtain ⟨A, hA, hsemi⟩ :=
    KahlerDomination.exists_pos_isSemipositive_add_smul omega (θE - θ)
  obtain ⟨b, hb⟩ := exists_nat_gt A
  have hbpos : 0 < b := by exact_mod_cast hA.trans hb
  refine ⟨b, hbpos, fun a hba => ?_⟩
  have hAa : A ≤ (a : ℝ) := hb.le.trans (by exact_mod_cast hba)
  have h := KahlerDomination.isSemipositive_add_smul_mono omega.isSemipositive hAa hsemi
  have heq : (θE - θ) + (a : ℝ) • θG = θE + (a : ℝ) • θG - θ := by module
  rwa [heq] at h

/-- The integer curvature shift is chosen before every original theta-psh
weight and produces its genuine enlarged background. -/
theorem exists_nat_twisted_background [CompactSpace X]
    (θ θE θG : ClosedRealOneOneForm n X) (hKah : θG.val.IsKahler) :
    ∃ b : ℕ, 0 < b ∧ ∀ a : ℕ, b ≤ a →
      ∀ φ : X → EReal, IsThetaPshPotential θ.val φ →
        IsThetaPshPotential (θE + (a : ℝ) • θG).val φ := by
  obtain ⟨b, hb, hdom⟩ := exists_nat_curvature_domination θ θE θG hKah
  refine ⟨b, hb, fun a ha φ hφ => ?_⟩
  have h := LocalPotentials.isThetaPshPotential_add_of_semipositive hφ (hdom a ha)
  have heq : θ + (θE + (a : ℝ) • θG - θ) = θE + (a : ℝ) • θG := by module
  rwa [heq] at h

open SGPT.Bergman.NativeHermitianMetric SGPT.Bergman.SiuUniformGeneration

/-- Every sufficiently high literal twist of an arbitrary fixed bundle
is globally generated with the entire original multiplier ideal. The
threshold precedes every weight with the fixed original background. -/
theorem eventually_twistedMultiplier_globallyGenerated [CompactSpace X]
    (G E : HermitianHolomorphicLineBundle.{0, 0} n X)
    (hG : IsSourceSmoothHermitianMetric G) (hE : IsSourceSmoothHermitianMetric E)
    (hKah : (sourceNativeFirstChernForm G hG).val.IsKahler)
    (θ : ClosedRealOneOneForm n X) :
    ∃ a₀ : ℕ, 0 < a₀ ∧ ∀ a : ℕ, a₀ ≤ a →
      ∀ φ : X → EReal, IsThetaPshPotential θ.val φ →
        IsBaseGloballyGenerated (twistedPower G E a) (multiplierIdeal (n := n) 1 φ) := by
  let _ : MeasurableSpace X := borel X
  have _ : BorelSpace X := ⟨rfl⟩
  let θG := sourceNativeFirstChernForm G hG
  let θE := sourceNativeFirstChernForm E hE
  let omega : KahlerBackground n X := ⟨θG, hKah⟩
  have hμ := KahlerVolumeSmoothPositive.isSmoothPositiveVolume_kahlerVolume omega
  have hOwnG := sourceNativeFirstChernForm_isOwn G hG
  let D := fixedGeometry hμ G hG θG hOwnG hKah
  obtain ⟨B, hB0, hBa⟩ := D.exists_uniform_siuPoleB hKah
  let K := exponent D (((n : ℝ) + 3) * B)
  have hKpos : 0 < K := exponent_pos D _
  have hGood := goodPower_exponent D (((n : ℝ) + 3) * B) (K := K) le_rfl
  obtain ⟨b, hb, hbg⟩ := exists_nat_twisted_background θ θE θG hKah
  refine ⟨b + K, by omega, fun a ha φ hφ => ?_⟩
  have haK : K ≤ a := by omega
  have hab : b ≤ a - K := by omega
  have hφ' := hbg (a - K) hab φ hφ
  have hΦ := isThetaPshPotential_comp_fst (m := 1) (Y := unitDisc)
    (θE + ((a - K : ℕ) : ℝ) • θG) hφ'
  have hTarget := sourceNativeTwistedPower_smooth G E hG hE a
  have hOwn := sourceNativeTwistedPower_isOwn G E hG hE a
  have hform : (a : ℝ) • θG + θE =
      ((1 : ℕ) : ℝ) • (θE + ((a - K : ℕ) : ℝ) • θG) + (K : ℝ) • θG := by
    rw [Nat.cast_sub haK, Nat.cast_one]
    module
  change IsOwnFirstChernForm (twistedPower G E a) ((a : ℝ) • θG + θE) at hOwn
  rw [hform] at hOwn
  have hcorr := hasProdCorrection_fixedCover D hG hTarget hOwnG hGood
    (by norm_num : 0 < (1 : ℕ)) hOwn hΦ
  have hprod := isProdGloballyGenerated_of_fixedCover_correction hμ D hKah hB0 hBa
    (by norm_num : 0 < (1 : ℕ)) hΦ hcorr
  apply isBaseGloballyGenerated_of_prod _ hφ.1.quasiPlurisubharmonic one_pos
  simpa only [Nat.cast_one] using hprod

open SGPT.Bergman.QuantizationDraft SGPT.Bergman.CompactHolomorphicSectionsDraft

/-- The entire native multiplier-valued H0 is an actual complex submodule
of all global holomorphic sections on the original fibres. -/
def multiplierSectionSubmodule (E : HermitianHolomorphicLineBundle.{0, 0} n X)
    {φ : X → EReal} (hφ : ManifoldQuasiPlurisubharmonic (n := n) φ)
    {c : ℝ} (hc : 0 < c) : Submodule ℂ (HolomorphicSections (n := n) E.Fiber) where
  carrier := {s | ∀ (x : X) (e : AtlasFrame E), x ∈ e.val.baseSet →
    (multiplierIdeal (n := n) c φ).mem x
      (fun z => e.val.continuousLinearMapAt ℂ z (s z))}
  zero_mem' := by
    intro x e _
    change (multiplierIdeal (n := n) c φ).mem x
      (fun z => e.val.continuousLinearMapAt ℂ z (0 : E.Fiber z))
    simpa only [map_zero] using
      (show (multiplierIdeal (n := n) c φ).mem x (fun _ => 0) from
        ⟨holomorphicAt_const 0, multiplierIntegrableAt_zero _ hc _ MeasureTheory.volume⟩)
  add_mem' := by
    intro s t hs ht x e hx
    have h1 := hs x e hx
    have h2 := ht x e hx
    have hz := (complexChartAt (n := n) x).val.map_source (mem_complexChartAt_source x)
    have hq := hφ (complexChartAt (n := n) x) _ hz
    change (multiplierIdeal (n := n) c φ).mem x
      (fun z => e.val.continuousLinearMapAt ℂ z (s z + t z))
    simpa only [map_add] using
      (show (multiplierIdeal (n := n) c φ).mem x
        (fun z => e.val.continuousLinearMapAt ℂ z (s z) +
          e.val.continuousLinearMapAt ℂ z (t z)) from
        ⟨h1.1.add h2.1, multiplierIntegrableAt_add hq h1.2 h2.2⟩)
  smul_mem' := by
    intro r s hs x e hx
    change (multiplierIdeal (n := n) c φ).mem x
      (fun z => e.val.continuousLinearMapAt ℂ z (r • s z))
    simpa only [map_smul, smul_eq_mul] using
      (MultiplierIdealProductComparison.mem_multiplierIdeal_holomorphic_mul
        (holomorphicAt_const r) (hs x e hx))

/-- Membership tests every native atlas frame and is precisely the section
predicate used by the global-generation theorem. -/
theorem mem_multiplierSectionSubmodule_iff
    (E : HermitianHolomorphicLineBundle.{0, 0} n X) {φ : X → EReal}
    (hφ : ManifoldQuasiPlurisubharmonic (n := n) φ) {c : ℝ} (hc : 0 < c)
    (s : HolomorphicSections (n := n) E.Fiber) :
    s ∈ multiplierSectionSubmodule E hφ hc ↔
      IsBaseSectionIn E (multiplierIdeal (n := n) c φ) s :=
  ⟨fun hs => ⟨s.mdifferentiable.mdifferentiableOn, hs⟩, fun hs => hs.2⟩

/-- Compactness gives a finite family of actual global multiplier-valued
sections generating all entire stalks simultaneously. No finite-family or
H0-dimension certificate is assumed. -/
theorem exists_finite_global_generators [CompactSpace X]
    (E : HermitianHolomorphicLineBundle.{0, 0} n X) {φ : X → EReal}
    (hφ : ManifoldQuasiPlurisubharmonic (n := n) φ) {c : ℝ} (hc : 0 < c)
    (hgen : IsBaseGloballyGenerated E (multiplierIdeal (n := n) c φ)) :
    ∃ (N : ℕ) (s : Fin N → HolomorphicSections (n := n) E.Fiber),
      (∀ j, IsBaseSectionIn E (multiplierIdeal (n := n) c φ) (s j)) ∧
      ∀ (x : X) (e : AtlasFrame E), x ∈ e.val.baseSet →
        ∀ g : X → ℂ, (multiplierIdeal (n := n) c φ).mem x g →
          IsInSpanAt (n := n)
            (fun h => ∃ j, h = fun z => e.val.continuousLinearMapAt ℂ z (s j z)) x g := by
  classical
  let H := multiplierSectionSubmodule E hφ hc
  let _ := holomorphicSections_finiteDimensional (n := n) E.Fiber
  let _ : FiniteDimensional ℂ H := inferInstance
  let b := Module.finBasis ℂ H
  refine ⟨Module.finrank ℂ H, fun j => (b j).val, fun j => ?_, fun x e hx g hg => ?_⟩
  · exact (mem_multiplierSectionSubmodule_iff E hφ hc (b j).val).mp (b j).property
  · apply RelativePrincipalizationSpan.IsInSpanAt.trans ?_ (hgen x e hx g hg)
    rintro h ⟨s, hs, rfl⟩
    let v : H := ⟨SGPT.Bergman.SiuKodaira.nativeSectionOfHolomorphic E s hs.1, hs.2⟩
    refine ⟨(hs.2 x e hx).1, Module.finrank ℂ H,
      (fun j z => e.val.continuousLinearMapAt ℂ z ((b j).val z)),
      (fun j _ => b.repr v j), (fun j => ⟨j, rfl⟩),
      (fun j => holomorphicAt_const (b.repr v j)), Eventually.of_forall ?_⟩
    intro z
    let ev : H →ₗ[ℂ] ℂ := {
      toFun := fun w => e.val.continuousLinearMapAt ℂ z (w.val z)
      map_add' := by
        intro u v
        change e.val.continuousLinearMapAt ℂ z (u.val z + v.val z) = _
        exact map_add _ _ _
      map_smul' := by
        intro r u
        change e.val.continuousLinearMapAt ℂ z (r • u.val z) = _
        exact map_smul _ _ _ }
    change ev v = ∑ j, b.repr v j * ev (b j)
    simpa only [map_sum, map_smul, smul_eq_mul] using (congrArg ev (b.sum_repr v)).symm


/-- The global-generation and finiteness clause E5' for any fixed target
bundle and fixed theta-psh background, with one threshold before the weights.
Every displayed section is an actual section on the original tensor fibres. -/
theorem eventually_twistedMultiplier_finite_global_generators [CompactSpace X]
    (G E : HermitianHolomorphicLineBundle.{0, 0} n X)
    (hG : IsSourceSmoothHermitianMetric G) (hE : IsSourceSmoothHermitianMetric E)
    (hKah : (sourceNativeFirstChernForm G hG).val.IsKahler)
    (θ : ClosedRealOneOneForm n X) :
    ∃ a₀ : ℕ, 0 < a₀ ∧ ∀ a : ℕ, a₀ ≤ a →
      ∀ φ : X → EReal, IsThetaPshPotential θ.val φ →
        ∃ (N : ℕ) (s : Fin N → HolomorphicSections (n := n) (twistedPower G E a).Fiber),
          (∀ j, IsBaseSectionIn (twistedPower G E a) (multiplierIdeal (n := n) 1 φ) (s j)) ∧
          ∀ (x : X) (e : AtlasFrame (twistedPower G E a)), x ∈ e.val.baseSet →
            ∀ g : X → ℂ, (multiplierIdeal (n := n) 1 φ).mem x g →
              IsInSpanAt (n := n)
                (fun h => ∃ j, h = fun z => e.val.continuousLinearMapAt ℂ z (s j z)) x g := by
  obtain ⟨a₀, ha₀, hgen⟩ := eventually_twistedMultiplier_globallyGenerated G E hG hE hKah θ
  exact ⟨a₀, ha₀, fun a ha φ hφ => exists_finite_global_generators (twistedPower G E a)
    hφ.1.quasiPlurisubharmonic one_pos (hgen a ha φ hφ)⟩

end SGPT.Trace.BertiniGlobalGeneration
