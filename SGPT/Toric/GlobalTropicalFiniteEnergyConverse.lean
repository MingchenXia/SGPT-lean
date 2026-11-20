import SGPT.Toric.GlobalTropicalLegendreEnergy
import SGPT.Toric.TropicalBoundaryDivisorPole
import SGPT.Okounkov.LegendreEnergyEquality
import SGPT.Foundations.Analysis.Pending.SingularModelUniformTruncationFullMass

set_option autoImplicit false
noncomputable section

/-!
# Actual native finite energy from original convex finite energy

The actual canonical native truncations and their convex profiles are manufactured
from the original potential. Finite Cartier boundary geometry internally produces
an independent pole function. The accepted finite-energy Legendre identity is used
only on the internally constructed same-type truncations and reference; the original
potential is not assumed to have full mass or native finite energy.
-/

namespace SGPT.Toric

open Set Filter MeasureTheory SGPT.Convex
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending
open RelativeEnergy RelativeDarvasDistance RelativePreceqClasses
open MongeAmpereEnergyDecreasing SingularModelEnergyTruncation SingularModelEnergyCocycle
open scoped Topology ENNReal RealInnerProductSpace

/-- The same actual original convex max profile, manufactured for every native truncation. -/
def convexCanonicalTruncation {n : ℕ}
    (f₀ f : RealConvexFunction (EuclideanSpace ℝ (Fin n))) (j : ℕ) :
    RealConvexFunction (EuclideanSpace ℝ (Fin n)) :=
  ⟨fun x => max (f.val x) (f₀.val x - j), by
    refine ⟨convex_univ, fun x hx y hy a b ha hb hab => max_le ?_ ?_⟩
    · exact (f.property.2 hx hy ha hb hab).trans (add_le_add
        (mul_le_mul_of_nonneg_left (le_max_left _ _) ha)
        (mul_le_mul_of_nonneg_left (le_max_left _ _) hb))
    · have h := (f₀.property.add_const (-(j : ℝ))).2 hx hy ha hb hab
      simp only [Pi.add_apply, sub_eq_add_neg] at h ⊢
      exact h.trans (add_le_add
        (mul_le_mul_of_nonneg_left (le_max_right _ _) ha)
        (mul_le_mul_of_nonneg_left (le_max_right _ _) hb))⟩

/-- The actual pointwise max order reverses under the original conjugate, retaining top values. -/
theorem conjugate_convexCanonicalTruncation_le {n : ℕ}
    (f₀ f : RealConvexFunction (EuclideanSpace ℝ (Fin n))) (j : ℕ) :
    conjugate (innerₗ (EuclideanSpace ℝ (Fin n)))
      (fun a => ((convexCanonicalTruncation f₀ f j).val a : EReal)) ≤
    conjugate (innerₗ (EuclideanSpace ℝ (Fin n))) (fun a => (f.val a : EReal)) :=
  conjugate_antitone _ (fun _a => EReal.coe_le_coe_iff.mpr (le_max_left _ _))

private theorem finite_correction_sub_comm (a : EReal) (c d : ℝ) :
    (a - (c : EReal)) + (d : EReal) = (a + (d : EReal)) - (c : EReal) := by
  simpa only [sub_eq_add_neg] using add_right_comm a (-(c : EReal)) (d : EReal)

section NativeTruncation

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {θ : ClosedRealOneOneForm n M} {φ u : M → EReal} {r : ComplexModel n → ℝ}

omit [IsComplexManifold n M] in
/-- Original corrected chart identities manufacture the entire native truncation profile. -/
theorem corrected_profile_convexCanonicalTruncation
    (e : ComplexChart n M)
    (f₀ f : RealConvexFunction (EuclideanSpace ℝ (Fin n)))
    (h₀ : EqOn (fun z => chartFunction φ e z + (r z : EReal))
      (fun z => (f₀.val (tropicalization z) : EReal)) (tropicalSmoothDomain n))
    (hf : EqOn (fun z => chartFunction u e z + (r z : EReal))
      (fun z => (f.val (tropicalization z) : EReal)) (tropicalSmoothDomain n)) (j : ℕ) :
    EqOn (fun z => chartFunction (truncation φ u j) e z + (r z : EReal))
      (fun z => ((convexCanonicalTruncation f₀ f j).val (tropicalization z) : EReal))
      (tropicalSmoothDomain n) := by
  intro z hz
  have huChart : chartFunction u e z + (r z : EReal) =
      (f.val (tropicalization z) : EReal) := hf hz
  have hφChart : chartFunction φ e z + (r z : EReal) =
      (f₀.val (tropicalization z) : EReal) := h₀ hz
  change max (chartFunction u e z) (chartFunction φ e z - ((j : ℝ) : EReal)) +
    (r z : EReal) = _
  rw [← max_add_coe, finite_correction_sub_comm, huChart, hφChart, ← EReal.coe_sub]
  exact (Monotone.map_max EReal.coe_strictMono.monotone).symm

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M]
  {hφ : IsModelPotential θ φ}

/-- Internally produced same-type truncations have actual full mass and a finite own-gap integral. -/
theorem nativeFiniteEnergy_canonicalTruncation (omega : KahlerBackground n M)
    (hu : IsThetaPshPotential θ.val u) (hule : u ≤ φ) (j : ℕ) :
    RelativeFiniteEnergy θ φ (truncation φ u j) hφ := by
  let horder : MoreSingularOn u φ univ := MoreSingularOn.of_le fun x _ => hule x
  let ht := relativeEInfinity_truncation hφ.plurisubharmonic hu horder j
  have hfull : RelativeFullMass θ φ (truncation φ u j) hφ := by
    refine ⟨ht.1, FiniteEnergyCharacterization.truncation_le hule j, ?_⟩
    change DiagonalMass.diagonalPotentialMeasure θ (truncation φ u j) ht.1 univ =
      DiagonalMass.diagonalPotentialMass θ φ hφ.plurisubharmonic
    exact SingularModelEnergyTruncationGap.diagonalPotentialMeasure_truncation_univ
      omega θ hφ.plurisubharmonic hu horder j
  exact relativeFiniteEnergy_of_fullMass_of_sameSingularityType
    omega θ φ (truncation φ u j) hφ hfull ht.2

end NativeTruncation

/-- Actual original convex E1 retains finite-AE conjugate values before the real L1 representative. -/
theorem conjugate_finite_ae_and_integrable_of_energyOneClass {n : ℕ}
    {P : Set (EuclideanSpace ℝ (Fin n))} (hP : IsCompact P) (hne : P.Nonempty)
    (f : RealConvexFunction (EuclideanSpace ℝ (Fin n)))
    (hE : (fun a => (f.val a : EReal)) ∈
      EnergyOneClass (innerₗ (EuclideanSpace ℝ (Fin n))) P volume) :
    (∀ᵐ p ∂volume.restrict P,
      conjugate (innerₗ (EuclideanSpace ℝ (Fin n))) (fun a => (f.val a : EReal)) p ≠ ⊤ ∧
      conjugate (innerₗ (EuclideanSpace ℝ (Fin n))) (fun a => (f.val a : EReal)) p ≠ ⊥) ∧
    Integrable (fun p => (conjugate (innerₗ (EuclideanSpace ℝ (Fin n)))
      (fun a => (f.val a : EReal)) p).toReal) (volume.restrict P) := by
  let B := innerₗ (EuclideanSpace ℝ (Fin n))
  let G := conjugate B (fun a => (f.val a : EReal))
  have hG : Measurable G := measurable_conjugate B _
  have hpos := ((mem_energyOneClass_iff volume B hP hne).mp hE).2
  have hneg := lintegral_neg_conjugate_lt_top_of_mem_growthClass
    volume B hP hne hE.1.1
  have hproper := isProper_conjugate_of_isContPerfPair B hE.1.1.1
  have hfin : ∀ᵐ p ∂volume.restrict P, G p ≠ ⊤ ∧ G p ≠ ⊥ := by
    filter_upwards [ae_lt_top hG.ereal_toENNReal hpos.ne] with p hp
    exact ⟨EReal.toENNReal_ne_top_iff.mp hp.ne, hproper.2.2 p⟩
  exact ⟨hfin, SGPT.Okounkov.integrable_toReal_of_finite_parts
    (volume.restrict P) G hG hfin hpos hneg⟩

/-- Original convex E1 is equivalent to original full mass together with genuinely
finite conjugate values almost everywhere and an integrable finite representative. -/
theorem energyOneClass_iff_fullMass_and_conjugate_integrable {n : ℕ}
    {P : Set (EuclideanSpace ℝ (Fin n))} (hP : IsCompact P) (hne : P.Nonempty)
    (f : RealConvexFunction (EuclideanSpace ℝ (Fin n))) :
    (fun a => (f.val a : EReal)) ∈
      EnergyOneClass (innerₗ (EuclideanSpace ℝ (Fin n))) P volume ↔
    (fun a => (f.val a : EReal)) ∈
      FullMassClass (innerₗ (EuclideanSpace ℝ (Fin n))) P ∧
    (∀ᵐ p ∂volume.restrict P,
      conjugate (innerₗ (EuclideanSpace ℝ (Fin n))) (fun a => (f.val a : EReal)) p ≠ ⊤ ∧
      conjugate (innerₗ (EuclideanSpace ℝ (Fin n))) (fun a => (f.val a : EReal)) p ≠ ⊥) ∧
    Integrable (fun p => (conjugate (innerₗ (EuclideanSpace ℝ (Fin n)))
      (fun a => (f.val a : EReal)) p).toReal) (volume.restrict P) := by
  constructor
  · intro hE
    exact ⟨hE.1, conjugate_finite_ae_and_integrable_of_energyOneClass hP hne f hE⟩
  · rintro ⟨hFull, hfin, hInt⟩
    apply (mem_energyOneClass_iff volume _ hP hne).mpr
    refine ⟨hFull, ?_⟩
    have he : (∫⁻ p in P, (conjugate (innerₗ (EuclideanSpace ℝ (Fin n)))
        (fun a => (f.val a : EReal)) p).toENNReal ∂volume) =
        ∫⁻ p in P, ENNReal.ofReal (conjugate (innerₗ (EuclideanSpace ℝ (Fin n)))
          (fun a => (f.val a : EReal)) p).toReal ∂volume := by
      apply lintegral_congr_ae
      filter_upwards [hfin] with p hp
      rw [← EReal.coe_toReal hp.1 hp.2, EReal.real_coe_toENNReal, EReal.toReal_coe]
    rw [he]
    exact (lintegral_ofReal_le_lintegral_enorm _).trans_lt hInt.2

/-- Actual constant translation of the original finite convex profile. -/
def convexAddConst {n : ℕ} (f : RealConvexFunction (EuclideanSpace ℝ (Fin n))) (C : ℝ) :
    RealConvexFunction (EuclideanSpace ℝ (Fin n)) :=
  ⟨fun a => f.val a + C, f.property.add_const C⟩

/-- Literal conjugation subtracts the finite constant, retaining both original infinite values. -/
theorem conjugate_convexAddConst {n : ℕ}
    (f : RealConvexFunction (EuclideanSpace ℝ (Fin n))) (C : ℝ) :
    conjugate (innerₗ (EuclideanSpace ℝ (Fin n)))
      (fun a => ((convexAddConst f C).val a : EReal)) =
    fun p => conjugate (innerₗ (EuclideanSpace ℝ (Fin n)))
      (fun a => (f.val a : EReal)) p - (C : EReal) := by
  funext p
  let B := innerₗ (EuclideanSpace ℝ (Fin n))
  have hcost (a : EuclideanSpace ℝ (Fin n)) :
      (B a p : EReal) - ((f.val a + C : ℝ) : EReal) =
        ((B a p : EReal) - (f.val a : EReal)) - (C : EReal) := by
    rw [← EReal.coe_sub, ← EReal.coe_sub, ← EReal.coe_sub]
    exact congrArg (fun q : ℝ => (q : EReal)) (by ring)
  change (⨆ a, (B a p : EReal) - ((f.val a + C : ℝ) : EReal)) =
    (⨆ a, (B a p : EReal) - (f.val a : EReal)) - (C : EReal)
  simp_rw [hcost]
  simpa only [sub_eq_add_neg, ← EReal.coe_neg] using
    iSup_add_coe (fun a => (B a p : EReal) - (f.val a : EReal)) (-C)

/-- The actual raw subgradient image is unchanged, by cancelling one finite real constant. -/
theorem rawSubgradientImage_convexAddConst {n : ℕ}
    (f : RealConvexFunction (EuclideanSpace ℝ (Fin n))) (C : ℝ) :
    rawSubgradientImage (innerₗ (EuclideanSpace ℝ (Fin n)))
      (fun a => ((convexAddConst f C).val a : EReal)) =
    rawSubgradientImage (innerₗ (EuclideanSpace ℝ (Fin n)))
      (fun a => (f.val a : EReal)) := by
  ext p
  simp only [rawSubgradientImage, mem_iUnion, rawSubdifferential, mem_ofPred_eq]
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨a, fun b => ?_⟩
    have h := ha b
    simp only [convexAddConst, ← EReal.coe_add, EReal.coe_le_coe_iff] at h ⊢
    linarith
  · rintro ⟨a, ha⟩
    refine ⟨a, fun b => ?_⟩
    have h := ha b
    simp only [convexAddConst, ← EReal.coe_add, EReal.coe_le_coe_iff] at h ⊢
    linarith

/-- A genuine original convex E1 member remains E1 after finite translation. -/
theorem energyOneClass_convexAddConst {n : ℕ}
    {P : Set (EuclideanSpace ℝ (Fin n))} (hP : IsCompact P) (hne : P.Nonempty)
    (f : RealConvexFunction (EuclideanSpace ℝ (Fin n))) (C : ℝ)
    (hE : (fun a => (f.val a : EReal)) ∈
      EnergyOneClass (innerₗ (EuclideanSpace ℝ (Fin n))) P volume) :
    (fun a => ((convexAddConst f C).val a : EReal)) ∈
      EnergyOneClass (innerₗ (EuclideanSpace ℝ (Fin n))) P volume := by
  let B := innerₗ (EuclideanSpace ℝ (Fin n))
  let : IsFiniteMeasure (volume.restrict P) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hP.measure_lt_top⟩
  have hGrowth : (fun a => ((convexAddConst f C).val a : EReal)) ∈ GrowthClass B P := by
    refine ⟨isProper_coe_of_convexOn (convexAddConst f C).property, ?_⟩
    have h := ((sameSingularityTypeOn_add_const (fun a => (f.val a : EReal)) univ C).1).trans
      hE.1.1.2
    change MoreSingularOn _ _ univ
    simpa only [convexAddConst, EReal.coe_add, B] using h
  have hFull : (fun a => ((convexAddConst f C).val a : EReal)) ∈ FullMassClass B P := by
    refine ⟨hGrowth, ?_⟩
    rcases hE.1.2 with hEmpty | hImage
    · exact Or.inl hEmpty
    · exact Or.inr (by rw [rawSubgradientImage_convexAddConst]; exact hImage)
  obtain ⟨hfin, hInt⟩ := conjugate_finite_ae_and_integrable_of_energyOneClass hP hne f hE
  apply (energyOneClass_iff_fullMass_and_conjugate_integrable hP hne (convexAddConst f C)).mpr
  refine ⟨hFull, ?_, ?_⟩
  · filter_upwards [hfin] with p hp
    simp only [conjugate_convexAddConst]
    rw [← EReal.coe_toReal hp.1 hp.2, ← EReal.coe_sub]
    exact ⟨EReal.coe_ne_top _, EReal.coe_ne_bot _⟩
  · have hreal : (fun p => (conjugate B
        (fun a => ((convexAddConst f C).val a : EReal)) p).toReal) =ᵐ[volume.restrict P]
        fun p => (conjugate B (fun a => (f.val a : EReal)) p).toReal - C := by
      filter_upwards [hfin] with p hp
      simp only [B, conjugate_convexAddConst]
      rw [← EReal.coe_toReal hp.1 hp.2, ← EReal.coe_sub, EReal.toReal_coe, EReal.toReal_coe]
    exact (hInt.sub (integrable_const C)).congr hreal.symm

section Converse

variable {n N : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]
  {θ : ClosedRealOneOneForm n M} {φ u : M → EReal} {hφ : IsModelPotential θ φ}
  {r : ComplexModel n → ℝ}

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "B" => innerₗ E
local notation "T" => tropicalSmoothDomain n

/-- Original convex E1 and independent Cartier chart geometry produce a single finite lower
bound for every actual native truncation energy. Native full mass/E1 of u are not premises. -/
theorem exists_uniform_native_truncation_energy_lower_of_convex_energyOneClass
    (omega : KahlerBackground n M) (hu : IsThetaPshPotential θ.val u) (hule : u ≤ φ)
    (e : ComplexChart n M) (hT : (T : Set (ComplexModel n)) ⊆ e.val.target)
    (hr : IsSmoothLocalPotential θ.val e T r) (f₀ f : RealConvexFunction E)
    (h₀ : EqOn (fun z => chartFunction φ e z + (r z : EReal))
      (fun z => (f₀.val (tropicalization z) : EReal)) T)
    (hf : EqOn (fun z => chartFunction u e z + (r z : EReal))
      (fun z => (f.val (tropicalization z) : EReal)) T)
    (D : Fin N → EffectiveDivisor n M)
    (hcover : (e.val.source ∩ e.val ⁻¹' (T : Set (ComplexModel n)))ᶜ ⊆ ⋃ j, (D j).support)
    (hP : IsCompact (closure (rawSubgradientImage B (fun a => (f₀.val a : EReal)))))
    (hE : (fun a => (f.val a : EReal)) ∈ EnergyOneClass B
      (closure (rawSubgradientImage B (fun a => (f₀.val a : EReal)))) volume) :
    ∃ L : ℝ, ∀ j : ℕ, L ≤ relativeEnergyOfMinimalType θ φ (truncation φ u j)
      hφ.plurisubharmonic (relativeEInfinity_truncation hφ.plurisubharmonic hu
        (MoreSingularOn.of_le fun x _ => hule x) j).1 := by
  classical
  let P := closure (rawSubgradientImage B (fun a => (f₀.val a : EReal)))
  obtain ⟨_E, ψ, _hsupp, _hmetric, _hsum, hψ, hpoles, _hzero⟩ :=
    exists_qpsh_pole_union_of_effective_divisors D
  have hpole : (e.val.source ∩ e.val ⁻¹' (T : Set (ComplexModel n)))ᶜ ⊆
      {x | ψ x = ⊥} := by
    rw [hpoles]
    exact hcover
  have hRefFull : RelativeFullMassPreceq θ φ φ hφ :=
    ⟨hφ.plurisubharmonic, (SameSingularityTypeOn.refl φ univ).1, rfl⟩
  obtain ⟨hne, _hconv, _hRefReal, _hRefReal'⟩ :=
    fullMassClass_of_nativeRelativeFullMass_tropical_chart
      hRefFull e hT hr f₀ f₀ h₀ h₀ hψ hpole hP
  let : IsFiniteMeasure (volume.restrict P) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hP.measure_lt_top⟩
  obtain ⟨hUfinit, hUint⟩ := conjugate_finite_ae_and_integrable_of_energyOneClass hP hne f hE
  have hRefInf : RelativeEInfinity θ φ φ :=
    ⟨hφ.plurisubharmonic, SameSingularityTypeOn.refl φ univ⟩
  have hRefE : RelativeFiniteEnergy θ φ φ hφ :=
    relativeFiniteEnergy_of_fullMass_of_sameSingularityType omega θ φ φ hφ
      ⟨hφ.plurisubharmonic, le_rfl, rfl⟩ (SameSingularityTypeOn.refl φ univ)
  have hRefEP := preceq_of_relativeFiniteEnergy hRefE
  have hLowerInt : Integrable
      (fun p => -f₀.val 0 - (conjugate B (fun a => (f.val a : EReal)) p).toReal)
      (volume.restrict P) := (integrable_const (-f₀.val 0)).sub hUint
  let L := (n.factorial : ℝ) * ∫ p in P,
    -f₀.val 0 - (conjugate B (fun a => (f.val a : EReal)) p).toReal ∂volume
  refine ⟨L, fun j => ?_⟩
  let fj := convexCanonicalTruncation f₀ f j
  have htInf := relativeEInfinity_truncation hφ.plurisubharmonic hu
    (MoreSingularOn.of_le fun x _ => hule x) j
  have htE := nativeFiniteEnergy_canonicalTruncation (hφ := hφ) omega hu hule j
  have htEP := preceq_of_relativeFiniteEnergy htE
  have htProfile := corrected_profile_convexCanonicalTruncation e f₀ f h₀ hf j
  have hEnergy := energy_sub_eq_factorial_conjugate_gap_integral
    omega htEP hRefEP e hT hr f₀ fj f₀ h₀ htProfile h₀ hψ hpole hP
  rw [energy_eq_of_relativeEInfinity omega θ hφ htInf,
    energy_eq_of_relativeEInfinity omega θ hφ hRefInf,
    relativeEnergyOfMinimalType_self, EReal.toReal_coe, EReal.toReal_coe, sub_zero] at hEnergy
  have hGap := integrable_conjugate_gap_of_native_E1_tropical_chart
    omega htEP hRefEP e hT hr f₀ fj f₀ h₀ htProfile h₀ hψ hpole hP
  have hCompare : ∀ᵐ p ∂volume.restrict P,
      -f₀.val 0 - (conjugate B (fun a => (f.val a : EReal)) p).toReal ≤
        (conjugate B (fun a => (f₀.val a : EReal)) p).toReal -
          (conjugate B (fun a => (fj.val a : EReal)) p).toReal := by
    filter_upwards [hUfinit, hGap.1] with p hpU hpT
    have hzero : (0 : E) ∈ effectiveDomain (fun a => (f₀.val a : EReal)) := by
      simp [effectiveDomain]
    have hlow := coe_lower_bound_conjugate_from_zero B
      (isProper_coe_of_convexOn f₀.property) hzero p
    simp only [EReal.toReal_coe] at hlow
    rw [← EReal.coe_toReal hpT.2.2.1 hpT.2.2.2, EReal.coe_le_coe_iff] at hlow
    have hle := conjugate_convexCanonicalTruncation_le f₀ f j p
    change conjugate B (fun a => (fj.val a : EReal)) p ≤
      conjugate B (fun a => (f.val a : EReal)) p at hle
    rw [← EReal.coe_toReal hpT.1 hpT.2.1,
      ← EReal.coe_toReal hpU.1 hpU.2, EReal.coe_le_coe_iff] at hle
    linarith
  have hIntegral := integral_mono_ae hLowerInt hGap.2 hCompare
  have hBound := mul_le_mul_of_nonneg_left hIntegral
    (by positivity : 0 ≤ (n.factorial : ℝ))
  rw [← hEnergy] at hBound
  exact hBound

/-- Convex finite energy manufactures actual native full mass and finite energy via the
constructed truncations. Singular model references and complex dimension zero are retained. -/
theorem relativeFiniteEnergy_of_convex_energyOneClass_tropical_cartier_chart
    (omega : KahlerBackground n M) (hu : IsThetaPshPotential θ.val u) (hule : u ≤ φ)
    (e : ComplexChart n M) (hT : (T : Set (ComplexModel n)) ⊆ e.val.target)
    (hr : IsSmoothLocalPotential θ.val e T r) (f₀ f : RealConvexFunction E)
    (h₀ : EqOn (fun z => chartFunction φ e z + (r z : EReal))
      (fun z => (f₀.val (tropicalization z) : EReal)) T)
    (hf : EqOn (fun z => chartFunction u e z + (r z : EReal))
      (fun z => (f.val (tropicalization z) : EReal)) T)
    (D : Fin N → EffectiveDivisor n M)
    (hcover : (e.val.source ∩ e.val ⁻¹' (T : Set (ComplexModel n)))ᶜ ⊆ ⋃ j, (D j).support)
    (hP : IsCompact (closure (rawSubgradientImage B (fun a => (f₀.val a : EReal)))))
    (hE : (fun a => (f.val a : EReal)) ∈ EnergyOneClass B
      (closure (rawSubgradientImage B (fun a => (f₀.val a : EReal)))) volume) :
    RelativeFiniteEnergy θ φ u hφ := by
  obtain ⟨L, hL⟩ := exists_uniform_native_truncation_energy_lower_of_convex_energyOneClass
    (hφ := hφ) omega hu hule e hT hr f₀ f h₀ hf D hcover hP hE
  exact SingularModelUniformTruncationFullMass.relativeFiniteEnergy_of_uniform_truncation_energy_lower
    omega hu hule hL

/-- The original global singularity comparison internally supplies the finite translation
and its actual profile. Convex E1 then produces unnormalized native E1 without reference L1. -/
theorem relativeFiniteEnergyPreceq_of_convex_energyOneClass_tropical_cartier_chart
    (omega : KahlerBackground n M) (hu : IsThetaPshPotential θ.val u)
    (huφ : MoreSingularOn u φ univ)
    (e : ComplexChart n M) (hT : (T : Set (ComplexModel n)) ⊆ e.val.target)
    (hr : IsSmoothLocalPotential θ.val e T r) (f₀ f : RealConvexFunction E)
    (h₀ : EqOn (fun z => chartFunction φ e z + (r z : EReal))
      (fun z => (f₀.val (tropicalization z) : EReal)) T)
    (hf : EqOn (fun z => chartFunction u e z + (r z : EReal))
      (fun z => (f.val (tropicalization z) : EReal)) T)
    (D : Fin N → EffectiveDivisor n M)
    (hcover : (e.val.source ∩ e.val ⁻¹' (T : Set (ComplexModel n)))ᶜ ⊆ ⋃ j, (D j).support)
    (hP : IsCompact (closure (rawSubgradientImage B (fun a => (f₀.val a : EReal)))))
    (hE : (fun a => (f.val a : EReal)) ∈ EnergyOneClass B
      (closure (rawSubgradientImage B (fun a => (f₀.val a : EReal)))) volume) :
    RelativeFiniteEnergyPreceq θ φ u hφ := by
  have hpsh : RelativePSHPreceq θ φ u := ⟨hu, huφ⟩
  obtain ⟨C, hC⟩ := hpsh.exists_add_le
  have hdom : effectiveDomain (fun a => (f₀.val a : EReal)) = univ := by
    ext a
    simp [effectiveDomain]
  have hp := isProper_coe_of_convexOn f₀.property
  have hlower := lowerSemicontinuous_of_isClosedConvex
    (isClosedConvex_of_isProper_full_domain hp hdom)
  have hbody := closure_rawSubgradientImage_eq_closure_effectiveDomain_conjugate B hp hlower
  have hne : (closure (rawSubgradientImage B (fun a => (f₀.val a : EReal)))).Nonempty := by
    rw [hbody]
    exact (isProper_conjugate_of_isContPerfPair B hp).2.1.closure
  have hTranslate := energyOneClass_convexAddConst hP hne f C hE
  have hProfile : EqOn
      (fun z => chartFunction (fun x => u x + (C : EReal)) e z + (r z : EReal))
      (fun z => ((convexAddConst f C).val (tropicalization z) : EReal)) T := by
    intro z hz
    have hfz : chartFunction u e z + (r z : EReal) =
        (f.val (tropicalization z) : EReal) := hf hz
    change (chartFunction u e z + (C : EReal)) + (r z : EReal) =
      ((f.val (tropicalization z) + C : ℝ) : EReal)
    rw [add_right_comm, hfz, ← EReal.coe_add]
  have hNative := relativeFiniteEnergy_of_convex_energyOneClass_tropical_cartier_chart
    (hφ := hφ) omega (hu.add_const C) (hC C le_rfl)
      e hT hr f₀ (convexAddConst f C) h₀ hProfile D hcover hP hTranslate
  exact relativeFiniteEnergyPreceq_of_add omega (preceq_of_relativeFiniteEnergy hNative)

/-- Compact native upper bounds manufacture the original singularity comparison to zero. -/
theorem relativeFiniteEnergyPreceq_zero_of_convex_energyOneClass_tropical_cartier_chart
    (omega : KahlerBackground n M) (hu : IsThetaPshPotential θ.val u)
    (hzero : φ = fun _ => (0 : EReal))
    (e : ComplexChart n M) (hT : (T : Set (ComplexModel n)) ⊆ e.val.target)
    (hr : IsSmoothLocalPotential θ.val e T r) (f₀ f : RealConvexFunction E)
    (h₀ : EqOn (fun z => chartFunction φ e z + (r z : EReal))
      (fun z => (f₀.val (tropicalization z) : EReal)) T)
    (hf : EqOn (fun z => chartFunction u e z + (r z : EReal))
      (fun z => (f.val (tropicalization z) : EReal)) T)
    (D : Fin N → EffectiveDivisor n M)
    (hcover : (e.val.source ∩ e.val ⁻¹' (T : Set (ComplexModel n)))ᶜ ⊆ ⋃ j, (D j).support)
    (hP : IsCompact (closure (rawSubgradientImage B (fun a => (f₀.val a : EReal)))))
    (hE : (fun a => (f.val a : EReal)) ∈ EnergyOneClass B
      (closure (rawSubgradientImage B (fun a => (f₀.val a : EReal)))) volume) :
    RelativeFiniteEnergyPreceq θ φ u hφ := by
  obtain ⟨m, hm⟩ := exists_le_coe_of_isThetaPshPotential hu
  have huφ : MoreSingularOn u φ univ :=
    ⟨m, fun x _ => by simpa only [hzero, zero_add] using hm x⟩
  exact relativeFiniteEnergyPreceq_of_convex_energyOneClass_tropical_cartier_chart
    omega hu huφ e hT hr f₀ f h₀ hf D hcover hP hE

end Converse

end SGPT.Toric
