import SGPT.Foundations.Analysis.Pending.FiniteGeodesics
import SGPT.Foundations.Analysis.Pending.RooftopEnvelopeLatticeMass
import SGPT.Foundations.Analysis.Pending.GlobalMixedMassMonotone

set_option autoImplicit false

/-!
# Full-mass Perron geodesics and shifted rooftops in every dimension

Xia, *Singularities in global pluripotential theory* (SGPT), §3.1 and §4.2
(`xia-sgpt:page-0132`--`page-0135`, `page-0154`--`page-0156`), works on a connected compact Kähler
manifold `X` of dimension `n` with a model potential `φ` of positive mass.  The relative full-mass
theorems of `Pending.RelativeFullMass` and `Pending.FiniteGeodesics` carry three hypotheses beyond
that setting:

* `0 < n`;
* `BigWithRespectToViaPotentials omega theta` (Xia's bigness of `{θ}`);
* `RooftopMassDiamondReduction.EnvelopeLatticeMassReduction omega theta` (the Step 1 mass
  identities of Xia's Theorem 3.1.3).

Here all three are removed.

* The envelope identities are `RooftopEnvelopeLatticeMass.envelopeLatticeMassReduction`.
* `hbig` is not used by any proof of the chain; it is simply dropped.
* `0 < n` is used by the chain only to produce `Nonempty (Fin n)`, in three places of
  `Pending.RelativeFullMassEnergyUpwardClosure` (the comparison principle, the Guedj--Zeriahi
  superlevel inequality and the pole-null step of the energy integral).  In dimension `0` these are
  elementary: a point of a zero-dimensional manifold is open, so a theta-PSH potential has no pole
  (`ne_bot_of_dim_zero`), and the diagonal non-pluripolar measure has no slot, so it does not depend
  on the potential (`diagonalPotentialMeasure_eq_of_dim_zero`).  Every other lemma of the chain
  only passes `0 < n` along (measured on the proof terms); the copies below drop it, and mass
  monotonicity comes from `GlobalMixedMassMonotone.globalMixedMass_mono_of_isThetaPshPotential`,
  which has no dimension hypothesis.

So every statement below assumes only a connected compact Kähler manifold (of any dimension), a
model potential and endpoints in the relevant relative class.  Connectedness is the standing
hypothesis of the diagonal mass in the blueprint (`trace:diagonal-mass`) and cannot be dropped:
on a disconnected manifold the positive mass of `φ` may sit on one component only, and the
rooftops and Perron slices can then be identically `-∞` on another.

The proofs are those of the original modules with the three hypotheses removed; no statement of
those modules is changed.

## Main results

* `finiteTranslation_invariance`, `moreSingularOn_add_const_and_mass_eq` (finite translations);
* `mass_max_add_const_lt`, `isThetaPshPotential_rooftop_add_const_of_massCriterion` and
  `isThetaPshPotential_rooftop_add_const` (the rooftop is theta-PSH, by Xia's mass criterion and by
  the epsilon-barrier), `rooftop_add_const_le_obstacles`, `reference_mass_le_rooftop_add_const`,
  `relativeFullMass_rooftop_add_const` (shifted rooftops);
* `shiftedRooftop_monotone'`, `uscRegularization_iSup_shiftedRooftop_eq`,
  `relativeFullMass_rooftop_add_const_tendsto` (rooftop exhaustion);
* `finiteGeodesic_isSubgeodesicInterior_of_common_lower` (the Perron interior from a common lower
  barrier, no mass), `finiteGeodesic_isSubgeodesicInterior_of_relativeFullMass`,
  `finiteGeodesic_tendsto_left_of_relativeFullMass`,
  `finiteGeodesic_tendsto_right_of_relativeFullMass`,
  `finiteGeodesic_isSubgeodesicFrom_of_relativeFullMass` (full-mass Perron geodesics);
* `finiteGeodesic_fullMass_sandwich`: `u₀ ∧ u₁ ≤ G_t ≤ (1 - t) u₀ + t u₁ ≤ φ` and
  `G_t ∈ E(X, θ; φ)` (from `rooftop_le_finiteGeodesic`, `finiteGeodesic_le_eRealChord_le_reference`,
  `relativeFullMass_finiteGeodesic`);
* the finite-energy and bounded-singularity forms.
-/

open Filter Set MeasureTheory
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis.Pending.FiniteGeodesicsFullMassAnyDim

open FirstPass FirstPass.PositiveClasses DiagonalMass

noncomputable section

/-- For a nondecreasing family indexed by `ℝ`, the supremum over `ℝ` equals the supremum over the
integers `j ∈ ℕ`. -/
theorem iSup_real_eq_iSup_nat_of_monotone {β : Type*} [CompleteLattice β] {f : ℝ → β}
    (hf : Monotone f) : (⨆ C : ℝ, f C) = ⨆ j : ℕ, f (j : ℝ) := by
  refine le_antisymm (iSup_le fun C => ?_) (iSup_le fun j => le_iSup f (j : ℝ))
  exact (hf (Nat.le_ceil C)).trans (le_iSup (fun j : ℕ => f (j : ℝ)) ⌈C⌉₊)

/-! ### Dimension zero -/

section DimensionZero

/-- In a zero-dimensional manifold every point is open: a chart is injective on its open source
and takes values in the one-point model space. -/
theorem isOpen_singleton_of_dim_zero {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel 0) M] (x : M) : IsOpen ({x} : Set M) := by
  let e := chartAt (ComplexModel 0) x
  have hsrc : e.source = {x} := by
    ext y
    constructor
    · intro hy
      exact e.injOn hy (mem_chart_source _ x) (Subsingleton.elim _ _)
    · rintro rfl
      exact mem_chart_source _ y
  rw [← hsrc]
  exact e.open_source

/-- In dimension zero a theta-PSH potential has no pole: local nondegeneracy, tested on the open
singleton, says so. -/
theorem ne_bot_of_dim_zero {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel 0) M] [IsComplexManifold 0 M] {θ : SmoothRealForm 0 M 2}
    {f : M → EReal} (hf : IsThetaPshPotential θ f) (x : M) : f x ≠ ⊥ := by
  obtain ⟨y, hy, hfy⟩ := hf.2 x {x} (isOpen_singleton_of_dim_zero x) (mem_singleton x)
  rw [mem_singleton_iff] at hy
  rwa [hy] at hfy

/-- In dimension zero the diagonal non-pluripolar measure has no slot, so it does not depend on
the potential. -/
theorem diagonalPotentialMeasure_eq_of_dim_zero {M : Type*} [TopologicalSpace M]
    [MeasurableSpace M] [BorelSpace M] [ChartedSpace (ComplexModel 0) M] [IsComplexManifold 0 M]
    [CompactSpace M] (θ : ClosedRealOneOneForm 0 M) {f g : M → EReal}
    (hf : IsThetaPshPotential θ.val f) (hg : IsThetaPshPotential θ.val g) :
    diagonalPotentialMeasure θ f hf = diagonalPotentialMeasure θ g hg := by
  have key : ∀ (us vs : Fin 0 → M → EReal) (hus : ∀ i, ThetaPlurisubharmonic θ.val (us i))
      (hvs : ∀ i, ThetaPlurisubharmonic θ.val (vs i)),
      GlobalNonPluripolar.globalMixedMeasure (fun _ : Fin 0 => θ) us hus =
        GlobalNonPluripolar.globalMixedMeasure (fun _ : Fin 0 => θ) vs hvs := by
    intro us vs hus hvs
    obtain rfl : us = vs := Subsingleton.elim _ _
    rfl
  exact key _ _ _ _

end DimensionZero

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M]

/-! ### The energy estimate in every dimension -/

section Energy

open RelativeFullMassEnergyUpwardClosure

/-- The pole set of a theta-PSH potential is null for its own diagonal measure, in every
dimension: for `n > 0` this is `GlobalSlotComparison.globalMixedMeasure_pole_null`, and for
`n = 0` the pole set is empty. -/
theorem diagonalPotentialMeasure_pole_null {theta : ClosedRealOneOneForm n M} {f : M → EReal}
    (hf : IsThetaPshPotential theta.val f) :
    diagonalPotentialMeasure theta f hf {x | f x = ⊥} = 0 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hempty : {x | f x = ⊥} = (∅ : Set M) :=
      eq_empty_iff_forall_notMem.mpr fun x hx => ne_bot_of_dim_zero hf x hx
    rw [hempty, measure_empty]
  · exact GlobalSlotComparison.globalMixedMeasure_pole_null (fun _ => hf.1) ⟨0, hn⟩

/-- `RelativeFullMassEnergyUpwardClosure.lintegral_canonicalERealAbsDiff_eq_ofReal_toReal` without
`0 < n`. -/
theorem lintegral_canonicalERealAbsDiff_eq_ofReal_toReal
    {theta : ClosedRealOneOneForm n M} {phi f : M → EReal}
    (hphitop : ∀ x, phi x ≠ ⊤) (hf : IsThetaPshPotential theta.val f)
    (hfphi : ∀ x, f x ≤ phi x) :
    ∫⁻ x, canonicalERealAbsDiff (phi x) (f x) ∂ diagonalPotentialMeasure theta f hf =
      ∫⁻ x, ENNReal.ofReal (canonicalERealAbsDiff (phi x) (f x)).toReal
        ∂ diagonalPotentialMeasure theta f hf := by
  apply lintegral_congr_ae
  have hpole : diagonalPotentialMeasure theta f hf {x | f x = ⊥} = 0 :=
    diagonalPotentialMeasure_pole_null hf
  have hae : ∀ᵐ x ∂ diagonalPotentialMeasure theta f hf, f x ≠ ⊥ := by
    rw [ae_iff]
    simpa using hpole
  filter_upwards [hae] with x hx
  have hftop : f x ≠ ⊤ := hf.1.quasiPlurisubharmonic.ne_top x
  have hpb : phi x ≠ ⊥ := fun h => hx (le_bot_iff.mp ((hfphi x).trans_eq h))
  obtain ⟨a, ha⟩ : ∃ a : ℝ, f x = a := ⟨(f x).toReal, (EReal.coe_toReal hftop hx).symm⟩
  obtain ⟨b, hb⟩ : ∃ b : ℝ, phi x = b :=
    ⟨(phi x).toReal, (EReal.coe_toReal (hphitop x) hpb).symm⟩
  have hne : canonicalERealAbsDiff (phi x) (f x) ≠ ⊤ := by
    rw [ha, hb, canonicalERealAbsDiff_coe_coe]
    exact ENNReal.ofReal_ne_top
  exact (ENNReal.ofReal_toReal hne).symm

/-- **Guedj--Zeriahi's fundamental inequality, relative form, in every dimension.**  For
`u ≤ v ≤ φ` with `u` of full relative mass and `t > 0`,
`θ_v^n {t < |φ - v|} ≤ 2^n θ_u^n {t ≤ 2 |φ - u|}`.  For `n > 0` this is
`RelativeFullMassEnergyUpwardClosure.diagonalPotentialMeasure_superlevel_le`; for `n = 0` the two
measures agree and `|φ - v| ≤ |φ - u|` pointwise. -/
theorem diagonalPotentialMeasure_superlevel_le [ConnectedSpace M]
    (omega : KahlerBackground n M) {theta : ClosedRealOneOneForm n M}
    {phi u v : M → EReal} {hphi : IsModelPotential theta phi}
    (hu : RelativeFullMass theta phi u hphi) (hv : IsThetaPshPotential theta.val v)
    (huv : u ≤ v) (hvphi : v ≤ phi) {t : ℝ} (ht : 0 < t) :
    diagonalPotentialMeasure theta v hv
        {x | t < (canonicalERealAbsDiff (phi x) (v x)).toReal} ≤
      2 ^ n * diagonalPotentialMeasure theta u hu.plurisubharmonic
        {x | t ≤ 2 * (canonicalERealAbsDiff (phi x) (u x)).toReal} := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [pow_zero, one_mul,
      diagonalPotentialMeasure_eq_of_dim_zero theta hv hu.plurisubharmonic]
    apply measure_mono
    intro x hx
    simp only [Set.mem_ofPred_eq] at hx ⊢
    have hphiP : IsThetaPshPotential theta.val phi := hphi.plurisubharmonic
    have hphitop : phi x ≠ ⊤ := hphiP.1.quasiPlurisubharmonic.ne_top x
    have hutop : u x ≠ ⊤ := ne_top_of_le_ne_top hphitop ((huv x).trans (hvphi x))
    have hvtop : v x ≠ ⊤ := ne_top_of_le_ne_top hphitop (hvphi x)
    obtain ⟨c, hc⟩ : ∃ c : ℝ, u x = c :=
      ⟨(u x).toReal,
        (EReal.coe_toReal hutop (ne_bot_of_dim_zero hu.plurisubharmonic x)).symm⟩
    obtain ⟨a, ha⟩ : ∃ a : ℝ, v x = a :=
      ⟨(v x).toReal, (EReal.coe_toReal hvtop (ne_bot_of_dim_zero hv x)).symm⟩
    obtain ⟨b, hb⟩ : ∃ b : ℝ, phi x = b :=
      ⟨(phi x).toReal, (EReal.coe_toReal hphitop (ne_bot_of_dim_zero hphiP x)).symm⟩
    have hca : c ≤ a := EReal.coe_le_coe_iff.mp (by rw [← hc, ← ha]; exact huv x)
    have hab : a ≤ b := EReal.coe_le_coe_iff.mp (by rw [← ha, ← hb]; exact hvphi x)
    rw [hb, ha, toReal_canonicalERealAbsDiff_coe_coe hab] at hx
    rw [hb, hc, toReal_canonicalERealAbsDiff_coe_coe (hca.trans hab)]
    linarith
  · exact RelativeFullMassEnergyUpwardClosure.diagonalPotentialMeasure_superlevel_le hn omega hu hv
      huv hvphi ht

variable [ConnectedSpace M] in
/-- **The energy estimate in every dimension.**  For `u ≤ v ≤ φ` with `u` of full relative mass,
`∫ |φ - v| θ_v^n ≤ 2^n · 2 · ∫ |φ - u| θ_u^n`.  This is
`RelativeFullMassEnergyUpwardClosure.relativeFiniteEnergyIntegral_le` without `0 < n`. -/
theorem relativeFiniteEnergyIntegral_le (omega : KahlerBackground n M)
    {theta : ClosedRealOneOneForm n M} {phi u v : M → EReal}
    {hphi : IsModelPotential theta phi}
    (hu : RelativeFullMass theta phi u hphi) (hv : IsThetaPshPotential theta.val v)
    (huv : u ≤ v) (hvphi : v ≤ phi) :
    relativeFiniteEnergyIntegral theta phi v hv ≤
      2 ^ n * (2 * relativeFiniteEnergyIntegral theta phi u hu.plurisubharmonic) := by
  have huP : IsThetaPshPotential theta.val u := hu.plurisubharmonic
  have hphitop : ∀ x, phi x ≠ ⊤ := fun x =>
    hphi.plurisubharmonic.1.quasiPlurisubharmonic.ne_top x
  have hphim : Measurable phi :=
    hphi.plurisubharmonic.1.quasiPlurisubharmonic.upperSemicontinuous.measurable
  have hvm : Measurable v := hv.1.quasiPlurisubharmonic.upperSemicontinuous.measurable
  have hum : Measurable u := huP.1.quasiPlurisubharmonic.upperSemicontinuous.measurable
  set μv := diagonalPotentialMeasure theta v hv with hμv
  set μu := diagonalPotentialMeasure theta u huP with hμu
  let Gv : M → ℝ := fun x => (canonicalERealAbsDiff (phi x) (v x)).toReal
  let Gu : M → ℝ := fun x => (canonicalERealAbsDiff (phi x) (u x)).toReal
  have hGv : Measurable Gv := (hphim.canonicalERealAbsDiff hvm).ennreal_toReal
  have hGu : Measurable Gu := (hphim.canonicalERealAbsDiff hum).ennreal_toReal
  have hGu2 : Measurable fun x => 2 * Gu x := hGu.const_mul 2
  unfold relativeFiniteEnergyIntegral
  rw [lintegral_canonicalERealAbsDiff_eq_ofReal_toReal hphitop hv hvphi,
    lintegral_eq_lintegral_meas_lt μv
      (Eventually.of_forall fun x => ENNReal.toReal_nonneg) hGv.aemeasurable]
  calc ∫⁻ t in Ioi 0, μv {a | t < Gv a}
      ≤ ∫⁻ t in Ioi 0, 2 ^ n * μu {a | t ≤ 2 * Gu a} := by
        apply setLIntegral_mono' measurableSet_Ioi
        intro t ht
        exact diagonalPotentialMeasure_superlevel_le omega hu hv huv hvphi ht
    _ = 2 ^ n * ∫⁻ t in Ioi 0, μu {a | t ≤ 2 * Gu a} :=
        lintegral_const_mul' _ _ (ENNReal.pow_ne_top ENNReal.ofNat_ne_top)
    _ = 2 ^ n * ∫⁻ x, ENNReal.ofReal (2 * Gu x) ∂μu := by
        rw [lintegral_eq_lintegral_meas_le μu
          (Eventually.of_forall fun x => by positivity) hGu2.aemeasurable]
    _ = 2 ^ n * (2 * ∫⁻ x, ENNReal.ofReal (Gu x) ∂μu) := by
        rw [← lintegral_const_mul' _ _ ENNReal.ofNat_ne_top]
        congr 2
        funext x
        rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
    _ ≤ 2 ^ n * (2 * ∫⁻ x, canonicalERealAbsDiff (phi x) (u x) ∂μu) := by
        gcongr with x
        exact ENNReal.ofReal_toReal_le

end Energy

/-! ### Mass monotonicity and the relative full-mass class -/

/-- Equal singularity type gives equal total mixed mass, in every dimension (monotonicity in both
directions, `GlobalMixedMassMonotone.globalMixedMass_mono_of_isThetaPshPotential`). -/
theorem globalMixedMass_eq_of_sameSingularityType {θ : Fin n → ClosedRealOneOneForm n M}
    {u v : Fin n → M → EReal} (omega : KahlerBackground n M)
    (hu : ∀ i, IsThetaPshPotential (θ i).val (u i))
    (hv : ∀ i, IsThetaPshPotential (θ i).val (v i))
    (huv : ∀ i, SameSingularityTypeOn (u i) (v i) univ) :
    MixedMass.globalMixedMass θ u (fun i => (hu i).1) =
      MixedMass.globalMixedMass θ v (fun i => (hv i).1) :=
  le_antisymm
    (GlobalMixedMassMonotone.globalMixedMass_mono_of_isThetaPshPotential omega hu hv
      (fun i => (huv i).1))
    (GlobalMixedMassMonotone.globalMixedMass_mono_of_isThetaPshPotential omega hv hu
      (fun i => (huv i).2))

/-- Relative full mass is closed under singularity-order interpolation between a full-mass
potential and the model potential (Xia, Proposition 3.1.22, full-mass case), in every dimension
and without connectedness. -/
theorem relativeFullMass_of_singularity_between
    (omega : KahlerBackground n M)
    {theta : ClosedRealOneOneForm n M} {phi u v : M → EReal}
    {hphi : IsModelPotential theta phi}
    (hu : RelativeFullMass theta phi u hphi)
    (hv : IsThetaPshPotential theta.val v)
    (huv : MoreSingularOn u v univ)
    (hvphi : MoreSingularOn v phi univ) (hvle : v ≤ phi) :
    RelativeFullMass theta phi v hphi := by
  rcases hu with ⟨hupsh, _, humass⟩
  apply (relativeFullMass_iff theta phi v hphi hv).2
  refine ⟨hvle, le_antisymm ?_ ?_⟩
  · change MixedMass.globalMixedMass (fun _ : Fin n => theta) (fun _ => v)
        (fun _ => hv.1) ≤
      MixedMass.globalMixedMass (fun _ : Fin n => theta) (fun _ => phi)
        (fun _ => hphi.plurisubharmonic.1)
    exact GlobalMixedMassMonotone.globalMixedMass_mono_of_isThetaPshPotential omega
      (fun _ => hv) (fun _ => hphi.plurisubharmonic) (fun _ => hvphi)
  · calc
      diagonalPotentialMass theta phi hphi.plurisubharmonic =
          diagonalPotentialMass theta u hupsh := humass.symm
      _ ≤ diagonalPotentialMass theta v hv := by
        change MixedMass.globalMixedMass (fun _ : Fin n => theta) (fun _ => u)
              (fun _ => hupsh.1) ≤
            MixedMass.globalMixedMass (fun _ : Fin n => theta) (fun _ => v)
              (fun _ => hv.1)
        exact GlobalMixedMassMonotone.globalMixedMass_mono_of_isThetaPshPotential omega
          (fun _ => hupsh) (fun _ => hv) (fun _ => huv)

/-- The pointwise form of `relativeFullMass_of_singularity_between`: a theta-PSH potential between
a relative full-mass potential and the model potential has relative full mass. -/
theorem relativeFullMass_of_between
    (omega : KahlerBackground n M)
    {theta : ClosedRealOneOneForm n M} {phi u v : M → EReal}
    {hphi : IsModelPotential theta phi}
    (hu : RelativeFullMass theta phi u hphi)
    (hv : IsThetaPshPotential theta.val v)
    (huv : u ≤ v) (hvphi : v ≤ phi) :
    RelativeFullMass theta phi v hphi :=
  relativeFullMass_of_singularity_between omega hu hv
    (MoreSingularOn.of_le fun x _ => huv x)
    (MoreSingularOn.of_le fun x _ => hvphi x) hvphi

/-- **Xia, Proposition 3.1.22, `E¹` case, in every dimension.**  If `u ≤ v ≤ φ`,
`u ∈ E¹(X, θ; φ)` and `v` is theta-PSH, then `v ∈ E¹(X, θ; φ)`. -/
theorem relativeFiniteEnergy_of_between_of_kahler [ConnectedSpace M]
    (omega : KahlerBackground n M)
    {theta : ClosedRealOneOneForm n M} {phi u v : M → EReal}
    {hphi : IsModelPotential theta phi}
    (hu : RelativeFiniteEnergy theta phi u hphi)
    (hv : IsThetaPshPotential theta.val v)
    (huv : u ≤ v) (hvphi : v ≤ phi) :
    RelativeFiniteEnergy theta phi v hphi := by
  have hufull : RelativeFullMass theta phi u hphi := hu.fullMass
  have hfull : RelativeFullMass theta phi v hphi :=
    relativeFullMass_of_between omega hufull hv huv hvphi
  have hufin : relativeFiniteEnergyIntegral theta phi u hufull.plurisubharmonic < ⊤ :=
    ((relativeFiniteEnergy_iff theta phi u hphi hufull.plurisubharmonic).1 hu).2
  refine (relativeFiniteEnergy_iff theta phi v hphi hv).2 ⟨hfull, ?_⟩
  refine (relativeFiniteEnergyIntegral_le omega hufull hv huv hvphi).trans_lt ?_
  exact ENNReal.mul_lt_top (ENNReal.pow_ne_top ENNReal.ofNat_ne_top).lt_top
    (ENNReal.mul_lt_top ENNReal.ofNat_lt_top hufin)

/-! ### Finite translations -/

/-- **Finite-translation invariance** (Xia SGPT, `xia-sgpt:page-0132`; blueprint
`trace:finite-translation-invariance`).  If `v` is theta-PSH and `C ∈ ℝ`, then `v + C` is
theta-PSH, `v + C ∼ v` on the whole manifold, and the two diagonal masses agree (for every witness
of the theta-PSH property).  No dimension or connectedness hypothesis. -/
theorem finiteTranslation_invariance (theta : ClosedRealOneOneForm n M) {v : M → EReal}
    (hv : IsThetaPshPotential theta.val v) (C : ℝ) :
    IsThetaPshPotential theta.val (fun x => v x + (C : EReal)) ∧
      SameSingularityTypeOn (fun x => v x + (C : EReal)) v univ ∧
      ∀ hvC : IsThetaPshPotential theta.val (fun x => v x + (C : EReal)),
        diagonalPotentialMass theta (fun x => v x + (C : EReal)) hvC =
          diagonalPotentialMass theta v hv :=
  ⟨hv.add_const C, sameSingularityTypeOn_add_const v univ C, fun hvC => by
    unfold diagonalPotentialMass
    rw [DiagonalMeasureRegularity.diagonalPotentialMeasure_add_const theta hv C hvC]⟩

/-- **A finite translation does not change membership in an unnormalized relative full-mass
class** (blueprint `trace:finite-translation-invariance`, last sentence): if `v ⪯ φ` and `v` has the
mass of `φ`, then so has `v + C`, and `v + C ⪯ φ`. -/
theorem moreSingularOn_add_const_and_mass_eq (theta : ClosedRealOneOneForm n M)
    {phi v : M → EReal} (hphi : IsThetaPshPotential theta.val phi)
    (hv : IsThetaPshPotential theta.val v) (hvphi : MoreSingularOn v phi univ)
    (hmass : diagonalPotentialMass theta v hv = diagonalPotentialMass theta phi hphi) (C : ℝ) :
    MoreSingularOn (fun x => v x + (C : EReal)) phi univ ∧
      ∀ hvC : IsThetaPshPotential theta.val (fun x => v x + (C : EReal)),
        diagonalPotentialMass theta (fun x => v x + (C : EReal)) hvC =
          diagonalPotentialMass theta phi hphi :=
  ⟨((sameSingularityTypeOn_add_const v univ C).1).trans hvphi, fun hvC =>
    ((finiteTranslation_invariance theta hv C).2.2 hvC).trans hmass⟩

/-! ### Shifted rooftops -/

section Rooftops

variable [ConnectedSpace M]

/-- **Xia, Proposition 3.1.5, relative full-mass case** (blueprint
`trace:rooftop-psh-positive-mass`).  For `u, v ∈ E(X, θ; φ)` and `C ∈ ℝ`, the rooftop
`P_θ(min(u, v + C))` is a genuine theta-PSH potential.  No dimension hypothesis. -/
theorem isThetaPshPotential_rooftop_add_const (omega : KahlerBackground n M)
    (theta : ClosedRealOneOneForm n M)
    (phi u v : M → EReal) (hphi : IsModelPotential theta phi)
    (hu : RelativeFullMass theta phi u hphi)
    (hv : RelativeFullMass theta phi v hphi) (C : ℝ) :
    IsThetaPshPotential theta.val
      (rooftopEnvelope theta.val (fun x => min (u x) (v x + (C : EReal)))) := by
  obtain ⟨w, hw, hwu, hwv⟩ :=
    exists_common_thetaPsh_lower_of_relativeFullMass omega theta phi u v
      hphi hu hv C
  exact isThetaPshPotential_rooftop_min_add_const_of_common_thetaPsh_lower_qe
    theta u v w hu.plurisubharmonic hw
    (quasiEverywhere_of_forall fun x => hwu x) C
    (quasiEverywhere_of_forall fun x => hwv x)

omit [ConnectedSpace M] in
/-- **The strict mass hypothesis of Xia's Proposition 3.1.5 for relative full-mass inputs**
(blueprint `trace:rooftop-psh-positive-mass`): for `u, v ∈ E(X, θ; φ)` and `C ∈ ℝ`,
`∫⟨θ_{u ∨ (v + C)}^n⟩ < ∫⟨θ_u^n⟩ + ∫⟨θ_{v + C}^n⟩`.  The left side is at most the mass `V` of `φ`
(monotonicity, `u ∨ (v + C) ≤ φ + max(C, 0)`), the right side is `V + V` (full mass and
finite-translation invariance), and `0 < V < ∞`. -/
theorem mass_max_add_const_lt (omega : KahlerBackground n M)
    (theta : ClosedRealOneOneForm n M)
    (phi u v : M → EReal) (hphi : IsModelPotential theta phi)
    (hu : RelativeFullMass theta phi u hphi)
    (hv : RelativeFullMass theta phi v hphi) (C : ℝ) :
    diagonalPotentialMass theta (fun x => max (u x) (v x + (C : EReal)))
        (IsThetaPshPotential.max hu.plurisubharmonic (hv.plurisubharmonic.add_const C)) <
      diagonalPotentialMass theta u hu.plurisubharmonic +
        diagonalPotentialMass theta (fun x => v x + (C : EReal))
          (hv.plurisubharmonic.add_const C) := by
  set V := diagonalPotentialMass theta phi hphi.plurisubharmonic with hV
  have humass : diagonalPotentialMass theta u hu.plurisubharmonic = V :=
    ((relativeFullMass_iff theta phi u hphi hu.plurisubharmonic).1 hu).2
  have hvmass : diagonalPotentialMass theta v hv.plurisubharmonic = V :=
    ((relativeFullMass_iff theta phi v hphi hv.plurisubharmonic).1 hv).2
  have hvCmass : diagonalPotentialMass theta (fun x => v x + (C : EReal))
      (hv.plurisubharmonic.add_const C) = V :=
    ((finiteTranslation_invariance theta hv.plurisubharmonic C).2.2 _).trans hvmass
  have hmaxle : diagonalPotentialMass theta (fun x => max (u x) (v x + (C : EReal)))
      (IsThetaPshPotential.max hu.plurisubharmonic (hv.plurisubharmonic.add_const C)) ≤ V := by
    rw [hV]
    refine GlobalMixedMassMonotone.globalMixedMass_mono_of_isThetaPshPotential omega
      (fun _ : Fin n => IsThetaPshPotential.max hu.plurisubharmonic
        (hv.plurisubharmonic.add_const C))
      (fun _ => hphi.plurisubharmonic) (fun _ => ⟨max C 0, fun x _ => ?_⟩)
    refine max_le ?_ ?_
    · calc u x ≤ phi x := hu.le_reference x
        _ = phi x + ((0 : ℝ) : EReal) := by simp
        _ ≤ phi x + ((max C 0 : ℝ) : EReal) :=
            add_le_add le_rfl (EReal.coe_le_coe_iff.mpr (le_max_right _ _))
    · exact add_le_add (hv.le_reference x)
        (EReal.coe_le_coe_iff.mpr (le_max_left _ _))
  have hVpos : 0 < V := hphi.positive_mass
  have hVtop : V ≠ ⊤ :=
    (MixedMass.globalMixedMass_lt_top omega
      (fun _ : Fin n => hphi.plurisubharmonic.1)).ne
  rw [humass, hvCmass]
  exact hmaxle.trans_lt (ENNReal.lt_add_right hVtop hVpos.ne')

/-- **Xia, Proposition 3.1.5, relative full-mass case, by the mass criterion** (blueprint
`trace:rooftop-psh-positive-mass`): the strict mass hypothesis `mass_max_add_const_lt` and Xia's
Proposition 3.1.5 (`RooftopPshCriterion.isThetaPshPotential_rooftopEnvelope_min_of_mass_lt`,
blueprint `trace:rooftop-psh-criterion`) make `P_θ(min(u, v + C))` theta-PSH.  The same conclusion
as `isThetaPshPotential_rooftop_add_const`, by the route the blueprint states. -/
theorem isThetaPshPotential_rooftop_add_const_of_massCriterion (omega : KahlerBackground n M)
    (theta : ClosedRealOneOneForm n M)
    (phi u v : M → EReal) (hphi : IsModelPotential theta phi)
    (hu : RelativeFullMass theta phi u hphi)
    (hv : RelativeFullMass theta phi v hphi) (C : ℝ) :
    IsThetaPshPotential theta.val
      (rooftopEnvelope theta.val (fun x => min (u x) (v x + (C : EReal)))) :=
  RooftopPshCriterion.isThetaPshPotential_rooftopEnvelope_min_of_mass_lt omega theta
    hu.plurisubharmonic (hv.plurisubharmonic.add_const C)
    (mass_max_add_const_lt omega theta phi u v hphi hu hv C)

omit [BorelSpace M] [ConnectedSpace M] in
/-- Rooftop obstacle recovery: `P_θ(min(u, v + C)) ≤ u` and `≤ v + C`.  No dimension or
connectedness hypothesis. -/
theorem rooftop_add_const_le_obstacles (theta : ClosedRealOneOneForm n M)
    (phi u v : M → EReal) (hphi : IsModelPotential theta phi)
    (hu : RelativeFullMass theta phi u hphi)
    (hv : RelativeFullMass theta phi v hphi) (C : ℝ) :
    rooftopEnvelope theta.val (fun x => min (u x) (v x + (C : EReal))) ≤ u ∧
      rooftopEnvelope theta.val (fun x => min (u x) (v x + (C : EReal))) ≤
        fun x => v x + (C : EReal) :=
  rooftopEnvelope_min_add_const_le_obstacles hu.plurisubharmonic.1 hv.plurisubharmonic.1 C

/-- **Rooftop mass lower bound** (Xia SGPT, `xia-sgpt:page-0108`, `page-0132`; blueprint
`trace:rooftop-mass-lower`).  For `u, v ∈ E(X, θ; φ)` and `C ∈ ℝ`, the mass of
`P_θ(min(u, v + C))` is at least that of `φ`.  The rooftop mass diamond is used with its envelope
identities proved (`RooftopEnvelopeLatticeMass.envelopeLatticeMassReduction`). -/
theorem reference_mass_le_rooftop_add_const (omega : KahlerBackground n M)
    (theta : ClosedRealOneOneForm n M)
    (phi u v : M → EReal) (hphi : IsModelPotential theta phi)
    (hu : RelativeFullMass theta phi u hphi)
    (hv : RelativeFullMass theta phi v hphi) (C : ℝ)
    (hw : IsThetaPshPotential theta.val
      (rooftopEnvelope theta.val
        (fun x => min (u x) (v x + (C : EReal))))) :
    diagonalPotentialMass theta phi hphi.plurisubharmonic ≤
      diagonalPotentialMass theta
        (rooftopEnvelope theta.val
          (fun x => min (u x) (v x + (C : EReal)))) hw := by
  set V := diagonalPotentialMass theta phi hphi.plurisubharmonic with hV
  have hv' : IsThetaPshPotential theta.val (fun x => v x + (C : EReal)) :=
    hv.plurisubharmonic.add_const C
  have hmax : IsThetaPshPotential theta.val
      (fun x => max (u x) (v x + (C : EReal))) :=
    IsThetaPshPotential.max hu.plurisubharmonic hv'
  have humass : diagonalPotentialMass theta u hu.plurisubharmonic = V :=
    ((relativeFullMass_iff theta phi u hphi hu.plurisubharmonic).1 hu).2
  have hvmass : diagonalPotentialMass theta v hv.plurisubharmonic = V :=
    ((relativeFullMass_iff theta phi v hphi hv.plurisubharmonic).1 hv).2
  have hv'mass : diagonalPotentialMass theta (fun x => v x + (C : EReal)) hv' = V := by
    rw [← hvmass]
    exact globalMixedMass_eq_of_sameSingularityType omega
      (fun _ : Fin n => hv') (fun _ => hv.plurisubharmonic)
      (fun _ => sameSingularityTypeOn_add_const v univ C)
  have hmaxle : diagonalPotentialMass theta
      (fun x => max (u x) (v x + (C : EReal))) hmax ≤ V := by
    rw [hV]
    refine GlobalMixedMassMonotone.globalMixedMass_mono_of_isThetaPshPotential omega
      (fun _ : Fin n => hmax)
      (fun _ => hphi.plurisubharmonic) (fun _ => ⟨max C 0, fun x _ => ?_⟩)
    refine max_le ?_ ?_
    · calc u x ≤ phi x := hu.le_reference x
        _ = phi x + ((0 : ℝ) : EReal) := by simp
        _ ≤ phi x + ((max C 0 : ℝ) : EReal) :=
            add_le_add le_rfl (EReal.coe_le_coe_iff.mpr (le_max_right _ _))
    · exact add_le_add (hv.le_reference x)
        (EReal.coe_le_coe_iff.mpr (le_max_left _ _))
  have hdiamond := RooftopMassDiamond.mass_add_mass_le_mass_max_add_mass_rooftop
    omega theta hu.plurisubharmonic hv' hmax hw
    (RooftopEnvelopeLatticeMass.envelopeLatticeMassReduction omega theta)
  rw [humass, hv'mass] at hdiamond
  have hstep : V + V ≤ V + diagonalPotentialMass theta
      (rooftopEnvelope theta.val
        (fun x => min (u x) (v x + (C : EReal)))) hw :=
    hdiamond.trans (add_le_add hmaxle le_rfl)
  have hVtop : V ≠ ⊤ :=
    (MixedMass.globalMixedMass_lt_top omega
      (fun _ : Fin n => hphi.plurisubharmonic.1)).ne
  exact (ENNReal.add_le_add_iff_left hVtop).1 hstep

/-- **Full-mass closure under shifted rooftops** (Xia SGPT, `xia-sgpt:page-0132`--`page-0134`;
blueprint `trace:full-mass-rooftop-closure`).  For `u, v ∈ E(X, θ; φ)` and `C ∈ ℝ`, the rooftop
`P_θ(min(u, v + C))` lies in `E(X, θ; φ)` and below both obstacles. -/
theorem relativeFullMass_rooftop_add_const (omega : KahlerBackground n M)
    (theta : ClosedRealOneOneForm n M)
    (phi u v : M → EReal) (hphi : IsModelPotential theta phi)
    (hu : RelativeFullMass theta phi u hphi)
    (hv : RelativeFullMass theta phi v hphi) (C : ℝ) :
    RelativeFullMass theta phi
        (rooftopEnvelope theta.val (fun x => min (u x) (v x + (C : EReal)))) hphi ∧
      rooftopEnvelope theta.val (fun x => min (u x) (v x + (C : EReal))) ≤ u ∧
      rooftopEnvelope theta.val (fun x => min (u x) (v x + (C : EReal))) ≤
        fun x => v x + (C : EReal) := by
  let w := rooftopEnvelope theta.val
    (fun x => min (u x) (v x + (C : EReal)))
  have hw : IsThetaPshPotential theta.val w :=
    isThetaPshPotential_rooftop_add_const_of_massCriterion omega theta phi u v hphi hu hv C
  have hobs : w ≤ u ∧ w ≤ fun x => v x + (C : EReal) :=
    rooftop_add_const_le_obstacles theta phi u v hphi hu hv C
  have hwphi : w ≤ phi := hobs.1.trans hu.le_reference
  have hlower : diagonalPotentialMass theta phi hphi.plurisubharmonic ≤
      diagonalPotentialMass theta w hw :=
    reference_mass_le_rooftop_add_const omega theta phi u v hphi hu hv C hw
  refine ⟨(relativeFullMass_iff theta phi w hphi hw).2
    ⟨hwphi, le_antisymm ?_ hlower⟩, hobs⟩
  change MixedMass.globalMixedMass (fun _ : Fin n => theta) (fun _ => w)
        (fun _ => hw.1) ≤
      MixedMass.globalMixedMass (fun _ : Fin n => theta) (fun _ => phi)
        (fun _ => hphi.plurisubharmonic.1)
  exact GlobalMixedMassMonotone.globalMixedMass_mono_of_isThetaPshPotential omega
    (fun _ => hw) (fun _ => hphi.plurisubharmonic)
    (fun _ => MoreSingularOn.of_le fun x _ => hwphi x)

/-- The unshifted rooftop `u ∧ v = P_θ(min(u, v))` of two relative full-mass potentials has
relative full mass and lies below both. -/
theorem relativeFullMass_rooftop (omega : KahlerBackground n M)
    (theta : ClosedRealOneOneForm n M)
    (phi u v : M → EReal) (hphi : IsModelPotential theta phi)
    (hu : RelativeFullMass theta phi u hphi)
    (hv : RelativeFullMass theta phi v hphi) :
    RelativeFullMass theta phi (rooftopEnvelope theta.val (fun x => min (u x) (v x))) hphi ∧
      rooftopEnvelope theta.val (fun x => min (u x) (v x)) ≤ u ∧
      rooftopEnvelope theta.val (fun x => min (u x) (v x)) ≤ v := by
  simpa using relativeFullMass_rooftop_add_const omega theta phi u v hphi hu hv 0

/-- **Xia, Proposition 3.1.21, `E¹` case, in every dimension.**  The rooftop of two relative
finite-energy potentials has relative finite energy. -/
theorem relativeFiniteEnergy_rooftop_of_kahler (omega : KahlerBackground n M)
    (theta : ClosedRealOneOneForm n M) (phi u v : M → EReal)
    (hphi : IsModelPotential theta phi)
    (hu : RelativeFiniteEnergy theta phi u hphi)
    (hv : RelativeFiniteEnergy theta phi v hphi) :
    RelativeFiniteEnergy theta phi
      (rooftopEnvelope theta.val (fun x => min (u x) (v x))) hphi := by
  obtain ⟨hwfull, hwu, hwv⟩ := relativeFullMass_rooftop omega theta phi u v hphi
    hu.fullMass hv.fullMass
  obtain ⟨hu', hufin⟩ := hu.2
  obtain ⟨hv', hvfin⟩ := hv.2
  refine ⟨hwfull, hwfull.plurisubharmonic, ?_⟩
  exact (relativeFiniteEnergyIntegral_rooftop_le omega theta hu' hv'
    hwfull.plurisubharmonic hwu hwv).trans_lt (ENNReal.add_lt_top.mpr ⟨hufin, hvfin⟩)

end Rooftops

/-! ### Regularized suprema, increasing families and the domination principle -/

section Suprema

/-- **Full mass under regularized suprema** (Xia SGPT, `xia-sgpt:page-0134`; blueprint
`trace:full-mass-supremum-closure`): for a nonempty family `(u_i)` in `E(X, θ; φ)`, the
upper-semicontinuous regularization of its supremum lies in `E(X, θ; φ)`.  Every dimension, no
connectedness. -/
theorem relativeFullMass_uscRegularization_iSup {ι : Type*} [Nonempty ι]
    (omega : KahlerBackground n M) {theta : ClosedRealOneOneForm n M} {phi : M → EReal}
    {hphi : IsModelPotential theta phi} (f : ι → M → EReal)
    (hf : ∀ i, RelativeFullMass theta phi (f i) hphi) :
    RelativeFullMass theta phi (uscRegularization (⨆ i, f i)) hphi := by
  have hphi0 : phi ≤ 0 := by
    rw [hphi.envelope_eq]
    exact singularityEnvelope_le_zero theta.val phi
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  have hle : f i₀ ≤ uscRegularization (⨆ i, f i) :=
    (le_iSup f i₀).trans (le_uscRegularization _)
  have hpsh : IsThetaPshPotential theta.val (uscRegularization (⨆ i, f i)) := by
    refine ⟨?_, (hf i₀).plurisubharmonic.2.mono hle⟩
    rw [← sSup_range]
    refine thetaPlurisubharmonic_uscRegularization_sSup
      (hf i₀).plurisubharmonic.1.hasSmoothLocalPotentials ⟨_, Set.mem_range_self i₀⟩ ?_ ?_
    · rintro _ ⟨i, rfl⟩
      exact (hf i).plurisubharmonic
    · rintro _ ⟨i, rfl⟩
      exact (hf i).le_reference.trans hphi0
  have hlephi : uscRegularization (⨆ i, f i) ≤ phi :=
    uscRegularization_le hphi.plurisubharmonic.1.quasiPlurisubharmonic.upperSemicontinuous
      (iSup_le fun i => (hf i).le_reference)
  exact relativeFullMass_of_between omega (hf i₀) hpsh hle hlephi

omit [MeasurableSpace M] [BorelSpace M] in
/-- A family of functions on a compact space that is locally uniformly bounded above is uniformly
bounded above. -/
theorem exists_uniform_upper_bound_of_locally {ι : Type*} (g : ι → M → EReal)
    (hbdd : ∀ x, ∃ U ∈ 𝓝 x, ∃ C : ℝ, ∀ j, ∀ y ∈ U, g j y ≤ (C : EReal)) :
    ∃ C : ℝ, ∀ j y, g j y ≤ (C : EReal) := by
  choose U hU C hC using hbdd
  obtain ⟨t, ht⟩ := isCompact_univ.elim_nhds_subcover U (fun x _ => hU x)
  obtain ⟨D, hD⟩ := (t.image C).exists_le
  refine ⟨D, fun j y => ?_⟩
  have hy : y ∈ ⋃ x ∈ t, U x := ht.2 (mem_univ y)
  simp only [mem_iUnion] at hy
  obtain ⟨x, hxt, hyx⟩ := hy
  exact (hC x j y hyx).trans (EReal.coe_le_coe_iff.mpr (hD (C x) (Finset.mem_image_of_mem C hxt)))

/-- Adding a finite constant commutes with suprema in `EReal`. -/
theorem iSup_add_coe {ι : Sort*} (f : ι → EReal) (c : ℝ) :
    (⨆ j, f j + (c : EReal)) = (⨆ j, f j) + (c : EReal) := by
  apply le_antisymm
  · exact iSup_le fun j => add_le_add (le_iSup f j) le_rfl
  · have h : (⨆ j, f j) ≤ (⨆ j, f j + (c : EReal)) + ((-c : ℝ) : EReal) := by
      refine iSup_le fun j => ?_
      calc f j = f j + (c : EReal) + ((-c : ℝ) : EReal) := by
            rw [add_assoc, ← EReal.coe_add, add_neg_cancel, EReal.coe_zero, add_zero]
        _ ≤ _ := add_le_add (le_iSup (fun j => f j + (c : EReal)) j) le_rfl
    calc (⨆ j, f j) + (c : EReal)
        ≤ (⨆ j, f j + (c : EReal)) + ((-c : ℝ) : EReal) + (c : EReal) := add_le_add h le_rfl
      _ = _ := by rw [add_assoc, ← EReal.coe_add, neg_add_cancel, EReal.coe_zero, add_zero]

omit [MeasurableSpace M] [BorelSpace M] in
/-- **Local `L¹` convergence of increasing theta-PSH families** (Demailly, CADG I.5.3; Xia SGPT,
`xia-sgpt:page-0135`; blueprint `trace:increasing-psh-l1`), real-parameter form: for a
nondecreasing family `(a_C)_{C ∈ ℝ}` of theta-PSH potentials, locally uniformly bounded above,
`a = sup*_C a_C` is theta-PSH and `a_C → a` chartwise locally in `L¹` as `C → +∞`.  (The proof
restricts to the cofinal sequence `C = j ∈ ℕ`.) -/
theorem manifoldL1LocallyTendsto_uscRegularization_iSup_real {theta : ClosedRealOneOneForm n M}
    {w : ℝ → M → EReal} (hw : ∀ C, IsThetaPshPotential theta.val (w C)) (hmono : Monotone w)
    (hbdd : ∀ x, ∃ U ∈ 𝓝 x, ∃ C : ℝ, ∀ j, ∀ y ∈ U, w j y ≤ (C : EReal)) :
    IsThetaPshPotential theta.val (uscRegularization (⨆ C, w C)) ∧
      ManifoldL1LocallyTendsto (n := n) w atTop (uscRegularization (⨆ C, w C)) := by
  obtain ⟨D, hD⟩ := exists_uniform_upper_bound_of_locally w hbdd
  -- shift down by `D`, so that the family is nonpositive
  let w' : ℝ → M → EReal := fun C x => w C x + ((-D : ℝ) : EReal)
  have hw' : ∀ C, IsThetaPshPotential theta.val (w' C) := fun C => (hw C).add_const (-D)
  have hw'0 : ∀ C, w' C ≤ 0 := by
    intro C x
    have h := add_le_add (hD C x) (le_refl ((-D : ℝ) : EReal))
    rwa [← EReal.coe_add, add_neg_cancel, EReal.coe_zero] at h
  have hmono' : Monotone w' := fun C C' hCC' x => add_le_add (hmono hCC' x) le_rfl
  have hback : ∀ C, w C = fun x => w' C x + (D : EReal) := by
    intro C
    funext x
    simp only [w']
    rw [add_assoc, ← EReal.coe_add, neg_add_cancel, EReal.coe_zero, add_zero]
  -- the regularized supremum of the shifted family, along the integers
  set a' := uscRegularization (⨆ j : ℕ, w' (j : ℝ)) with ha'
  have ha'psh : IsThetaPshPotential theta.val a' := by
    have hle : w' ((0 : ℕ) : ℝ) ≤ a' :=
      (le_iSup (fun j : ℕ => w' (j : ℝ)) 0).trans (le_uscRegularization _)
    refine ⟨?_, (hw' ((0 : ℕ) : ℝ)).2.mono hle⟩
    rw [ha', ← sSup_range]
    refine thetaPlurisubharmonic_uscRegularization_sSup
      (hw' 0).1.hasSmoothLocalPotentials ⟨_, Set.mem_range_self 0⟩ ?_ ?_
    · rintro _ ⟨j, rfl⟩
      exact hw' (j : ℝ)
    · rintro _ ⟨j, rfl⟩
      exact hw'0 (j : ℝ)
  have hlim' : ManifoldL1LocallyTendsto (n := n) w' atTop a' :=
    IncreasingThetaPshChartL1.manifoldL1LocallyTendsto_real_of_monotone_uscRegularization
      hw' hw'0 hmono' ha'psh ha'.symm
  -- undo the shift
  have heq : uscRegularization (⨆ C, w C) = fun x => a' x + (D : EReal) := by
    rw [iSup_real_eq_iSup_nat_of_monotone hmono, ha', ← uscRegularization_add_coe_const]
    congr 1
    funext x
    simp only [iSup_apply]
    rw [← iSup_add_coe]
    congr 1
    funext j
    rw [hback (j : ℝ)]
  refine ⟨heq ▸ ha'psh.add_const D, ?_⟩
  have h := hlim'.add_tendsto_const (c := fun _ : ℝ => D) (d := D) tendsto_const_nhds
  rw [heq]
  convert h using 1
  funext C
  exact hback C

omit [MeasurableSpace M] [BorelSpace M] in
/-- **Local `L¹` convergence of increasing theta-PSH sequences** (blueprint
`trace:increasing-psh-l1`), sequence form: for an increasing sequence `(a_j)` of theta-PSH
potentials, locally uniformly bounded above, `a = sup*_j a_j` is theta-PSH and `a_j → a` chartwise
locally in `L¹`. -/
theorem manifoldL1LocallyTendsto_uscRegularization_iSup {theta : ClosedRealOneOneForm n M}
    {g : ℕ → M → EReal} (hg : ∀ j, IsThetaPshPotential theta.val (g j)) (hmono : Monotone g)
    (hbdd : ∀ x, ∃ U ∈ 𝓝 x, ∃ C : ℝ, ∀ j, ∀ y ∈ U, g j y ≤ (C : EReal)) :
    IsThetaPshPotential theta.val (uscRegularization (⨆ j, g j)) ∧
      ManifoldL1LocallyTendsto (n := n) g atTop (uscRegularization (⨆ j, g j)) := by
  -- extend to the real parameter by `C ↦ g ⌊C⌋₊`
  let w : ℝ → M → EReal := fun C => g ⌊C⌋₊
  have hw : ∀ C, IsThetaPshPotential theta.val (w C) := fun C => hg _
  have hmono' : Monotone w := fun C C' hCC' => hmono (Nat.floor_le_floor hCC')
  have hbdd' : ∀ x, ∃ U ∈ 𝓝 x, ∃ C : ℝ, ∀ j, ∀ y ∈ U, w j y ≤ (C : EReal) := by
    intro x
    obtain ⟨U, hU, C, hC⟩ := hbdd x
    exact ⟨U, hU, C, fun j y hy => hC _ y hy⟩
  have hsup : (⨆ C, w C) = ⨆ j, g j := by
    rw [iSup_real_eq_iSup_nat_of_monotone hmono']
    simp only [w, Nat.floor_natCast]
  obtain ⟨hpsh, hlim⟩ := manifoldL1LocallyTendsto_uscRegularization_iSup_real hw hmono' hbdd'
  rw [hsup] at hpsh hlim
  refine ⟨hpsh, ?_⟩
  have h := hlim.comp tendsto_natCast_atTop_atTop
  convert h using 1
  funext j
  simp only [w, Nat.floor_natCast]

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] in
/-- For a nondecreasing family indexed by `ℝ`, the supremum over `C > 0` equals the supremum over
the integers. -/
theorem iSup_pos_real_eq_iSup_nat_of_monotone {β : Type*} [CompleteLattice β] {f : ℝ → β}
    (hf : Monotone f) : (⨆ C : Ioi (0 : ℝ), f C) = ⨆ j : ℕ, f (j : ℝ) := by
  refine le_antisymm (iSup_le fun C => ?_) (iSup_le fun j => ?_)
  · exact (hf (Nat.le_ceil (C : ℝ))).trans (le_iSup (fun j : ℕ => f (j : ℝ)) ⌈(C : ℝ)⌉₊)
  · have hpos : (0 : ℝ) < ((j + 1 : ℕ) : ℝ) := by positivity
    have hle : (j : ℝ) ≤ ((j + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ j
    exact (hf hle).trans (le_iSup (fun C : Ioi (0 : ℝ) => f C) ⟨((j + 1 : ℕ) : ℝ), hpos⟩)

variable [ConnectedSpace M] in
/-- **Relative domination principle, full-mass case** (Xia SGPT, Theorem 2.4.5,
`xia-sgpt:page-0087`--`page-0089`; blueprint `trace:relative-domination-principle`, last sentence):
for `u, v ∈ E(X, θ; φ)`, if `θ_u^n` does not charge `{u < v}`, then `v ≤ u`.  Every dimension. -/
theorem le_of_relativeFullMass_of_measure_lt_eq_zero (omega : KahlerBackground n M)
    {theta : ClosedRealOneOneForm n M} {phi u v : M → EReal} {hphi : IsModelPotential theta phi}
    (hu : RelativeFullMass theta phi u hphi) (hv : RelativeFullMass theta phi v hphi)
    (hzero : diagonalPotentialMeasure theta u hu.plurisubharmonic {x | u x < v x} = 0) :
    v ≤ u := by
  have humass : diagonalPotentialMass theta u hu.plurisubharmonic =
      diagonalPotentialMass theta phi hphi.plurisubharmonic :=
    ((relativeFullMass_iff theta phi u hphi hu.plurisubharmonic).1 hu).2
  have hvmass : diagonalPotentialMass theta v hv.plurisubharmonic =
      diagonalPotentialMass theta phi hphi.plurisubharmonic :=
    ((relativeFullMass_iff theta phi v hphi hv.plurisubharmonic).1 hv).2
  refine DominationPrinciple.le_of_diagonalPotentialMeasure_lt_eq_zero omega theta
    hu.plurisubharmonic hv.plurisubharmonic hphi.plurisubharmonic ?_ ?_
    (MoreSingularOn.of_le fun x _ => hu.le_reference x)
    (MoreSingularOn.of_le fun x _ => hv.le_reference x) humass hvmass hzero
  · change 0 < diagonalPotentialMass theta u hu.plurisubharmonic
    rw [humass]
    exact hphi.positive_mass
  · change 0 < diagonalPotentialMass theta v hv.plurisubharmonic
    rw [hvmass]
    exact hphi.positive_mass

variable [ConnectedSpace M] in
/-- **Contact mass for an increasing rooftop family** (Xia SGPT, `xia-sgpt:page-0101`,
`page-0134`--`page-0135`; blueprint `trace:full-mass-rooftop-contact`): for `u, v ∈ E(X, θ; φ)`, the
regularized supremum `γ = sup*_{C > 0} (v + C) ∧ u` lies in `E(X, θ; φ)` and `θ_γ^n` does not
charge `{γ < u}`.  (The blueprint assumes `v ≤ u`; it is not needed.) -/
theorem relativeFullMass_and_measure_lt_eq_zero_of_rooftops (omega : KahlerBackground n M)
    (theta : ClosedRealOneOneForm n M) (phi u v : M → EReal) (hphi : IsModelPotential theta phi)
    (hu : RelativeFullMass theta phi u hphi) (hv : RelativeFullMass theta phi v hphi) :
    RelativeFullMass theta phi
        (uscRegularization (⨆ C : Ioi (0 : ℝ), ShiftedRooftopLimit.shiftedRooftop theta u v C))
        hphi ∧
      ∀ hγ : IsThetaPshPotential theta.val
          (uscRegularization (⨆ C : Ioi (0 : ℝ), ShiftedRooftopLimit.shiftedRooftop theta u v C)),
        diagonalPotentialMeasure theta _ hγ
          {x | uscRegularization (⨆ C : Ioi (0 : ℝ),
            ShiftedRooftopLimit.shiftedRooftop theta u v C) x < u x} = 0 := by
  have heq : uscRegularization (⨆ C : Ioi (0 : ℝ), ShiftedRooftopLimit.shiftedRooftop theta u v C) =
      ShiftedRooftopLimit.shiftedRooftopLimit theta u v := by
    rw [iSup_pos_real_eq_iSup_nat_of_monotone
      (ShiftedRooftopLimit.shiftedRooftop_monotone theta u v)]
    rfl
  have hfull : RelativeFullMass theta phi
      (uscRegularization (⨆ C : Ioi (0 : ℝ), ShiftedRooftopLimit.shiftedRooftop theta u v C))
      hphi :=
    relativeFullMass_uscRegularization_iSup omega
      (fun C : Ioi (0 : ℝ) => ShiftedRooftopLimit.shiftedRooftop theta u v C)
      (fun C => (relativeFullMass_rooftop_add_const omega theta phi u v hphi hu hv C).1)
  refine ⟨hfull, fun hγ => ?_⟩
  have hw : ∀ C : ℝ, IsThetaPshPotential theta.val
      (ShiftedRooftopLimit.shiftedRooftop theta u v C) := fun C =>
    isThetaPshPotential_rooftop_add_const_of_massCriterion omega theta phi u v hphi hu hv C
  have heta : IsThetaPshPotential theta.val (ShiftedRooftopLimit.shiftedRooftopLimit theta u v) :=
    heq ▸ hγ
  have h :=
    ShiftedRooftopContactProof.diagonalPotentialMeasure_shiftedRooftopLimit_lt_eq_zero_of_family
      omega theta hu.plurisubharmonic hv.plurisubharmonic hw heta
  revert hγ
  rw [heq]
  intro hγ
  exact h

end Suprema

/-! ### Rooftop exhaustion -/

section Exhaustion

open ShiftedRooftopLimit

/-- The regularized limit of the shifted rooftops has the common mass of the family, in every
dimension (`ShiftedRooftopLimit.diagonalPotentialMass_shiftedRooftopLimit` without `0 < n`). -/
theorem diagonalPotentialMass_shiftedRooftopLimit
    (omega : KahlerBackground n M) (theta : ClosedRealOneOneForm n M)
    {u v : M → EReal} (V : ℝ≥0∞)
    (hw : ∀ C : ℝ, IsThetaPshPotential theta.val (shiftedRooftop theta u v C))
    (hle : ∀ C : ℝ, shiftedRooftop theta u v C ≤ u) (hu0 : u ≤ 0)
    (hmass : ∀ j : ℕ, diagonalPotentialMass theta
      (shiftedRooftop theta u v (j : ℝ)) (hw (j : ℝ)) = V) :
    diagonalPotentialMass theta (shiftedRooftopLimit theta u v)
      (isThetaPshPotential_shiftedRooftopLimit theta hw hle hu0) = V := by
  set eta := shiftedRooftopLimit theta u v with heta
  have hetapsh : IsThetaPshPotential theta.val eta :=
    isThetaPshPotential_shiftedRooftopLimit theta hw hle hu0
  have hmono : Monotone (fun j : ℕ => shiftedRooftop theta u v (j : ℝ)) :=
    fun j k hjk => shiftedRooftop_monotone theta u v (by exact_mod_cast hjk)
  refine le_antisymm ?_ ?_
  · have hbound := IncreasingLimitMass.diagonalPotentialMass_le_iSup_of_monotone
      (theta := theta) (fun j : ℕ => shiftedRooftop theta u v (j : ℝ))
      (fun j => hw (j : ℝ)) hmono hetapsh
    refine hbound.trans ?_
    exact iSup_le fun j => (hmass j).le
  · have hlower : diagonalPotentialMass theta
        (shiftedRooftop theta u v ((0 : ℕ) : ℝ)) (hw ((0 : ℕ) : ℝ)) ≤
        diagonalPotentialMass theta eta hetapsh :=
      GlobalMixedMassMonotone.globalMixedMass_mono_of_isThetaPshPotential omega
        (fun _ : Fin n => hw ((0 : ℕ) : ℝ))
        (fun _ => hetapsh)
        (fun _ => MoreSingularOn.of_le fun x _ =>
          shiftedRooftop_le_shiftedRooftopLimit theta u v 0 x)
    rw [← hmass 0]
    exact hlower

variable [ConnectedSpace M]

/-- **The shifted rooftops exhaust their first obstacle** (Xia SGPT, `xia-sgpt:page-0134`--
`page-0135`), in every dimension: if the regularized limit of `P_θ(min(u, v + j))` carries the model
mass, it equals `u` (`ShiftedRooftopContact.shiftedRooftopLimit_eq_of_mass` without `0 < n`). -/
theorem shiftedRooftopLimit_eq_of_mass
    (omega : KahlerBackground n M) (theta : ClosedRealOneOneForm n M)
    {phi u v : M → EReal}
    (hphi : IsThetaPshPotential theta.val phi) (hphi0 : phi ≤ 0)
    (hphipos : 0 < diagonalPotentialMass theta phi hphi)
    (hu : IsThetaPshPotential theta.val u) (huphi : u ≤ phi)
    (humass : diagonalPotentialMass theta u hu =
      diagonalPotentialMass theta phi hphi)
    (hv : IsThetaPshPotential theta.val v)
    (hw : ∀ C : ℝ, IsThetaPshPotential theta.val (shiftedRooftop theta u v C))
    (hwmass : ∀ j : ℕ, diagonalPotentialMass theta
      (shiftedRooftop theta u v (j : ℝ)) (hw (j : ℝ)) =
        diagonalPotentialMass theta phi hphi) :
    shiftedRooftopLimit theta u v = u := by
  have hu0 : u ≤ 0 := huphi.trans hphi0
  have hle : ∀ C : ℝ, shiftedRooftop theta u v C ≤ u := fun C =>
    (rooftopEnvelope_min_add_const_le_obstacles hu.1 hv.1 C).1
  have hetapsh : IsThetaPshPotential theta.val (shiftedRooftopLimit theta u v) :=
    isThetaPshPotential_shiftedRooftopLimit theta hw hle hu0
  have hetale : shiftedRooftopLimit theta u v ≤ u :=
    shiftedRooftopLimit_le theta hu hle
  have hetamass : diagonalPotentialMass theta (shiftedRooftopLimit theta u v)
      hetapsh = diagonalPotentialMass theta phi hphi :=
    diagonalPotentialMass_shiftedRooftopLimit omega theta _ hw hle hu0 hwmass
  have hetapos : HasPositivePotentialMass theta (shiftedRooftopLimit theta u v)
      hetapsh := by
    change 0 < diagonalPotentialMass theta (shiftedRooftopLimit theta u v) hetapsh
    rw [hetamass]
    exact hphipos
  have hupos : HasPositivePotentialMass theta u hu := by
    change 0 < diagonalPotentialMass theta u hu
    rw [humass]
    exact hphipos
  have hzero :=
    ShiftedRooftopContactProof.diagonalPotentialMeasure_shiftedRooftopLimit_lt_eq_zero_of_family
      omega theta hu hv hw hetapsh
  have hge : u ≤ shiftedRooftopLimit theta u v :=
    DominationPrinciple.le_of_diagonalPotentialMeasure_lt_eq_zero omega theta hetapsh hu hphi
      hetapos hupos
      (MoreSingularOn.of_le fun x _ => (hetale x).trans (huphi x))
      (MoreSingularOn.of_le fun x _ => huphi x)
      hetamass humass hzero
  exact le_antisymm hetale hge

/-- **Rooftop exhaustion, regularized-supremum form** (blueprint
`trace:full-mass-rooftop-exhaustion`): for `u, v ∈ E(X, θ; φ)` the regularized supremum of the
shifted rooftops `P_θ(min(u, v + j))`, `j ∈ ℕ`, is `u`. -/
theorem shiftedRooftopLimit_eq_of_relativeFullMass (omega : KahlerBackground n M)
    (theta : ClosedRealOneOneForm n M)
    (phi u v : M → EReal) (hphi : IsModelPotential theta phi)
    (hu : RelativeFullMass theta phi u hphi)
    (hv : RelativeFullMass theta phi v hphi) :
    shiftedRooftopLimit theta u v = u := by
  have hu' : IsThetaPshPotential theta.val u := hu.plurisubharmonic
  have hv' : IsThetaPshPotential theta.val v := hv.plurisubharmonic
  have hphi0 : phi ≤ 0 := by
    rw [hphi.envelope_eq]
    exact singularityEnvelope_le_zero theta.val phi
  have hw : ∀ C : ℝ, IsThetaPshPotential theta.val (shiftedRooftop theta u v C) := fun C =>
    isThetaPshPotential_rooftop_add_const_of_massCriterion omega theta phi u v hphi hu hv C
  have humass : diagonalPotentialMass theta u hu' =
      diagonalPotentialMass theta phi hphi.plurisubharmonic :=
    ((relativeFullMass_iff theta phi u hphi hu').1 hu).2
  have hwmass : ∀ j : ℕ, diagonalPotentialMass theta
      (shiftedRooftop theta u v (j : ℝ)) (hw (j : ℝ)) =
        diagonalPotentialMass theta phi hphi.plurisubharmonic := by
    intro j
    have hfull := (relativeFullMass_rooftop_add_const omega theta phi u v
      hphi hu hv (j : ℝ)).1
    exact ((relativeFullMass_iff theta phi _ hphi (hw (j : ℝ))).1 hfull).2
  exact shiftedRooftopLimit_eq_of_mass omega theta
    hphi.plurisubharmonic hphi0 hphi.positive_mass hu' hu.le_reference humass
    hv' hw hwmass

/-- **Rooftop exhaustion, the increase** (blueprint `trace:full-mass-rooftop-exhaustion`): for
`u, v ∈ E(X, θ; φ)` the rooftops `w_C = P_θ(min(u, v + C))` increase with `C`, and their
upper-semicontinuous regularized supremum over `C ∈ ℝ` is `u`. -/
theorem uscRegularization_iSup_shiftedRooftop_eq (omega : KahlerBackground n M)
    (theta : ClosedRealOneOneForm n M)
    (phi u v : M → EReal) (hphi : IsModelPotential theta phi)
    (hu : RelativeFullMass theta phi u hphi)
    (hv : RelativeFullMass theta phi v hphi) :
    Monotone (shiftedRooftop theta u v) ∧
      uscRegularization (⨆ C : ℝ, shiftedRooftop theta u v C) = u := by
  refine ⟨shiftedRooftop_monotone theta u v, ?_⟩
  rw [iSup_real_eq_iSup_nat_of_monotone (shiftedRooftop_monotone theta u v)]
  exact shiftedRooftopLimit_eq_of_relativeFullMass omega theta phi u v hphi hu hv

/-- **Rooftop exhaustion** (Xia SGPT, Proposition 3.1.24, `xia-sgpt:page-0134`--`page-0135`;
blueprint `trace:full-mass-rooftop-exhaustion`): for `u, v ∈ E(X, θ; φ)` the shifted rooftops
`P_θ(min(u, v + C))` converge to `u` in chart-local `L¹` as `C → +∞`.  Every dimension. -/
theorem relativeFullMass_rooftop_add_const_tendsto (omega : KahlerBackground n M)
    (theta : ClosedRealOneOneForm n M)
    (phi u v : M → EReal) (hphi : IsModelPotential theta phi)
    (hu : RelativeFullMass theta phi u hphi)
    (hv : RelativeFullMass theta phi v hphi) :
    ManifoldL1LocallyTendsto (n := n)
      (fun C : ℝ => rooftopEnvelope theta.val
        (fun x => min (u x) (v x + (C : EReal)))) atTop u := by
  have hu' : IsThetaPshPotential theta.val u := hu.plurisubharmonic
  have hphi0 : phi ≤ 0 := by
    rw [hphi.envelope_eq]
    exact singularityEnvelope_le_zero theta.val phi
  have hw : ∀ C : ℝ, IsThetaPshPotential theta.val (shiftedRooftop theta u v C) := fun C =>
    isThetaPshPotential_rooftop_add_const_of_massCriterion omega theta phi u v hphi hu hv C
  have hle : ∀ C : ℝ, shiftedRooftop theta u v C ≤ u := fun C =>
    (rooftop_add_const_le_obstacles theta phi u v hphi hu hv C).1
  exact
    IncreasingThetaPshChartL1.manifoldL1LocallyTendsto_real_of_monotone_uscRegularization
      hw (fun C => (hle C).trans (hu.le_reference.trans hphi0))
      (shiftedRooftop_monotone theta u v) hu'
      (shiftedRooftopLimit_eq_of_relativeFullMass omega theta phi u v hphi hu hv)

end Exhaustion

/-! ### Full-mass Perron geodesics -/

section Geodesics

variable [ConnectedSpace M]

omit [MeasurableSpace M] [BorelSpace M] [ConnectedSpace M] in
/-- **Perron interior from a common lower barrier** (Xia SGPT, Proposition 4.1.3,
`xia-sgpt:page-0150`--`page-0152`, and the first step of Proposition 4.2.1; blueprint
`trace:finite-geodesic-interior-barrier`).  Let `u₀, u₁` be theta-PSH on a nonempty compact
complex manifold and let `w` be theta-PSH with `w ≤ u₀` and `w ≤ u₁`.  Then the Perron envelope
`t ↦ G_t(u₀, u₁)` is a theta-subgeodesic on the open strip.  No mass, model potential, dimension or
connectedness hypothesis. -/
theorem finiteGeodesic_isSubgeodesicInterior_of_common_lower [Nonempty M]
    {θ : SmoothRealForm n M 2} {u₀ u₁ w : M → EReal} (hu₀ : IsThetaPshPotential θ u₀)
    (hu₁ : IsThetaPshPotential θ u₁) (hw : IsThetaPshPotential θ w) (hw₀ : w ≤ u₀) (hw₁ : w ≤ u₁) :
    IsSubgeodesicInterior θ (finiteGeodesic θ u₀ u₁) := by
  have hlocal : HasSmoothLocalPotentials θ := hu₀.1.hasSmoothLocalPotentials
  have hne := finiteGeodesicCompetitors_nonempty_of_common_lower θ u₀ u₁ w hw hw₀ hw₁
  obtain ⟨C, hC⟩ := finiteGeodesic_uniformlyBoundedAbove θ u₀ u₁ hu₀ hu₁
  refine ⟨fun t ht => isThetaPshPotential_finiteGeodesic_of_bounded hlocal hne ht
    (hC t ht) hw hw₀ hw₁, ?_⟩
  intro e z hz
  obtain ⟨W, rho, hzW, hrho⟩ := hlocal e z hz
  refine ⟨W, rho, hzW, hrho, ?_⟩
  intro p hp
  refine (SubgeodesicChartPotential.plurisubharmonicOn_uscRegularization_sSup_image e hrho hne
    (finiteGeodesicCompetitors_chart_locallyUniformlyBoundedAbove θ u₀ u₁ hu₀ hu₁ e hrho)
    p hp).congr ?_
  filter_upwards [(isOpen_geodesicChartDomain hrho.1).mem_nhds hp] with q hq
  exact (subgeodesicChartFunction_finiteGeodesic_eq_strip_envelope hu₀ hu₁ e hrho hq).symm

/-- **Perron interior for full-mass endpoints** (Xia SGPT, Propositions 4.1.3 and 4.2.1; blueprint
`trace:finite-geodesic-full-mass-interior`): for `u₀, u₁ ∈ E(X, θ; φ)` the Perron envelope is a
theta-subgeodesic on the open strip.  The rooftop `u₀ ∧ u₁` is a common theta-PSH lower barrier
(`isThetaPshPotential_rooftop_add_const_of_massCriterion`, obstacle recovery).  No dimension or
bigness hypothesis. -/
theorem finiteGeodesic_isSubgeodesicInterior_of_relativeFullMass
    (omega : KahlerBackground n M) (theta : ClosedRealOneOneForm n M)
    (phi u₀ u₁ : M → EReal) (hphi : IsModelPotential theta phi)
    (hu₀ : RelativeFullMass theta phi u₀ hphi)
    (hu₁ : RelativeFullMass theta phi u₁ hphi) :
    IsSubgeodesicInterior theta.val (finiteGeodesic theta.val u₀ u₁) := by
  have hw := isThetaPshPotential_rooftop_add_const_of_massCriterion omega theta phi u₀ u₁ hphi
    hu₀ hu₁ 0
  obtain ⟨hw₀, hw₁⟩ := rooftop_add_const_le_obstacles theta phi u₀ u₁ hphi hu₀ hu₁ 0
  exact finiteGeodesic_isSubgeodesicInterior_of_common_lower hu₀.plurisubharmonic
    hu₁.plurisubharmonic hw hw₀ (fun x => by simpa using hw₁ x)

/-- **Left endpoint recovery** (blueprint `trace:finite-geodesic-rooftop-truncation`): for
`u₀, u₁ ∈ E(X, θ; φ)`, `G_t(u₀, u₁) → u₀` in chart-local `L¹` as `t → 0+`. -/
theorem finiteGeodesic_tendsto_left_of_relativeFullMass
    (omega : KahlerBackground n M) (theta : ClosedRealOneOneForm n M)
    (phi u₀ u₁ : M → EReal) (hphi : IsModelPotential theta phi)
    (hu₀ : RelativeFullMass theta phi u₀ hphi)
    (hu₁ : RelativeFullMass theta phi u₁ hphi) :
    ManifoldL1LocallyTendsto (n := n) (finiteGeodesic theta.val u₀ u₁)
      (𝓝[>] (0 : ℝ)) u₀ := by
  let w : ℝ → M → EReal := fun C => rooftopEnvelope theta.val
    (fun x => min (u₀ x) (u₁ x + (C : EReal)))
  apply finiteGeodesic_tendsto_left_of_rooftop_exhaustion
      hu₀.plurisubharmonic hu₁.plurisubharmonic
      (w := w)
  · intro C _
    exact (relativeFullMass_rooftop_add_const omega theta phi u₀ u₁
      hphi hu₀ hu₁ C).1.plurisubharmonic
  · intro C _
    exact (relativeFullMass_rooftop_add_const omega theta phi u₀ u₁
      hphi hu₀ hu₁ C).2.1
  · intro C _
    exact (relativeFullMass_rooftop_add_const omega theta phi u₀ u₁
      hphi hu₀ hu₁ C).2.2
  · simpa only [w] using relativeFullMass_rooftop_add_const_tendsto
      omega theta phi u₀ u₁ hphi hu₀ hu₁

/-- **Right endpoint recovery**: for `u₀, u₁ ∈ E(X, θ; φ)`, `G_t(u₀, u₁) → u₁` in chart-local `L¹`
as `t → 1-` (time reversal of the left limit). -/
theorem finiteGeodesic_tendsto_right_of_relativeFullMass
    (omega : KahlerBackground n M) (theta : ClosedRealOneOneForm n M)
    (phi u₀ u₁ : M → EReal) (hphi : IsModelPotential theta phi)
    (hu₀ : RelativeFullMass theta phi u₀ hphi)
    (hu₁ : RelativeFullMass theta phi u₁ hphi) :
    ManifoldL1LocallyTendsto (n := n) (finiteGeodesic theta.val u₀ u₁)
      (𝓝[<] (1 : ℝ)) u₁ := by
  have hleft := finiteGeodesic_tendsto_left_of_relativeFullMass
    omega theta phi u₁ u₀ hphi hu₁ hu₀
  have hreversed := hleft.comp tendsto_one_sub_nhdsLT_one
  apply ManifoldL1LocallyTendsto.congr (hu := hreversed)
  intro t
  rw [finiteGeodesic_timeReversal]
  congr 2
  ring

/-- **Full-mass Perron geodesics** (Xia SGPT, Proposition 4.2.1, full-mass case; blueprint
`trace:finite-geodesic-properties`): for `u₀, u₁ ∈ E(X, θ; φ)` the Perron envelope is a subgeodesic
from `u₀` to `u₁`. -/
theorem finiteGeodesic_isSubgeodesicFrom_of_relativeFullMass
    (omega : KahlerBackground n M) (theta : ClosedRealOneOneForm n M)
    (phi u₀ u₁ : M → EReal) (hphi : IsModelPotential theta phi)
    (hu₀ : RelativeFullMass theta phi u₀ hphi)
    (hu₁ : RelativeFullMass theta phi u₁ hphi) :
    IsSubgeodesicFrom theta.val (finiteGeodesic theta.val u₀ u₁) u₀ u₁ :=
  ⟨hu₀.plurisubharmonic, hu₁.plurisubharmonic,
    finiteGeodesic_isSubgeodesicInterior_of_relativeFullMass
      omega theta phi u₀ u₁ hphi hu₀ hu₁,
    finiteGeodesic_tendsto_left_of_relativeFullMass
      omega theta phi u₀ u₁ hphi hu₀ hu₁,
    finiteGeodesic_tendsto_right_of_relativeFullMass
      omega theta phi u₀ u₁ hphi hu₀ hu₁⟩

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M] in
/-- **The upper half of the sandwich** (blueprint `trace:finite-geodesic-full-mass-slices`): for
`u₀, u₁ ≤ φ` theta-PSH and `t ∈ (0, 1)`, `G_t(u₀, u₁) ≤ (1 - t) u₀ + t u₁ ≤ φ`.  No mass,
dimension, connectedness or bigness hypothesis. -/
theorem finiteGeodesic_le_eRealChord_le_reference (theta : ClosedRealOneOneForm n M)
    (phi u₀ u₁ : M → EReal) (hphi : IsThetaPshPotential theta.val phi)
    (hu₀ : IsThetaPshPotential theta.val u₀) (hu₁ : IsThetaPshPotential theta.val u₁)
    (hu₀phi : u₀ ≤ phi) (hu₁phi : u₁ ≤ phi) (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
    finiteGeodesic theta.val u₀ u₁ t ≤ (fun x => eRealChord (u₀ x) (u₁ x) t) ∧
      (fun x => eRealChord (u₀ x) (u₁ x) t) ≤ phi := by
  refine ⟨finiteGeodesic_le_eRealChord hu₀ hu₁ ht, ?_⟩
  intro x
  refine (eRealChord_mono (hu₀phi x) (hu₁phi x) ht.1.le ht.2.le).trans_eq ?_
  induction hpx : phi x using EReal.rec with
  | bot =>
      simp only [eRealChord]
      rw [EReal.coe_mul_bot_of_pos (sub_pos.mpr ht.2),
        EReal.coe_mul_bot_of_pos ht.1, EReal.bot_add]
  | coe r =>
      simp only [eRealChord]
      norm_cast
      ring
  | top =>
      exact False.elim (hphi.quasiPshPotential.1.ne_top x hpx)

omit [BorelSpace M] [ConnectedSpace M] in
/-- Perron slices between relative full-mass endpoints stay below the model potential (blueprint
`trace:finite-geodesic-below-reference`), with no dimension, connectedness or bigness hypothesis. -/
theorem finiteGeodesic_le_reference_of_relativeFullMass
    (theta : ClosedRealOneOneForm n M)
    (phi u₀ u₁ : M → EReal) (hphi : IsModelPotential theta phi)
    (hu₀ : RelativeFullMass theta phi u₀ hphi)
    (hu₁ : RelativeFullMass theta phi u₁ hphi)
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
    finiteGeodesic theta.val u₀ u₁ t ≤ phi :=
  let h := finiteGeodesic_le_eRealChord_le_reference theta phi u₀ u₁ hphi.plurisubharmonic
    hu₀.plurisubharmonic hu₁.plurisubharmonic hu₀.le_reference hu₁.le_reference t ht
  h.1.trans h.2

/-- **The lower half of the sandwich** (blueprint `trace:finite-geodesic-full-mass-slices`): for
`u₀, u₁ ∈ E(X, θ; φ)` the rooftop `u₀ ∧ u₁ = P_θ(min(u₀, u₁))` lies below every Perron slice. -/
theorem rooftop_le_finiteGeodesic (omega : KahlerBackground n M)
    (theta : ClosedRealOneOneForm n M)
    (phi u₀ u₁ : M → EReal) (hphi : IsModelPotential theta phi)
    (hu₀ : RelativeFullMass theta phi u₀ hphi)
    (hu₁ : RelativeFullMass theta phi u₁ hphi) (t : ℝ) :
    rooftopEnvelope theta.val (fun x => min (u₀ x) (u₁ x)) ≤ finiteGeodesic theta.val u₀ u₁ t := by
  obtain ⟨hw, hw₀, hw₁⟩ := relativeFullMass_rooftop omega theta phi u₀ u₁ hphi hu₀ hu₁
  exact le_finiteGeodesic_of_le_endpoints hw.plurisubharmonic hw₀ hw₁ t

/-- **Full-mass slices** (Xia SGPT, Proposition 4.2.1; blueprint
`trace:finite-geodesic-full-mass-slices`): for `u₀, u₁ ∈ E(X, θ; φ)` and `t ∈ (0, 1)`,
`G_t(u₀, u₁) ∈ E(X, θ; φ)`.  Every dimension, no bigness hypothesis. -/
theorem relativeFullMass_finiteGeodesic
    (omega : KahlerBackground n M) (theta : ClosedRealOneOneForm n M)
    (phi u₀ u₁ : M → EReal) (hphi : IsModelPotential theta phi)
    (hu₀ : RelativeFullMass theta phi u₀ hphi)
    (hu₁ : RelativeFullMass theta phi u₁ hphi)
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
    RelativeFullMass theta phi (finiteGeodesic theta.val u₀ u₁ t) hphi := by
  obtain ⟨hw, _, _⟩ := relativeFullMass_rooftop omega theta phi u₀ u₁ hphi hu₀ hu₁
  exact relativeFullMass_of_between omega hw
    ((finiteGeodesic_isSubgeodesicInterior_of_relativeFullMass
      omega theta phi u₀ u₁ hphi hu₀ hu₁).thetaPshPotential ht)
    (rooftop_le_finiteGeodesic omega theta phi u₀ u₁ hphi hu₀ hu₁ t)
    (finiteGeodesic_le_reference_of_relativeFullMass theta phi u₀ u₁ hphi hu₀ hu₁ t ht)

/-- **The full-mass sandwich for Perron slices** (blueprint
`trace:finite-geodesic-full-mass-slices`): for `u₀, u₁ ∈ E(X, θ; φ)` and `t ∈ (0, 1)`,
`u₀ ∧ u₁ ≤ G_t(u₀, u₁) ≤ (1 - t) u₀ + t u₁ ≤ φ` and `G_t(u₀, u₁) ∈ E(X, θ; φ)`. -/
theorem finiteGeodesic_fullMass_sandwich
    (omega : KahlerBackground n M) (theta : ClosedRealOneOneForm n M)
    (phi u₀ u₁ : M → EReal) (hphi : IsModelPotential theta phi)
    (hu₀ : RelativeFullMass theta phi u₀ hphi)
    (hu₁ : RelativeFullMass theta phi u₁ hphi)
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
    rooftopEnvelope theta.val (fun x => min (u₀ x) (u₁ x)) ≤ finiteGeodesic theta.val u₀ u₁ t ∧
      finiteGeodesic theta.val u₀ u₁ t ≤ (fun x => eRealChord (u₀ x) (u₁ x) t) ∧
      (fun x => eRealChord (u₀ x) (u₁ x) t) ≤ phi ∧
      RelativeFullMass theta phi (finiteGeodesic theta.val u₀ u₁ t) hphi :=
  ⟨rooftop_le_finiteGeodesic omega theta phi u₀ u₁ hphi hu₀ hu₁ t,
    (finiteGeodesic_le_eRealChord_le_reference theta phi u₀ u₁ hphi.plurisubharmonic
      hu₀.plurisubharmonic hu₁.plurisubharmonic hu₀.le_reference hu₁.le_reference t ht).1,
    (finiteGeodesic_le_eRealChord_le_reference theta phi u₀ u₁ hphi.plurisubharmonic
      hu₀.plurisubharmonic hu₁.plurisubharmonic hu₀.le_reference hu₁.le_reference t ht).2,
    relativeFullMass_finiteGeodesic omega theta phi u₀ u₁ hphi hu₀ hu₁ t ht⟩

/-! ### Finite energy -/

/-- Relative finite-energy endpoints give a subgeodesic from `u₀` to `u₁` (blueprint
`trace:finite-geodesic-e1`). -/
theorem finiteGeodesic_isSubgeodesicFrom_of_relativeFiniteEnergy
    (omega : KahlerBackground n M) (theta : ClosedRealOneOneForm n M)
    (phi u₀ u₁ : M → EReal) (hphi : IsModelPotential theta phi)
    (hu₀ : RelativeFiniteEnergy theta phi u₀ hphi)
    (hu₁ : RelativeFiniteEnergy theta phi u₁ hphi) :
    IsSubgeodesicFrom theta.val (finiteGeodesic theta.val u₀ u₁) u₀ u₁ :=
  finiteGeodesic_isSubgeodesicFrom_of_relativeFullMass omega theta
    phi u₀ u₁ hphi hu₀.fullMass hu₁.fullMass

/-- **Xia, Proposition 4.2.1, finite-energy case** (blueprint `trace:finite-geodesic-e1`): every
interior Perron slice between relative finite-energy endpoints has relative finite energy.  The
rooftop of the endpoints is in `E¹` (`relativeFiniteEnergy_rooftop_of_kahler`) and lies below the
slice, which lies below `φ`; upward closure (`relativeFiniteEnergy_of_between_of_kahler`)
concludes. -/
theorem relativeFiniteEnergy_finiteGeodesic
    (omega : KahlerBackground n M) (theta : ClosedRealOneOneForm n M)
    (phi u₀ u₁ : M → EReal) (hphi : IsModelPotential theta phi)
    (hu₀ : RelativeFiniteEnergy theta phi u₀ hphi)
    (hu₁ : RelativeFiniteEnergy theta phi u₁ hphi)
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
    RelativeFiniteEnergy theta phi (finiteGeodesic theta.val u₀ u₁ t) hphi := by
  have hw := relativeFiniteEnergy_rooftop_of_kahler omega theta phi u₀ u₁ hphi hu₀ hu₁
  have hslice : IsThetaPshPotential theta.val (finiteGeodesic theta.val u₀ u₁ t) :=
    (finiteGeodesic_isSubgeodesicInterior_of_relativeFullMass
      omega theta phi u₀ u₁ hphi hu₀.fullMass hu₁.fullMass).thetaPshPotential ht
  exact relativeFiniteEnergy_of_between_of_kahler omega hw hslice
    (rooftop_le_finiteGeodesic omega theta phi u₀ u₁ hphi hu₀.fullMass hu₁.fullMass t)
    (finiteGeodesic_le_reference_of_relativeFullMass theta phi u₀ u₁ hphi
      hu₀.fullMass hu₁.fullMass t ht)

/-! ### Bounded singularity type -/

/-- Bounded-singularity endpoints give a subgeodesic from `u₀` to `u₁` (blueprint
`trace:finite-geodesic-einfinity`).  The endpoints are shifted into `E(X, θ; φ)`, the interior
property is transported back by affine covariance, and the endpoint limits are the ordered-endpoint
squeeze. -/
theorem finiteGeodesic_isSubgeodesicFrom_of_relativeEInfinity
    (omega : KahlerBackground n M) (theta : ClosedRealOneOneForm n M)
    (phi u₀ u₁ : M → EReal) (hphi : IsModelPotential theta phi)
    (hu₀ : RelativeEInfinity theta phi u₀)
    (hu₁ : RelativeEInfinity theta phi u₁) :
    IsSubgeodesicFrom theta.val (finiteGeodesic theta.val u₀ u₁) u₀ u₁ := by
  rcases hu₀.sameSingularityType.1 with ⟨C₀, hC₀⟩
  rcases hu₀.sameSingularityType.2 with ⟨D₀, hD₀⟩
  rcases hu₁.sameSingularityType.1 with ⟨C₁, hC₁⟩
  rcases hu₁.sameSingularityType.2 with ⟨D₁, hD₁⟩
  let B : ℝ := -C₀
  let A : ℝ := C₀ - C₁
  let v₀ : M → EReal := fun x => u₀ x + (B : EReal)
  let v₁ : M → EReal := fun x => u₁ x + ((A + B : ℝ) : EReal)
  have hAB : A + B = -C₁ := by
    dsimp only [A, B]
    ring
  have hv₀psh : IsThetaPshPotential theta.val v₀ := by
    exact hu₀.plurisubharmonic.add_const B
  have hv₁psh : IsThetaPshPotential theta.val v₁ := by
    exact hu₁.plurisubharmonic.add_const (A + B)
  have hv₀phi : SameSingularityTypeOn v₀ phi univ := by
    exact (sameSingularityTypeOn_add_const u₀ univ B).trans
      hu₀.sameSingularityType
  have hv₁phi : SameSingularityTypeOn v₁ phi univ := by
    exact (sameSingularityTypeOn_add_const u₁ univ (A + B)).trans
      hu₁.sameSingularityType
  have hv₀le : v₀ ≤ phi := by
    intro x
    apply (EReal.addLECancellable_coe C₀).add_le_add_iff_right.mp
    calc
      v₀ x + (C₀ : EReal) = u₀ x := by
        dsimp only [v₀, B]
        rw [add_assoc, ← EReal.coe_add]
        simp
      _ ≤ phi x + (C₀ : EReal) := hC₀ x (mem_univ x)
  have hv₁le : v₁ ≤ phi := by
    intro x
    apply (EReal.addLECancellable_coe C₁).add_le_add_iff_right.mp
    calc
      v₁ x + (C₁ : EReal) = u₁ x := by
        dsimp only [v₁]
        rw [hAB, add_assoc, ← EReal.coe_add]
        simp
      _ ≤ phi x + (C₁ : EReal) := hC₁ x (mem_univ x)
  have hphiFull : RelativeFullMass theta phi phi hphi :=
    ⟨hphi.plurisubharmonic, le_rfl, rfl⟩
  have hv₀Full : RelativeFullMass theta phi v₀ hphi :=
    relativeFullMass_of_singularity_between omega hphiFull hv₀psh hv₀phi.2
      hv₀phi.1 hv₀le
  have hv₁Full : RelativeFullMass theta phi v₁ hphi :=
    relativeFullMass_of_singularity_between omega hphiFull hv₁psh hv₁phi.2
      hv₁phi.1 hv₁le
  have hinteriorShifted :=
    finiteGeodesic_isSubgeodesicInterior_of_relativeFullMass
      omega theta phi v₀ v₁ hphi hv₀Full hv₁Full
  have hcov : finiteGeodesic theta.val v₀ v₁ =
      affineTranslatedCurve (finiteGeodesic theta.val u₀ u₁) A B := by
    funext t
    exact finiteGeodesic_affineCovariance theta.val u₀ u₁ A B t
  have hinterior := hinteriorShifted.affineTranslated (-A) (-B)
  have hcurve : affineTranslatedCurve
      (finiteGeodesic theta.val v₀ v₁) (-A) (-B) =
      finiteGeodesic theta.val u₀ u₁ := by
    rw [hcov, affineTranslatedCurve_inverse]
  rw [hcurve] at hinterior
  have hu₀le : u₀ ≤ fun x => u₁ x + ((D₁ + C₀ : ℝ) : EReal) := by
    intro x
    calc
      u₀ x ≤ phi x + (C₀ : EReal) := hC₀ x (mem_univ x)
      _ ≤ (u₁ x + (D₁ : EReal)) + (C₀ : EReal) :=
        add_le_add (hD₁ x (mem_univ x)) le_rfl
      _ = u₁ x + ((D₁ + C₀ : ℝ) : EReal) := by
        rw [add_assoc, ← EReal.coe_add]
  have hleftShifted := finiteGeodesic_tendsto_left_of_le
    hu₀.plurisubharmonic
    (hu₁.plurisubharmonic.add_const (D₁ + C₀)) hu₀le
  have hleftCorrected := hleftShifted.add_tendsto_const
    (c := fun t : ℝ => -((D₁ + C₀) * t)) (d := 0) (by
      have hcont : Continuous (fun t : ℝ => -((D₁ + C₀) * t)) := by
        fun_prop
      simpa using tendsto_nhdsWithin_of_tendsto_nhds
        (hcont.tendsto (0 : ℝ)))
  have hleft : ManifoldL1LocallyTendsto (n := n)
      (finiteGeodesic theta.val u₀ u₁) (𝓝[>] (0 : ℝ)) u₀ := by
    apply ManifoldL1LocallyTendsto.congr (hu := by
      simpa only [EReal.coe_zero, add_zero] using hleftCorrected)
    intro t
    funext x
    have hcovLeft : finiteGeodesic theta.val u₀
        (fun y => u₁ y + ((D₁ + C₀ : ℝ) : EReal)) t x =
        finiteGeodesic theta.val u₀ u₁ t x +
          (((D₁ + C₀) * t : ℝ) : EReal) := by
      have hu₀zero : (fun y => u₀ y + ((0 : ℝ) : EReal)) = u₀ := by
        funext y
        simp
      have hcov := congrFun
        (finiteGeodesic_affineCovariance theta.val u₀ u₁
          (D₁ + C₀) 0 t) x
      rw [hu₀zero] at hcov
      simpa only [add_zero] using hcov
    rw [hcovLeft]
    rw [add_assoc, ← EReal.coe_add]
    have hcancel : (D₁ + C₀) * t + -((D₁ + C₀) * t) = 0 := by ring
    rw [hcancel, EReal.coe_zero, add_zero]
  have hu₁le : u₁ ≤ fun x => u₀ x + ((D₀ + C₁ : ℝ) : EReal) := by
    intro x
    calc
      u₁ x ≤ phi x + (C₁ : EReal) := hC₁ x (mem_univ x)
      _ ≤ (u₀ x + (D₀ : EReal)) + (C₁ : EReal) :=
        add_le_add (hD₀ x (mem_univ x)) le_rfl
      _ = u₀ x + ((D₀ + C₁ : ℝ) : EReal) := by
        rw [add_assoc, ← EReal.coe_add]
  have hrightShifted := finiteGeodesic_tendsto_left_of_le
    hu₁.plurisubharmonic
    (hu₀.plurisubharmonic.add_const (D₀ + C₁)) hu₁le
  have hrightCorrected := hrightShifted.add_tendsto_const
    (c := fun t : ℝ => -((D₀ + C₁) * t)) (d := 0) (by
      have hcont : Continuous (fun t : ℝ => -((D₀ + C₁) * t)) := by
        fun_prop
      simpa using tendsto_nhdsWithin_of_tendsto_nhds
        (hcont.tendsto (0 : ℝ)))
  have hswapped : ManifoldL1LocallyTendsto (n := n)
      (finiteGeodesic theta.val u₁ u₀) (𝓝[>] (0 : ℝ)) u₁ := by
    apply ManifoldL1LocallyTendsto.congr (hu := by
      simpa only [EReal.coe_zero, add_zero] using hrightCorrected)
    intro t
    funext x
    have hcovRight : finiteGeodesic theta.val u₁
        (fun y => u₀ y + ((D₀ + C₁ : ℝ) : EReal)) t x =
        finiteGeodesic theta.val u₁ u₀ t x +
          (((D₀ + C₁) * t : ℝ) : EReal) := by
      have hu₁zero : (fun y => u₁ y + ((0 : ℝ) : EReal)) = u₁ := by
        funext y
        simp
      have hcov := congrFun
        (finiteGeodesic_affineCovariance theta.val u₁ u₀
          (D₀ + C₁) 0 t) x
      rw [hu₁zero] at hcov
      simpa only [add_zero] using hcov
    rw [hcovRight]
    rw [add_assoc, ← EReal.coe_add]
    have hcancel : (D₀ + C₁) * t + -((D₀ + C₁) * t) = 0 := by ring
    rw [hcancel, EReal.coe_zero, add_zero]
  have hrightReversed := hswapped.comp tendsto_one_sub_nhdsLT_one
  have hright : ManifoldL1LocallyTendsto (n := n)
      (finiteGeodesic theta.val u₀ u₁) (𝓝[<] (1 : ℝ)) u₁ := by
    apply ManifoldL1LocallyTendsto.congr (hu := hrightReversed)
    intro t
    rw [finiteGeodesic_timeReversal]
    congr 2
    ring
  exact ⟨hu₀.plurisubharmonic, hu₁.plurisubharmonic, hinterior,
    hleft, hright⟩

/-- **Bounded-singularity slices** (Xia SGPT, Proposition 4.2.1; blueprint
`trace:finite-geodesic-einfinity`): every interior Perron slice between endpoints of the bounded
singularity type of `φ` has that singularity type.  Upper bound: the endpoint chord; lower bound:
the constant competitor `φ - D`. -/
theorem relativeEInfinity_finiteGeodesic
    (omega : KahlerBackground n M) (theta : ClosedRealOneOneForm n M)
    (phi u₀ u₁ : M → EReal) (hphi : IsModelPotential theta phi)
    (hu₀ : RelativeEInfinity theta phi u₀)
    (hu₁ : RelativeEInfinity theta phi u₁)
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
    RelativeEInfinity theta phi (finiteGeodesic theta.val u₀ u₁ t) := by
  rcases hu₀.sameSingularityType.1 with ⟨C₀, hC₀⟩
  rcases hu₀.sameSingularityType.2 with ⟨D₀, hD₀⟩
  rcases hu₁.sameSingularityType.1 with ⟨C₁, hC₁⟩
  rcases hu₁.sameSingularityType.2 with ⟨D₁, hD₁⟩
  have hslicePsh :=
    (finiteGeodesic_isSubgeodesicFrom_of_relativeEInfinity
      omega theta phi u₀ u₁ hphi hu₀ hu₁).interior.thetaPshPotential ht
  refine ⟨hslicePsh, ?_⟩
  constructor
  · let C : ℝ := max C₀ C₁
    refine ⟨C, fun x _ => ?_⟩
    have hu₀upper : u₀ x ≤ phi x + (C : EReal) := by
      exact (hC₀ x (mem_univ x)).trans
        (add_le_add le_rfl (by exact_mod_cast le_max_left C₀ C₁))
    have hu₁upper : u₁ x ≤ phi x + (C : EReal) := by
      exact (hC₁ x (mem_univ x)).trans
        (add_le_add le_rfl (by exact_mod_cast le_max_right C₀ C₁))
    refine (finiteGeodesic_le_eRealChord hu₀.plurisubharmonic
      hu₁.plurisubharmonic ht x).trans
      ((eRealChord_mono hu₀upper hu₁upper ht.1.le ht.2.le).trans_eq ?_)
    induction hpx : phi x using EReal.rec with
    | bot =>
        simp only [eRealChord, EReal.bot_add]
        rw [EReal.coe_mul_bot_of_pos (sub_pos.mpr ht.2),
          EReal.coe_mul_bot_of_pos ht.1, EReal.bot_add]
    | coe r =>
        simp only [eRealChord, ← EReal.coe_add, ← EReal.coe_mul]
        norm_cast
        ring
    | top =>
        exact False.elim
          (hphi.plurisubharmonic.quasiPshPotential.1.ne_top x hpx)
  · let D : ℝ := max D₀ D₁
    let w : M → EReal := fun x => phi x + ((-D : ℝ) : EReal)
    have hwpsh : IsThetaPshPotential theta.val w :=
      hphi.plurisubharmonic.add_const (-D)
    have hwu₀ : w ≤ u₀ := by
      intro x
      apply (EReal.addLECancellable_coe D).add_le_add_iff_right.mp
      calc
        w x + (D : EReal) = phi x := by
          dsimp only [w]
          rw [add_assoc, ← EReal.coe_add]
          simp
        _ ≤ u₀ x + (D₀ : EReal) := hD₀ x (mem_univ x)
        _ ≤ u₀ x + (D : EReal) :=
          add_le_add le_rfl (by exact_mod_cast le_max_left D₀ D₁)
    have hwu₁ : w ≤ u₁ := by
      intro x
      apply (EReal.addLECancellable_coe D).add_le_add_iff_right.mp
      calc
        w x + (D : EReal) = phi x := by
          dsimp only [w]
          rw [add_assoc, ← EReal.coe_add]
          simp
        _ ≤ u₁ x + (D₁ : EReal) := hD₁ x (mem_univ x)
        _ ≤ u₁ x + (D : EReal) :=
          add_le_add le_rfl (by exact_mod_cast le_max_right D₀ D₁)
    have hlower := le_finiteGeodesic_of_le_endpoints hwpsh hwu₀ hwu₁ t
    refine ⟨D, fun x _ => ?_⟩
    have hadd :=
      (EReal.addLECancellable_coe D).add_le_add_iff_right.mpr (hlower x)
    calc
      phi x = w x + (D : EReal) := by
        dsimp only [w]
        rw [add_assoc, ← EReal.coe_add]
        simp
      _ ≤ finiteGeodesic theta.val u₀ u₁ t x + (D : EReal) := hadd

end Geodesics

end

end SGPT.Foundations.Analysis.Pending.FiniteGeodesicsFullMassAnyDim
