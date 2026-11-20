import SGPT.Foundations.Analysis.Pending.SingularMinimalBackgroundNegative
import SGPT.Foundations.Analysis.Pending.SingularCanonicalOrderedMixedMassDistance
import SGPT.Foundations.Analysis.Pending.MixedSummandCapacityDomination
import SGPT.Foundations.Analysis.Pending.AmbientMassBackgroundMonotone

set_option autoImplicit false

/-! # Actual positive-side minimal-background distance

SGPT PDF0244 Lemma 6.2.7 Step 1. An independent quantitative adaptation:
the genuine strict potential, distinct-background positive mixed summand,
actual mass monotonicity and the exact ordered canonical distance produce
both original moving-background readers, without assumed volume continuity.
-/

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis.Pending.SingularMinimalBackgroundPositive

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus
  RelativeEnergy GlobalNonPluripolar GlobalMultilinearExpansion DiagonalMass MixedMass
  GlobalMixedMassMonotone MixedSummandCapacityDomination AmbientMassBackgroundMonotone
  SingularMinimalCanonicalRay SingularCanonicalSingularityDistance ThetaPshL1Topology
  SingularCanonicalOrderedMixedMassDistance SingularMinimalBackgroundNegative

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M]

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M] in
private theorem isBigClass_add_semipositive
    {θ η : ClosedRealOneOneForm n M}
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ)) (hη : η.val.IsSemipositive) :
    IsBigClass (RealBottChern.ofRepresentative (θ + η)) := by
  obtain ⟨T⟩ := hbig
  refine ⟨{
    representative := T.representative + η
    represents := by
      rw [RealBottChern.ofRepresentative_add, T.represents, RealBottChern.ofRepresentative_add]
    potential := T.potential
    lowerBound := T.lowerBound
    strictlyPsh := ?_ }⟩
  have he : T.representative + η - T.lowerBound.form =
      (T.representative - T.lowerBound.form) + η := by abel
  rw [he]
  exact LocalPotentials.isThetaPshPotential_add_of_semipositive T.strictlyPsh hη

private theorem weighted_diagonal_minimal_add_le
    (omega : KahlerBackground n M) (θ : ClosedRealOneOneForm n M)
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    {δ : ℝ} (hδ : 0 < δ) {ψ : M → EReal}
    (hψ : IsThetaPshPotential (θ - δ • omega.form).val ψ) (hψ0 : ψ ≤ 0)
    {ε : ℝ} (hε : 0 < ε)
    (hplus : IsBigClass (RealBottChern.ofRepresentative (θ + ε • omega.form))) :
    (δ / (δ + ε)) ^ n *
      (diagonalPotentialMass (θ + ε • omega.form)
        (thetaPshSupremum (θ + ε • omega.form).val)
        (isModelPotential_thetaPshSupremum omega (θ + ε • omega.form) hplus).plurisubharmonic).toReal ≤
      (diagonalPotentialMass θ (thetaPshSupremum θ.val)
        (isModelPotential_thetaPshSupremum omega θ hbig).plurisubharmonic).toReal := by
  classical
  let s : ℝ := δ / (δ + ε)
  have hden : 0 < δ + ε := add_pos hδ hε
  have hs : 0 < s := div_pos hδ hden
  have hs1 : s < 1 := (div_lt_one hden).mpr (by linarith)
  let α : Bool → ClosedRealOneOneForm n M :=
    fun b => if b then θ + ε • omega.form else θ - δ • omega.form
  let w : Bool → ℝ := fun b => if b then s else 1 - s
  let f : Bool → M → EReal := fun b =>
    if b then thetaPshSupremum (θ + ε • omega.form).val else ψ
  have hT : (Finset.univ : Finset Bool).Nonempty := Finset.univ_nonempty
  have hw (b : Bool) : 0 < w b := by cases b <;> simp only [w, Bool.false_eq_true,
    ↓reduceIte] <;> first | exact hs | exact sub_pos.mpr hs1
  have hV := (isModelPotential_thetaPshSupremum omega θ hbig).plurisubharmonic
  have hp := (isModelPotential_thetaPshSupremum omega (θ + ε • omega.form) hplus).plurisubharmonic
  have hf (b : Bool) : IsThetaPshPotential (α b).val (f b) := by
    cases b
    · exact hψ
    · exact hp
  have hcoeff : s * ε - (1 - s) * δ = 0 := by
    dsimp [s]
    field_simp
    ring
  have hα : sumForm Finset.univ w α = θ := by
    simp only [sumForm, Fintype.sum_bool]
    change s • (θ + ε • omega.form) + (1 - s) • (θ - δ • omega.form) = θ
    calc
      _ = (s + (1 - s)) • θ + (s * ε - (1 - s) * δ) • omega.form := by module
      _ = θ := by rw [hcoeff]; simp
  have hq := isThetaPshPotential_sumPot hT hw hf
  rw [hα] at hq
  have hq0 : sumPot Finset.univ w f ≤ 0 := by
    intro x
    simp only [sumPot, Fintype.sum_bool]
    change (s : EReal) * thetaPshSupremum (θ + ε • omega.form).val x +
      ((1 - s : ℝ) : EReal) * ψ x ≤ 0
    exact add_nonpos
      (mul_nonpos_of_nonneg_of_nonpos (EReal.coe_nonneg.mpr hs.le)
        (thetaPshSupremum_le_zero _ x))
      (mul_nonpos_of_nonneg_of_nonpos (EReal.coe_nonneg.mpr (sub_nonneg.mpr hs1.le)) (hψ0 x))
  have hqV := le_thetaPshSupremum hq hq0
  have hmono := globalMixedMass_mono_of_isThetaPshPotential omega (fun _ : Fin n => hq)
    (fun _ => hV) (fun _ => MoreSingularOn.of_le fun x _ => hqV x)
  change diagonalPotentialMass θ (sumPot Finset.univ w f) hq ≤
    diagonalPotentialMass θ (thetaPshSupremum θ.val) hV at hmono
  have hsel := selectedMixedMeasure_apply_le_diagonal_sum hT hw hf
    (fun _ : Fin n => true) (fun _ => Finset.mem_univ _) Set.univ
  have hraw : ENNReal.ofReal (s ^ n) * diagonalPotentialMass (θ + ε • omega.form)
      (thetaPshSupremum (θ + ε • omega.form).val) hp ≤
      diagonalPotentialMass θ (thetaPshSupremum θ.val) hV := by
    have hsel' : ENNReal.ofReal (s ^ n) * diagonalPotentialMass (θ + ε • omega.form)
        (thetaPshSupremum (θ + ε • omega.form).val) hp ≤
        diagonalPotentialMass θ (sumPot Finset.univ w f) hq := by
      simpa only [w, α, f, ↓reduceIte, Finset.prod_const, Finset.card_univ,
        Fintype.card_fin, hα, diagonalPotentialMass, diagonalPotentialMeasure] using hsel
    exact hsel'.trans hmono
  have hfinite : diagonalPotentialMass θ (thetaPshSupremum θ.val) hV < ⊤ :=
    globalMixedMass_lt_top omega (fun _ : Fin n => hV.1)
  have hreal := ENNReal.toReal_mono hfinite.ne hraw
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg hs.le n)] using hreal

private theorem distance_minimal_real_bounds
    (omega : KahlerBackground n M) (θ : ClosedRealOneOneForm n M)
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ)) {u : M → EReal}
    (hu : IsThetaPshPotential θ.val u) (huV : u ≤ thetaPshSupremum θ.val) :
    let hV := (isModelPotential_thetaPshSupremum omega θ hbig).plurisubharmonic
    0 ≤ (singularityDistance omega θ hbig (thetaPshSupremum θ.val) u).toReal ∧
    (singularityDistance omega θ hbig (thetaPshSupremum θ.val) u).toReal ≤
      (diagonalPotentialMass θ (thetaPshSupremum θ.val) hV).toReal -
        (diagonalPotentialMass θ u hu).toReal := by
  classical
  let V := thetaPshSupremum θ.val
  have hV : IsThetaPshPotential θ.val V :=
    (isModelPotential_thetaPshSupremum omega θ hbig).plurisubharmonic
  let : PseudoMetricSpace (ThetaPshL1 θ.val) := singularityPseudoMetricSpace omega θ hbig
  let U : ThetaPshL1 θ.val := ⟨u, hu⟩
  let P : ThetaPshL1 θ.val := ⟨V, hV⟩
  have hcomm : (singularityDistance omega θ hbig V u).toReal =
      (singularityDistance omega θ hbig u V).toReal := by
    rw [← dist_eq_singularityDistance_toReal omega θ hbig P U,
      ← dist_eq_singularityDistance_toReal omega θ hbig U P]
    exact dist_comm P U
  have hself (j : Fin (n + 1)) : endpointMixedMass θ V V hV hV j =
      diagonalPotentialMass θ V hV := by
    have htuple : endpointMixedPotential j V V = fun _ : Fin n => V :=
      funext fun i => by simp only [endpointMixedPotential, ite_self]
    exact congrArg (fun μ : Measure M => μ Set.univ)
      (UniformBoundedGlobalMass.globalMixedMeasure_congr_tuple htuple
        (endpointMixedPotential_thetaPlurisubharmonic θ j V V hV hV) (fun _ => hV.1))
  have hmass (j : Fin (n + 1)) : (diagonalPotentialMass θ u hu).toReal ≤
      (endpointMixedMass θ V u hV hu j).toReal := by
    have htu (i : Fin n) : IsThetaPshPotential θ.val (endpointMixedPotential j u V i) := by
      by_cases h : i.val < j.val
      · simpa only [endpointMixedPotential, h, ↓reduceIte] using hu
      · simpa only [endpointMixedPotential, h, ↓reduceIte] using hV
    have horder (i : Fin n) : MoreSingularOn u (endpointMixedPotential j u V i) univ := by
      apply MoreSingularOn.of_le
      intro x _
      dsimp only [endpointMixedPotential]
      split_ifs
      · exact le_rfl
      · exact huV x
    have h := globalMixedMass_mono_of_isThetaPshPotential omega (fun _ : Fin n => hu) htu horder
    change diagonalPotentialMass θ u hu ≤ endpointMixedMass θ V u hV hu j at h
    exact ENNReal.toReal_mono (globalMixedMass_lt_top omega
      (endpointMixedPotential_thetaPlurisubharmonic θ j u V hu hV)).ne h
  have hf := singularityDistance_eq_mixedMass_sub_of_le omega θ hbig hu hV huV
  change singularityDistance omega θ hbig u V =
    (((∑ j : Fin (n + 1), ((endpointMixedMass θ V V hV hV j).toReal -
      (endpointMixedMass θ V u hV hu j).toReal)) / (n + 1 : ℝ) : ℝ) : EReal) at hf
  simp only [hself] at hf
  refine ⟨?_, ?_⟩
  · rw [← dist_eq_singularityDistance_toReal omega θ hbig P U]
    exact dist_nonneg
  · rw [hcomm, hf, EReal.toReal_coe]
    have hn : 0 < (n + 1 : ℝ) := by positivity
    apply (div_le_iff₀ hn).mpr
    calc
      _ ≤ ∑ _j : Fin (n + 1), ((diagonalPotentialMass θ V hV).toReal -
          (diagonalPotentialMass θ u hu).toReal) :=
        Finset.sum_le_sum fun j _ => sub_le_sub_left (hmass j) _
      _ = ((diagonalPotentialMass θ V hV).toReal -
          (diagonalPotentialMass θ u hu).toReal) * (n + 1 : ℝ) := by simp; ring

/-- A genuine strict potential and an actual distinct-background mixed
summand produce the moving-background distance bound, in every dimension. -/
theorem exists_singularityDistance_minimal_add_smul_bound
    (omega : KahlerBackground n M) (θ : ClosedRealOneOneForm n M)
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ)) :
    ∃ δ : ℝ, 0 < δ ∧
      ∃ hplus : ∀ ε : ℝ, 0 < ε →
        IsBigClass (RealBottChern.ofRepresentative (θ + ε • omega.form)),
        ∀ (ε : ℝ) (hε : 0 < ε),
          0 ≤ (singularityDistance omega (θ + ε • omega.form) (hplus ε hε)
            (thetaPshSupremum (θ + ε • omega.form).val) (thetaPshSupremum θ.val)).toReal ∧
          (singularityDistance omega (θ + ε • omega.form) (hplus ε hε)
            (thetaPshSupremum (θ + ε • omega.form).val) (thetaPshSupremum θ.val)).toReal ≤
            (((δ / (δ + ε)) ^ n)⁻¹ - 1) *
              (diagonalPotentialMass θ (thetaPshSupremum θ.val)
                (isModelPotential_thetaPshSupremum omega θ hbig).plurisubharmonic).toReal := by
  obtain ⟨δ, hδ, ψ, hψ, hψ0, _⟩ := exists_minimal_sub_smul_convex_barrier omega θ hbig
  let hplus : ∀ ε : ℝ, 0 < ε →
      IsBigClass (RealBottChern.ofRepresentative (θ + ε • omega.form)) := fun ε hε =>
    isBigClass_add_semipositive hbig
      (KahlerDomination.isSemipositive_smul omega.isSemipositive hε.le)
  have hV := (isModelPotential_thetaPshSupremum omega θ hbig).plurisubharmonic
  refine ⟨δ, hδ, hplus, fun ε hε => ?_⟩
  have hu : IsThetaPshPotential (θ + ε • omega.form).val (thetaPshSupremum θ.val) :=
    LocalPotentials.isThetaPshPotential_add_of_semipositive hV
      (KahlerDomination.isSemipositive_smul omega.isSemipositive hε.le)
  have hp := (isModelPotential_thetaPshSupremum omega (θ + ε • omega.form)
    (hplus ε hε)).plurisubharmonic
  have hup : thetaPshSupremum θ.val ≤ thetaPshSupremum (θ + ε • omega.form).val :=
    le_thetaPshSupremum hu (thetaPshSupremum_le_zero θ.val)
  have hd := distance_minimal_real_bounds omega (θ + ε • omega.form) (hplus ε hε) hu hup
  have hweight := weighted_diagonal_minimal_add_le omega θ hbig hδ hψ hψ0 hε (hplus ε hε)
  have hs : 0 < δ / (δ + ε) := div_pos hδ (add_pos hδ hε)
  have hpow : 0 < (δ / (δ + ε)) ^ n := pow_pos hs n
  have hbound : (diagonalPotentialMass (θ + ε • omega.form)
      (thetaPshSupremum (θ + ε • omega.form).val) hp).toReal ≤
      (diagonalPotentialMass θ (thetaPshSupremum θ.val) hV).toReal /
        (δ / (δ + ε)) ^ n := by
    apply (le_div_iff₀ hpow).mpr
    simpa only [mul_comm] using hweight
  have hmono := diagonalPotentialMass_le_add_smul omega.isSemipositive hε hV hu
  have hfinite : diagonalPotentialMass (θ + ε • omega.form) (thetaPshSupremum θ.val) hu < ⊤ :=
    globalMixedMass_lt_top omega (fun _ : Fin n => hu.1)
  have hmonoReal := ENNReal.toReal_mono hfinite.ne hmono
  refine ⟨hd.1, hd.2.trans ?_⟩
  calc
    _ ≤ (diagonalPotentialMass θ (thetaPshSupremum θ.val) hV).toReal /
        (δ / (δ + ε)) ^ n - (diagonalPotentialMass θ (thetaPshSupremum θ.val) hV).toReal :=
      sub_le_sub hbound hmonoReal
    _ = _ := by rw [div_eq_mul_inv]; ring

/-- Internally produced moving-class bigness and finite actual canonical
distance give both readers on the original raw right-neighborhood filter. -/
theorem exists_tendsto_singularityDistance_minimal_add_smul_right
    (omega : KahlerBackground n M) (θ : ClosedRealOneOneForm n M)
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ)) :
    ∃ hplus : ∀ ε : ℝ, 0 < ε →
      IsBigClass (RealBottChern.ofRepresentative (θ + ε • omega.form)),
      Tendsto (fun ε : ℝ => if hε : 0 < ε then
        singularityDistance omega (θ + ε • omega.form) (hplus ε hε)
          (thetaPshSupremum (θ + ε • omega.form).val) (thetaPshSupremum θ.val)
        else 0) (𝓝[>] 0) (𝓝 (0 : EReal)) ∧
      Tendsto (fun ε : ℝ => (if hε : 0 < ε then
        singularityDistance omega (θ + ε • omega.form) (hplus ε hε)
          (thetaPshSupremum (θ + ε • omega.form).val) (thetaPshSupremum θ.val)
        else 0).toReal) (𝓝[>] 0) (𝓝 (0 : ℝ)) := by
  obtain ⟨δ, hδ, hplus, hbound⟩ := exists_singularityDistance_minimal_add_smul_bound omega θ hbig
  let D : ℝ → EReal := fun ε => if hε : 0 < ε then
    singularityDistance omega (θ + ε • omega.form) (hplus ε hε)
      (thetaPshSupremum (θ + ε • omega.form).val) (thetaPshSupremum θ.val) else 0
  let m : ℝ := (diagonalPotentialMass θ (thetaPshSupremum θ.val)
    (isModelPotential_thetaPshSupremum omega θ hbig).plurisubharmonic).toReal
  have hcoord : Tendsto (fun ε : ℝ => ε) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hδlim : Tendsto (fun _ : ℝ => δ) (𝓝[>] (0 : ℝ)) (𝓝 δ) := tendsto_const_nhds
  have h1lim : Tendsto (fun _ : ℝ => (1 : ℝ)) (𝓝[>] (0 : ℝ)) (𝓝 1) := tendsto_const_nhds
  have hdenlim : Tendsto (fun ε : ℝ => δ + ε) (𝓝[>] 0) (𝓝 δ) := by
    simpa only [add_zero] using hδlim.add hcoord
  have hs : Tendsto (fun ε : ℝ => δ / (δ + ε)) (𝓝[>] 0) (𝓝 (1 : ℝ)) := by
    simpa only [div_eq_mul_inv, mul_inv_cancel₀ hδ.ne'] using
      hδlim.mul (hdenlim.inv₀ hδ.ne')
  have hupper : Tendsto (fun ε : ℝ => (((δ / (δ + ε)) ^ n)⁻¹ - 1) * m)
      (𝓝[>] 0) (𝓝 (0 : ℝ)) := by
    simpa only [one_pow, inv_one, sub_self, zero_mul] using
      (((hs.pow n).inv₀ (by simp)).sub h1lim).mul_const m
  have hgt : ∀ᶠ ε : ℝ in 𝓝[>] 0, 0 < ε := self_mem_nhdsWithin
  have hnonneg : ∀ᶠ ε : ℝ in 𝓝[>] 0, 0 ≤ (D ε).toReal := by
    filter_upwards [hgt] with ε hε
    simpa only [D, dif_pos hε] using (hbound ε hε).1
  have hle : ∀ᶠ ε : ℝ in 𝓝[>] 0,
      (D ε).toReal ≤ (((δ / (δ + ε)) ^ n)⁻¹ - 1) * m := by
    filter_upwards [hgt] with ε hε
    simpa only [D, dif_pos hε] using (hbound ε hε).2
  have hreal : Tendsto (fun ε : ℝ => (D ε).toReal) (𝓝[>] 0) (𝓝 (0 : ℝ)) :=
    squeeze_zero' hnonneg hle hupper
  have hfinite : ∀ ε : ℝ, ((D ε).toReal : EReal) = D ε := by
    intro ε
    by_cases hε : 0 < ε
    · have hV := (isModelPotential_thetaPshSupremum omega θ hbig).plurisubharmonic
      have hu : IsThetaPshPotential (θ + ε • omega.form).val (thetaPshSupremum θ.val) :=
        LocalPotentials.isThetaPshPotential_add_of_semipositive hV
          (KahlerDomination.isSemipositive_smul omega.isSemipositive hε.le)
      have hp := (isModelPotential_thetaPshSupremum omega (θ + ε • omega.form)
        (hplus ε hε)).plurisubharmonic
      obtain ⟨a, _, _, _, ha⟩ := exists_tendsto_singularityDistance omega
        (θ + ε • omega.form) (hplus ε hε) hp hu
      simp only [D, dif_pos hε, ha, EReal.toReal_coe]
    · simp only [D, dif_neg hε, EReal.toReal_zero, EReal.coe_zero]
  have hextended : Tendsto D (𝓝[>] 0) (𝓝 (0 : EReal)) := by
    simpa only [hfinite, EReal.coe_zero] using EReal.tendsto_coe.mpr hreal
  exact ⟨hplus, hextended, hreal⟩

end
end SGPT.Foundations.Analysis.Pending.SingularMinimalBackgroundPositive
