import SGPT.Okounkov.TranscendentalPartialResidual
import SGPT.Okounkov.TranscendentalPartialVolume
import SGPT.Okounkov.TranscendentalLifting
import SGPT.Foundations.Analysis.Pending.DominationResidualMass
import SGPT.Foundations.Analysis.Pending.AnalyticModificationMixedMass
import SGPT.Foundations.Analysis.Pending.RestrictedApproximantMass
import SGPT.Foundations.Analysis.Pending.MeteredDivisorGlobalIdeal

/-!
# Bimeromorphic behaviour of partial Okounkov bodies

Source: blueprint node `tok:partial-birational` (chapter `claude-okounkov-transcendental`), i.e.
Darvas--Reboulet--Witt Nyström--Xia--Zhang, *Transcendental Okounkov bodies* (DRWNXZ), Lemma 5.5,
with the bounded-potential current `R'` in place of the smooth form `β` of the source.

Let `R = θ + dd^c ψ` be a Kähler current with analytic singularities on `X` and let
`π : W → X` be a modification carrying a lifting `(W•, g)` of the flag (`g = cor(Y•, π)`) along
which `π^*R = [D] + R'`: `ψ ∘ π = ψ_D + b` with `b` a bounded `(π^*θ - Θ_D)`-psh function
(`IsResolutionData`; such data exist for `R ∈ 𝒜ᵍ(ξ)` by `tok:resolution-lifting`,
`exists_resolutionData`). Then

* `{R'} = {π^*θ - Θ_D}` is big and `∫_W ⟨R'^n⟩ = ∫_X ⟨R^n⟩` (`isBig_residualClass`,
  `diagonalPotentialMass_residual_eq`; the latter is the non-pluripolar mass identity
  `NPP([D] + R') = NPP(R')` and the invariance of masses under modifications);
* `vol {R'} = ∫_W ⟨R'^n⟩` (`R'` has bounded potentials, hence minimal singularities;
  `sourceClassVolume_eq_of_bounded`);
* `Δ_{Y•}(ξ; R) g ⊆ Δ_{W•}({R'}) + ν_{W•}([D])` (`image_partialOkounkovBody_subset`,
  **unconditional**): for `T ∈ Ω(ξ; R)`, `π^*T - [D]` has analytic singularities (the divisor
  subtraction `divisorResidualStatement` of `TranscendentalPartialResidual`, `tok:siu-analytic`),
  and DENSITY on `W`;
* `Δ_{W•}({R'}) + ν_{W•}([D]) ⊆ Δ_{Y•}(ξ; R) g` (`subset_image_partialOkounkovBody`), given
  `PushforwardAnalyticStatement` (LIFT's `tok:approx-pushforward`, conditional on RELGEN): for
  `S ∈ Ω(W, {R'})`, `S + [D]` is a Kähler current in `𝒜ᵍ(W, π^*ξ)` more singular than `π^*R`, and
  its approximants `T_k ⪯ π_*(S + [D]) ⪯ R` have `ν(T_k) g → ν_{W•}(S) + ν_{W•}([D])`;
* `partialOkounkovBody_birational`: the equality (DRWNXZ Lemma 5.5), conditional on
  `PushforwardAnalyticStatement` only.
-/

set_option autoImplicit false

noncomputable section

universe u

namespace SGPT.Okounkov.TranscendentalPartial

open Set Filter MeasureTheory
open scoped ENNReal Topology Matrix Pointwise
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
open SGPT.Foundations.Analysis.FirstPass.GlobalAnalyticSingularities
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.DiagonalMass
open SGPT.PSH SGPT.Okounkov.TranscendentalCore SGPT.Okounkov.TranscendentalLifting
open SGPT.Okounkov.TranscendentalRelGen
open SGPT.PSH.VariableComplexAtlas

/-! ### Bounded potentials and volumes -/

section Volume

variable {m : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel (m + 1)) X]
  [IsComplexManifold (m + 1) X] [CompactSpace X] [ConnectedSpace X]
  [MeasurableSpace X] [BorelSpace X]

/-- **A current with bounded potentials computes the volume of its class** (it has minimal
singularities; `def:volcohclass`): `vol {θ} = ∫_X ⟨(θ + dd^c b)^n⟩` for a bounded-below `θ`-psh
`b`. -/
theorem sourceClassVolume_eq_of_bounded (ω : KahlerBackground (m + 1) X)
    (θ : ClosedRealOneOneForm (m + 1) X) {b : X → EReal} (hb : IsThetaPshPotential θ.val b)
    {C : ℝ} (hbC : ∀ x, ((-C : ℝ) : EReal) ≤ b x) :
    sourceClassVolume (RealBottChern.ofRepresentative θ) = diagonalPotentialMass θ b hb := by
  obtain ⟨hV, hvol⟩ := TranscendentalVolumeConcavity.sourceClassVolume_ofRepresentative ω θ hb
  refine le_antisymm ?_ (TranscendentalVolumeConcavity.diagonalPotentialMass_le_sourceClassVolume
    ω θ hb)
  rw [hvol]
  obtain ⟨C', hC'⟩ := RelativePreceqClasses.exists_le_coe_of_isThetaPshPotential hV
  refine diagonalPotentialMass_mono_of_kahler ω hV hb ⟨C' + C, fun x _ => ?_⟩
  calc thetaPshSupremum θ.val x ≤ (C' : EReal) := hC' x
    _ = ((-C : ℝ) : EReal) + ((C' + C : ℝ) : EReal) := by
        rw [← EReal.coe_add]; congr 1; ring
    _ ≤ b x + ((C' + C : ℝ) : EReal) := add_le_add (hbC x) le_rfl

end Volume

/-! ### Resolution data -/

section Resolution

variable {m : ℕ} {F : OriginalFlagGeometry.{u} (m + 1)}

/-- **Resolution data of `R = θ + dd^c ψ` along a flag lifting `π : W → X`** (blueprint
`tok:resolution-lifting`, DRWNXZ §2 and Theorem 4.3): a metered effective `ℚ`-divisor `D` on `W`
and a bounded `(π^*θ - Θ_D)`-psh function `b` with `ψ ∘ π = ψ_D + b`, i.e. `π^*R = [D] + R'` with
`R' = π^*θ - Θ_D + dd^c b` closed positive with bounded potentials. -/
structure IsResolutionData (θ : ClosedRealOneOneForm (m + 1) F.carrier) (ψ : F.carrier → EReal)
    {W : OriginalFlagGeometry.{u} (m + 1)} {π : W.carrier → F.carrier} (hπ : IsFlagLifting F W π)
    (D : MeteredEffectiveQDivisor (m + 1) W.carrier) (b : W.carrier → EReal) : Prop where
  psh : IsThetaPshPotential (ClosedRealOneOneForm.pullback hπ.1.1 θ - D.curvature).val b
  bounded : ∃ C : ℝ, ∀ y, ((-C : ℝ) : EReal) ≤ b y ∧ b y ≤ (C : EReal)
  eq : ∀ y, ψ (π y) = D.weight y + b y

/-- **Existence of resolution data** (blueprint `tok:resolution-lifting`, LIFT's
`exists_logResolution_flagLifting`): every `R ∈ 𝒜ᵍ(ξ)` admits a log resolution by a blow-up
sequence carrying a lifting of the flag. -/
theorem exists_resolutionData {θ : ClosedRealOneOneForm (m + 1) F.carrier}
    {ψ : F.carrier → EReal} (hψ : ψ ∈ globalAnalyticCurrents θ) :
    ∃ (W : OriginalFlagGeometry.{u} (m + 1)) (π : W.carrier → F.carrier)
      (hπ : IsFlagLifting F W π) (D : MeteredEffectiveQDivisor (m + 1) W.carrier)
      (b : W.carrier → EReal), IsResolutionData θ ψ hπ D b := by
  obtain ⟨c, 𝔞, htype⟩ := hψ.2
  obtain ⟨W, π, _hp, D, hπ, -, ⟨b, C, hb, hbC, heq⟩, -⟩ :=
    exists_logResolution_flagLifting F θ hψ.1 htype
  refine ⟨W, π, hπ, D, b, ⟨⟨hb, fun y _ _ hy => ⟨y, hy, ?_⟩⟩, ⟨C, hbC⟩, heq⟩⟩
  intro hbot
  have h := (hbC y).1
  rw [hbot] at h
  exact EReal.coe_ne_bot _ (le_bot_iff.mp h)

variable {θ : ClosedRealOneOneForm (m + 1) F.carrier} {ψ : F.carrier → EReal}
  {W : OriginalFlagGeometry.{u} (m + 1)} {π : W.carrier → F.carrier} {hπ : IsFlagLifting F W π}
  {D : MeteredEffectiveQDivisor (m + 1) W.carrier} {b : W.carrier → EReal}

/-- `π^*R = [D] + R'` has the same non-pluripolar mass as `R'` and as `R`:
`∫_W ⟨R'^n⟩ = ∫_X ⟨R^n⟩`. -/
theorem diagonalPotentialMass_residual_eq [MeasurableSpace F.carrier] [BorelSpace F.carrier]
    [MeasurableSpace W.carrier] [BorelSpace W.carrier] (hR : IsResolutionData θ ψ hπ D b)
    (hψ : IsThetaPshPotential θ.val ψ) :
    diagonalPotentialMass (ClosedRealOneOneForm.pullback hπ.1.1 θ - D.curvature) b hR.psh =
      diagonalPotentialMass θ ψ hψ := by
  have hψπ : IsThetaPshPotential (ClosedRealOneOneForm.pullback hπ.1.1 θ).val
      (fun y => ψ (π y)) :=
    AnalyticModificationStrongPullback.isThetaPshPotential_comp_of_isAnalyticModification hπ.1 θ hψ
  rw [DominationResidualMass.diagonalPotentialMass_sub_curvature_eq _ D hψπ hR.psh
    (fun y _ => hR.eq y) (isThetaPshPotential_weight D).2]
  exact AnalyticModificationMixedMass.diagonalPotentialMass_pullback_of_isAnalyticModification
    hπ.1 θ hψ

/-- **`{R'}` is big** (DRWNXZ Lemma 5.5, first claim): `∫ ⟨R'^n⟩ = ∫ ⟨R^n⟩ > 0` for a Kähler
current `R` (`npp:source-whole-positive-mass-big`). -/
theorem isBig_residualClass (hR : IsResolutionData θ ψ hπ D b) (hK : IsKahlerCurrentPotential θ ψ) :
    SGPT.PSH.BookCurrent.IsBig
      (RealBottChern.ofRepresentative (ClosedRealOneOneForm.pullback hπ.1.1 θ - D.curvature)) := by
  let _ : MeasurableSpace F.carrier := borel F.carrier
  have _ : BorelSpace F.carrier := ⟨rfl⟩
  let _ : MeasurableSpace W.carrier := borel W.carrier
  have _ : BorelSpace W.carrier := ⟨rfl⟩
  have _ : Nonempty F.carrier := ⟨(F.smooth.2.2 0).2.1.nonempty.some⟩
  obtain ⟨κ, hκ⟩ := hK
  -- `κ ≥ c ω`
  obtain ⟨A, hA, hAsemi⟩ := KahlerDomination.exists_pos_isSemipositive_add_smul κ (-F.omega.form)
  set c : ℝ := A⁻¹ with hc
  have hc0 : 0 < c := inv_pos.mpr hA
  have hκc : (κ.form - c • F.omega.form).val.IsSemipositive := by
    have h := KahlerDomination.isSemipositive_smul hAsemi hc0.le
    have he : c • (-F.omega.form + A • κ.form) = κ.form - c • F.omega.form := by
      rw [smul_add, smul_smul, hc, inv_mul_cancel₀ hA.ne', one_smul, smul_neg]
      abel
    rwa [he] at h
  have hψc : IsThetaPshPotential (θ - c • F.omega.form).val ψ := by
    have h := LocalPotentials.isThetaPshPotential_add_of_semipositive hκ hκc
    have he : θ - κ.form + (κ.form - c • F.omega.form) = θ - c • F.omega.form := by abel
    rwa [he] at h
  have hψθ : IsThetaPshPotential θ.val ψ := by
    have h := LocalPotentials.isThetaPshPotential_add_of_semipositive hψc
      (KahlerDomination.isSemipositive_smul F.omega.isSemipositive hc0.le)
    rwa [sub_add_cancel] at h
  have hpos : 0 < diagonalPotentialMass θ ψ hψθ :=
    RestrictedApproximantMass.diagonalPotentialMass_pos_of_sub_smul F.omega hc0 hψc hψθ
  rw [← diagonalPotentialMass_residual_eq hR hψθ] at hpos
  have hvol := hpos.trans_le (TranscendentalVolumeConcavity.diagonalPotentialMass_le_sourceClassVolume
    W.omega _ hR.psh)
  rw [SGPT.PSH.BookCurrent.isBig_iff_isBigClass]
  exact (TranscendentalVolumeConcavity.sourceClassVolume_pos_iff_isBigClass W.omega _).mp hvol

end Resolution

/-! ### The two inclusions -/

section Inclusions

variable {m : ℕ} {F : OriginalFlagGeometry.{u} (m + 1)}
  {θ : ClosedRealOneOneForm (m + 1) F.carrier} {ψ : F.carrier → EReal}
  {W : OriginalFlagGeometry.{u} (m + 1)} {π : W.carrier → F.carrier} {hπ : IsFlagLifting F W π}
  {D : MeteredEffectiveQDivisor (m + 1) W.carrier} {b : W.carrier → EReal}

/-- `ν(ψ_D + w) = ν(ψ_D) + ν(w)`. -/
theorem flagValuation_weight_add {β : ClosedRealOneOneForm (m + 1) W.carrier}
    {w : W.carrier → EReal} (hw : IsThetaPshPotential β.val w) :
    flagValuation W (fun y => D.weight y + w y) = flagValuation W D.weight + flagValuation W w := by
  have h := flagValuation_add_smul (F := W) (isThetaPshPotential_weight D) hw (a := 1) (b := 1)
    zero_le_one zero_le_one
  have hfun : (fun y => ((1 : ℝ) : EReal) * D.weight y + ((1 : ℝ) : EReal) * w y) =
      fun y => D.weight y + w y := by
    funext y
    simp
  rwa [hfun, one_smul, one_smul] at h

/-- **`tok:partial-birational`, `⊆`** (DRWNXZ Lemma 5.5; unconditional):
`Δ_{Y•}(ξ; R) g ⊆ ν_{W•}([D]) + Δ_{W•}({R'})`. -/
theorem image_partialOkounkovBody_subset (hR : IsResolutionData θ ψ hπ D b) (hK : IsKahlerCurrentPotential θ ψ) :
    (fun x => x ᵥ* correctionMatrixReal hπ) '' partialOkounkovBody F θ ψ ⊆
      flagValuation W D.weight +ᵥ
        tradOkounkovBody W (ClosedRealOneOneForm.pullback hπ.1.1 θ - D.curvature) := by
  set β := ClosedRealOneOneForm.pullback hπ.1.1 θ - D.curvature with hβ
  have hbig := isBig_residualClass hR hK
  have hclosed : IsClosed (flagValuation W D.weight +ᵥ tradOkounkovBody W β) :=
    (isClosed_tradOkounkovBody β).vadd _
  have hcont : Continuous (fun x : Fin (m + 1) → ℝ => x ᵥ* correctionMatrixReal hπ) :=
    Continuous.matrix_vecMul continuous_id continuous_const
  refine (image_closure_subset_closure_image hcont).trans (closure_minimal ?_ hclosed)
  rintro _ ⟨_, ⟨φ, hφ, rfl⟩, rfl⟩
  have hφA : φ ∈ analyticCurrents θ := gentleCurrents_subset_analyticCurrents θ hφ.1.1
  have hu : (fun y => φ (π y)) ∈ analyticCurrents (ClosedRealOneOneForm.pullback hπ.1.1 θ) :=
    comp_mem_analyticCurrents hπ.1 hφA
  -- `π^*T ⪯ ψ_D`
  have huD : SingularityLE (fun y => φ (π y)) D.weight := by
    obtain ⟨C₁, hC₁⟩ := (singularityLE_iff_exists_real _ _).mp hφ.2
    obtain ⟨C, hC⟩ := hR.bounded
    refine (singularityLE_iff_exists_real _ _).mpr ⟨C₁ + C, fun y => ?_⟩
    calc φ (π y) ≤ ψ (π y) + (C₁ : EReal) := hC₁ (π y)
      _ = D.weight y + b y + (C₁ : EReal) := by rw [hR.eq y]
      _ ≤ D.weight y + (C : EReal) + (C₁ : EReal) := add_le_add (add_le_add le_rfl (hC y).2) le_rfl
      _ = D.weight y + ((C₁ + C : ℝ) : EReal) := by
          rw [add_assoc, ← EReal.coe_add, add_comm C C₁]
  obtain ⟨w, hw, hweq⟩ := divisorResidualStatement.{u} (m + 1) W.carrier _ D _ hu huD
  have hν : flagValuation F φ ᵥ* correctionMatrixReal hπ =
      flagValuation W D.weight + flagValuation W w := by
    rw [← flagValuation_comp_eq_vecMul hπ hφA.1, ← flagValuation_weight_add hw.1]
    congr 1
    funext y
    exact hweq y
  show flagValuation F φ ᵥ* correctionMatrixReal hπ ∈ _
  rw [hν]
  refine vadd_mem_vadd_set ?_
  rw [TranscendentalDensity.tradOkounkovBody_eq_closure_analyticCurrents hbig]
  exact subset_closure ⟨w, hw, rfl⟩

/-- **`tok:partial-birational`, `⊇`** (DRWNXZ Lemma 5.5), given the analytic pushforward
`PushforwardAnalyticStatement` (via LIFT's `tok:approx-pushforward`):
`ν_{W•}([D]) + Δ_{W•}({R'}) ⊆ Δ_{Y•}(ξ; R) g`. -/
theorem subset_image_partialOkounkovBody (hP : PushforwardAnalyticStatement.{u})
    (hR : IsResolutionData θ ψ hπ D b) (hK : IsKahlerCurrentPotential θ ψ)
    (hA : ψ ∈ analyticCurrents θ) :
    flagValuation W D.weight +ᵥ
        tradOkounkovBody W (ClosedRealOneOneForm.pullback hπ.1.1 θ - D.curvature) ⊆
      (fun x => x ᵥ* correctionMatrixReal hπ) '' partialOkounkovBody F θ ψ := by
  set β := ClosedRealOneOneForm.pullback hπ.1.1 θ - D.curvature with hβ
  set θ' := ClosedRealOneOneForm.pullback hπ.1.1 θ with hθ'
  have hbig := isBig_residualClass hR hK
  have hcont : Continuous (fun x : Fin (m + 1) → ℝ => x ᵥ* correctionMatrixReal hπ) :=
    Continuous.matrix_vecMul continuous_id continuous_const
  have hKc : IsClosed ((fun x => x ᵥ* correctionMatrixReal hπ) '' partialOkounkovBody F θ ψ) :=
    ((isCompact_partialOkounkovBody θ ψ).image hcont).isClosed
  have hvcont : Continuous (fun x : Fin (m + 1) → ℝ => flagValuation W D.weight +ᵥ x) :=
    continuous_const.add continuous_id
  rw [TranscendentalDensity.tradOkounkovBody_eq_closure_gentleKahlerCurrents hbig]
  refine (image_closure_subset_closure_image hvcont).trans (closure_minimal ?_ hKc)
  rintro _ ⟨_, ⟨s, hs, rfl⟩, rfl⟩
  -- `S + [D]` is a Kähler current in `𝒜ᵍ(W, π^*ξ)`
  set ψ' : W.carrier → EReal := fun y => D.weight y + s y with hψ'
  have hspsh : IsThetaPshPotential β.val s := isThetaPshPotential_of_mem_gentleCurrents hs.1
  have hformD : D.curvature + β = θ' := by rw [hβ]; abel
  have hψ'psh : IsThetaPshPotential θ'.val ψ' := by
    have h := isThetaPshPotential_add_from_positive_sum (isThetaPshPotential_weight D) hspsh
    rwa [hformD] at h
  have hψ'glob : ψ' ∈ globalAnalyticCurrents θ' := by
    refine ⟨hψ'psh, ?_⟩
    obtain ⟨c, 𝔞, -, -, hc⟩ := MeteredDivisorGlobalIdeal.exists_hasAnalyticSingularitiesOfType D
    exact hasAnalyticSingularities_add ⟨c, 𝔞, hc⟩
      (gentleKahlerCurrents_subset_globalAnalyticCurrents hs).2
  have hψ'K : IsKahlerCurrentPotential θ' ψ' := by
    obtain ⟨κ, hκ⟩ := hs.2
    refine ⟨κ, ?_⟩
    have h := isThetaPshPotential_add_from_positive_sum (isThetaPshPotential_weight D) hκ
    have hform : D.curvature + (β - κ.form) = θ' - κ.form := by rw [hβ]; abel
    rwa [hform] at h
  -- the approximants
  obtain ⟨wv, φ, -, hφA, -, hφle, hφν⟩ :=
    exists_analytic_approximation_of_lifting hP hπ hψ'glob hψ'K
  -- the pushforward `χ` of `S + [D]` is more singular than `R`
  obtain ⟨χ, -, hχ⟩ := exists_descent hπ.1 θ hψ'psh
  have hχψ : SingularityLE χ ψ := by
    rw [← singularityLE_comp_iff hπ.1]
    obtain ⟨Cs, hCs⟩ := RelativePreceqClasses.exists_le_coe_of_isThetaPshPotential hspsh
    obtain ⟨C, hC⟩ := hR.bounded
    refine (singularityLE_iff_exists_real _ _).mpr ⟨Cs + C, fun y => ?_⟩
    rw [hχ y, hR.eq y]
    calc D.weight y + s y ≤ D.weight y + (Cs : EReal) := add_le_add le_rfl (hCs y)
      _ = D.weight y + ((-C : ℝ) : EReal) + ((Cs + C : ℝ) : EReal) := by
          rw [add_assoc, ← EReal.coe_add]; congr 2; ring
      _ ≤ D.weight y + b y + ((Cs + C : ℝ) : EReal) :=
          add_le_add (add_le_add le_rfl (hC y).1) le_rfl
  have hmem : ∀ k, flagValuation F (φ k) ᵥ* correctionMatrixReal hπ ∈
      (fun x => x ᵥ* correctionMatrixReal hπ) '' partialOkounkovBody F θ ψ := fun k =>
    ⟨_, flagValuation_mem_partialOkounkovBody_of_analytic hK hA
      ⟨hφA k, singularityLE_trans (hφle k χ hχ) hχψ⟩, rfl⟩
  -- the limit
  have hlim : Tendsto (fun k : ℕ => flagValuation F (φ k) ᵥ* correctionMatrixReal hπ) atTop
      (𝓝 (flagValuation W ψ')) := by
    have h0 : Tendsto (fun k : ℕ => (1 : ℝ) / ((k : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have h1 : Tendsto (fun k : ℕ => flagValuation W ψ' + ((1 : ℝ) / ((k : ℝ) + 1)) • wv) atTop
        (𝓝 (flagValuation W ψ' + (0 : ℝ) • wv)) :=
      tendsto_const_nhds.add (h0.smul_const wv)
    rw [zero_smul, add_zero] at h1
    exact h1.congr fun k => (hφν k).symm
  have hlimmem := hKc.mem_of_tendsto hlim (Eventually.of_forall hmem)
  rwa [hψ', flagValuation_weight_add hspsh] at hlimmem

/-- **`tok:partial-birational`** (DRWNXZ Lemma 5.5), **conditional** on
`PushforwardAnalyticStatement` (RELGEN's `tok:boucksom-pushforward`, through LIFT's
`tok:approx-pushforward`): for a Kähler current `R = θ + dd^c ψ ∈ 𝒜(ξ)` and resolution data
`π^*R = [D] + R'` along a flag lifting `(W•, g)`, `{R'}` is big and
`Δ_{Y•}(ξ; R) g = ν_{W•}([D]) + Δ_{W•}({R'})`. -/
theorem partialOkounkovBody_birational (hP : PushforwardAnalyticStatement.{u}) (hR : IsResolutionData θ ψ hπ D b)
    (hK : IsKahlerCurrentPotential θ ψ) (hA : ψ ∈ analyticCurrents θ) :
    SGPT.PSH.BookCurrent.IsBig
        (RealBottChern.ofRepresentative (ClosedRealOneOneForm.pullback hπ.1.1 θ - D.curvature)) ∧
      (fun x => x ᵥ* correctionMatrixReal hπ) '' partialOkounkovBody F θ ψ =
        flagValuation W D.weight +ᵥ
          tradOkounkovBody W (ClosedRealOneOneForm.pullback hπ.1.1 θ - D.curvature) :=
  ⟨isBig_residualClass hR hK, (image_partialOkounkovBody_subset hR hK).antisymm
    (subset_image_partialOkounkovBody hP hR hK hA)⟩

end Inclusions

end SGPT.Okounkov.TranscendentalPartial
