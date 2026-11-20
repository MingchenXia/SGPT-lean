import SGPT.NAPotential.DivDictOperations
import SGPT.NAPotential.DivDictValuation
import SGPT.NAPotential.BJDivisorialSpecComplex
import SGPT.Foundations.Analysis.Pending.GlobalQuasiPshMultiplierPrincipalization

/-! # The trivial valuation: `φ^An(v_triv) = 0` and `Γ^An(v_triv) = Γ_max`

Source `chapter_NApotential.tex`, `eq:Gammamax` (Section *The comparison theorem*):
*also observe that `Γ_max = Γ^An(v_triv)`*.  Blueprint `claude-div-dict:trivial`.

For the integral scheme `X`, the trivial valuation `v_triv` of `ℂ(X)` has the generic point of `X`
as its centre, so `v_triv(𝔞) = 0` for every nonzero ideal sheaf `𝔞`
(`BerkovichPoint.trivial_idealVal_eq_zero`).  The algebraic model of a multiplier ideal `𝓘(cφ)`
of a quasi-psh function is nonzero as soon as it analytifies to `𝓘(cφ)`
(`algebraization_multiplierIdeal_ne_bot`); hence, conditionally on `MultiplierIdealAlgebraic`,

* `potentialAn_trivial`: `φ^An(v_triv) = 0` for `φ ∈ PSH(X, θ)`;
* `naPotentialAnAt_trivial`: `Γ^An(v_triv) = Γ_max` (`eq:Gammamax`).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.NAPotential.Berkovich

open Set Filter
open scoped Topology ENNReal
open AlgebraicGeometry CategoryTheory IsLocalRing SGPT.Foundations.Schemes SGPT.Okounkov
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves SGPT.Foundations.Analysis.Pending
open SGPT.PSH.VariableComplexAtlas

/-! ### The centre of the trivial valuation -/

section Center

variable {X : Scheme.{0}} {f : X ⟶ Spec (.of ℂ)} [IsIntegral X]

/-- The generic point of `X` is a centre of the trivial valuation. -/
theorem BerkovichPoint.isCenter_trivial :
    (BerkovichPoint.trivial f).IsCenter (genericPoint X) := by
  classical
  have hsp : (BerkovichPoint.trivial f).support ⤳ genericPoint X := by
    rw [BerkovichPoint.trivial_support]
  refine ⟨hsp, fun g => ?_, fun g hg => ?_⟩
  · by_cases h0 : (specializationMap hsp).hom g = 0
    · rw [h0, BerkovichPoint.valAt_zero]
      exact le_top
    · exact le_of_eq (BerkovichPoint.trivial_valAt_of_ne_zero h0).symm
  · have hF : IsField (X.presheaf.stalk (genericPoint X)) :=
      Semifield.toIsField (X.presheaf.stalk (genericPoint X))
    have hg0 : g = 0 := by
      have hbot : maximalIdeal (X.presheaf.stalk (genericPoint X)) = ⊥ :=
        isField_iff_maximalIdeal_eq.mp hF
      rw [hbot] at hg
      exact hg
    rw [hg0, map_zero, BerkovichPoint.valAt_zero]
    exact lt_of_le_of_ne le_top WithTop.zero_ne_top

variable [IsProper f]

/-- The centre of the trivial valuation is the generic point of `X`. -/
theorem BerkovichPoint.center_trivial :
    (BerkovichPoint.trivial f).center = genericPoint X :=
  (((BerkovichPoint.trivial f).isCenter_iff_eq_center _).mp BerkovichPoint.isCenter_trivial).symm

/-- A nonzero ideal sheaf of the integral scheme `X` has a nonzero germ at the generic point. -/
theorem stalkIdeal_genericPoint_eq_top {𝔞 : X.IdealSheafData} (h𝔞 : 𝔞 ≠ ⊥) :
    stalkIdeal 𝔞 (genericPoint X) = ⊤ := by
  have hex : ∃ U : X.affineOpens, 𝔞.ideal U ≠ ⊥ := by
    by_contra hcon
    push Not at hcon
    apply h𝔞
    ext U : 2
    rw [hcon U, Scheme.IdealSheafData.ideal_bot]
    rfl
  obtain ⟨U, hU⟩ := hex
  obtain ⟨r, hr, hr0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU
  have hne : ((U : X.Opens) : Set X).Nonempty := by
    by_contra hemp
    rw [Set.not_nonempty_iff_eq_empty] at hemp
    have hsub : Subsingleton Γ(X, (U : X.Opens)) := by
      have hbot : (U : X.Opens) = ⊥ := TopologicalSpace.Opens.ext hemp
      rw [hbot]
      exact CommRingCat.subsingleton_of_isTerminal X.sheaf.isTerminalOfEmpty
    exact hr0 (Subsingleton.elim _ _)
  have hη : genericPoint X ∈ (U : X.Opens) :=
    ((genericPoint_spec X).mem_open_set_iff (U : X.Opens).isOpen).mpr
      (by simpa only [Set.univ_inter] using hne)
  have hgerm : (X.presheaf.germ U (genericPoint X) hη).hom r ≠ 0 := by
    intro h0
    exact hr0 (germ_injective_of_isIntegral X (genericPoint X) hη (h0.trans (map_zero _).symm))
  have hmem := germ_mem_stalkIdeal 𝔞 U hη hr
  have hF : IsField (X.presheaf.stalk (genericPoint X)) :=
    Semifield.toIsField (X.presheaf.stalk (genericPoint X))
  exact Ideal.eq_top_of_isUnit_mem _ hmem
    (isUnit_iff_ne_zero.mpr hgerm)

variable [IsLocallyNoetherian X]

/-- `v_triv(𝔞) = 0` for every nonzero ideal sheaf `𝔞`. -/
theorem BerkovichPoint.trivial_idealVal_eq_zero {𝔞 : X.IdealSheafData} (h𝔞 : 𝔞 ≠ ⊥) :
    (BerkovichPoint.trivial f).idealVal 𝔞 = 0 := by
  rw [BerkovichPoint.idealVal_eq_zero_iff, BerkovichPoint.center_trivial]
  exact stalkIdeal_genericPoint_eq_top h𝔞

end Center

/-! ### Multiplier ideals have nonzero algebraic models -/

section Multiplier

variable {X : Scheme.{0}} {f : X ⟶ Spec (.of ℂ)} (k : ℕ) [SmoothOfRelativeDimension k f]
  (E : ClosedProjectiveEmbedding f) [IsProper f]

local instance divDictTrivPointTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance divDictTrivPointCharts : ChartedSpace (ComplexModel k) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f k
local instance divDictTrivPointManifold : IsComplexManifold k (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f k

omit [IsProper f] in
/-- The analytification of the zero ideal sheaf only contains germs vanishing near the point. -/
theorem eventually_eq_zero_of_mem_analytificationIdeal_bot {x : SchemeComplexPoint f}
    {g : SchemeComplexPoint f → ℂ}
    (hg : (analytificationIdeal f k E (⊥ : X.IdealSheafData)).mem x g) : g =ᶠ[𝓝 x] 0 := by
  obtain ⟨-, N, s, a, hs, -, hga⟩ := hg
  have hs0 : ∀ i : Fin N, s i =ᶠ[𝓝 x] 0 := by
    intro i
    obtain ⟨U, hxU, r, hr, hsr⟩ := hs i
    have hr0 : r = 0 := by
      rw [Scheme.IdealSheafData.ideal_bot] at hr
      exact hr
    have hgerm := regularGermHom_apply f k E U x hxU r
    rw [hr0, map_zero] at hgerm
    have hzero : (0 : NativeHolGerm k (SchemeComplexPoint f) x) =
        NativeHolGerm.mk (0 : SchemeComplexPoint f → ℂ) (holomorphicAt_const 0) := by
      apply Subtype.ext
      rfl
    rw [hzero] at hgerm
    have h := NativeHolGerm.mk_eq_mk_iff.mp hgerm
    rw [hsr, hr0]
    exact h.symm
  have hall : ∀ᶠ y in 𝓝 x, ∀ i : Fin N, s i y = 0 := by
    rw [eventually_all]
    exact fun i => hs0 i
  filter_upwards [hga, hall] with y hy hy0
  rw [hy]
  simp [hy0]

variable {k E}

/-- Under `MultiplierIdealAlgebraic`, the algebraic model of the multiplier ideal `𝓘(cφ)` of a
quasi-psh function on the nonempty `X(ℂ)` is not the zero ideal sheaf. -/
theorem algebraization_multiplierIdeal_ne_bot (hA : MultiplierIdealAlgebraic f k E)
    [Nonempty (SchemeComplexPoint f)] {φ : SchemeComplexPoint f → EReal}
    (hφ : IsGlobalQuasiPshPotential (n := k) φ) {c : ℝ} (hc : 0 < c) :
    algebraization f k E (multiplierIdeal (n := k) c φ) ≠ ⊥ := by
  intro hbot
  obtain ⟨x⟩ := ‹Nonempty (SchemeComplexPoint f)›
  obtain ⟨g, hg, hgne⟩ :=
    GlobalQuasiPshMultiplierPrincipalization.exists_nonzero_germ_of_isGlobalQuasiPshPotential
      hφ hc x
  have hmem : (analytificationIdeal f k E (⊥ : X.IdealSheafData)).mem x g := by
    rw [← hbot, analytificationIdeal_algebraization_eq f k E hA hφ hc]
    exact hg
  have h0 := eventually_eq_zero_of_mem_analytificationIdeal_bot k E hmem
  exact hgne (h0.mono fun y hy => by simpa using hy)

variable [IsIntegral X]

/-- **`φ^An(v_triv) = 0`** for `φ ∈ PSH(X, θ)`, conditionally on `MultiplierIdealAlgebraic`. -/
theorem potentialAn_trivial (hA : MultiplierIdealAlgebraic f k E)
    [Nonempty (SchemeComplexPoint f)] {φ : SchemeComplexPoint f → EReal}
    {θ : SmoothRealForm k (SchemeComplexPoint f) 2} (hφ : IsThetaPshPotential θ φ) :
    potentialAn k E φ (BerkovichPoint.trivial f) = 0 := by
  have := E.locallyOfFiniteType
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have hq : IsGlobalQuasiPshPotential (n := k) φ := ⟨hφ.1.quasiPlurisubharmonic, hφ.2⟩
  have h1 := BerkovichPoint.tendsto_potentialVal_of_multiplierIdealAlgebraic k E hA hφ
    (BerkovichPoint.trivial f)
  have h2 : Tendsto (fun j : ℕ => (BerkovichPoint.trivial f).multiplierIdealVal k E φ j / j)
      atTop (𝓝 0) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with j hj
    unfold BerkovichPoint.multiplierIdealVal
    rw [BerkovichPoint.trivial_idealVal_eq_zero (algebraization_multiplierIdeal_ne_bot hA hq
      (show (0 : ℝ) < j by exact_mod_cast hj)), ENNReal.zero_div]
  unfold potentialAn
  rw [tendsto_nhds_unique h1 h2]
  simp

variable [MeasurableSpace (SchemeComplexPoint f)] [BorelSpace (SchemeComplexPoint f)]
  [CompactSpace (SchemeComplexPoint f)] [ConnectedSpace (SchemeComplexPoint f)]
  {θ : AtlasClosedRealOneOneForm (ofFixedModel k (SchemeComplexPoint f))}

/-- **Source `eq:Gammamax`: `Γ^An(v_triv) = Γ_max`**, conditionally on
`MultiplierIdealAlgebraic`. -/
theorem naPotentialAnAt_trivial (hA : MultiplierIdealAlgebraic f k E) (Γ : SourceNAPotential θ)
    (ω : SourceKahlerForm k (SchemeComplexPoint f)) :
    naPotentialAnAt k E Γ ω (BerkovichPoint.trivial f) =
      (((Γ.component ω).val.max : ℝ) : EReal) := by
  have hterm : ∀ τ : Iio (Γ.component ω).val.max,
      potentialAn k E ((Γ.component ω).val.potential τ) (BerkovichPoint.trivial f) +
        ((τ : ℝ) : EReal) = ((τ : ℝ) : EReal) := by
    intro τ
    rw [potentialAn_trivial hA (naComponent_potential_isThetaPshPotential k Γ ω τ), zero_add]
  unfold naPotentialAnAt
  simp_rw [hterm]
  apply le_antisymm
  · exact iSup_le fun τ => EReal.coe_le_coe_iff.mpr (le_of_lt τ.2)
  · by_contra hcon
    rw [not_le] at hcon
    obtain ⟨q, hSq, hq⟩ := EReal.lt_iff_exists_real_btwn.mp hcon
    have hq' : q < (Γ.component ω).val.max := EReal.coe_lt_coe_iff.mp hq
    exact absurd hSq (not_lt.mpr (le_iSup (fun τ : Iio (Γ.component ω).val.max =>
      ((τ : ℝ) : EReal)) ⟨q, hq'⟩))

end Multiplier

end SGPT.NAPotential.Berkovich

end
