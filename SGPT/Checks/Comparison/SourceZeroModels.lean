import SGPT.NAPotential.DivDict2Unconditional
import SGPT.GAGA.H0SSchemeEmbedding
import SGPT.Foundations.Analysis.Pending.ZeroDimensionalQuasiPshMultiplierIdeals

/-! Original actual multiplier-unit and zero-dimensional formulas, independent of trace.
Fresh source ports of the corresponding NANSNonTrivRest/QwNANonTrivRestZero proofs.
Blueprint: source-comparison-slices.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.NAPotential.BJ.SourceZeroModels
open Set Filter
open scoped Topology ENNReal
open AlgebraicGeometry CategoryTheory IsLocalRing SGPT.Foundations.Schemes SGPT.Okounkov
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves SGPT.Foundations.Analysis.Pending
open SGPT.PSH.VariableComplexAtlas SGPT.NAPotential.Berkovich

section Units
variable {X : Scheme.{0}}
/-- The stalk of an ideal sheaf at `y` is the unit ideal iff some section over an affine
neighbourhood of `y` does not vanish at `y`. -/
theorem stalkIdeal_eq_top_iff (𝔞 : X.IdealSheafData) (y : X) :
    stalkIdeal 𝔞 y = ⊤ ↔
      ∃ (U : X.affineOpens) (r : Γ(X, U)), r ∈ 𝔞.ideal U ∧ y ∈ X.basicOpen r := by
  constructor
  · intro h
    by_contra hcon
    push Not at hcon
    have hle : stalkIdeal 𝔞 y ≤ maximalIdeal (X.presheaf.stalk y) := by
      apply iSup₂_le
      intro U hU
      rw [Ideal.map_le_iff_le_comap]
      intro r hr
      rw [Ideal.mem_comap, mem_maximalIdeal, mem_nonunits_iff]
      intro hunit
      exact hcon U r hr ((X.mem_basicOpen r y hU).mpr hunit)
    rw [h] at hle
    exact (maximalIdeal.isMaximal (X.presheaf.stalk y)).ne_top (top_le_iff.mp hle)
  · rintro ⟨U, r, hr, hy⟩
    have hyU : y ∈ (U : X.Opens) := X.basicOpen_le r hy
    exact Ideal.eq_top_of_isUnit_mem _ (germ_mem_stalkIdeal 𝔞 U hyU hr)
      ((X.mem_basicOpen r y hyU).mp hy)

end Units

section ComplexPoints

variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ))

/-- `Y(ℂ) ⊆ X(ℂ)`: the complex points of `Y = closure {y}`. -/
def subvarietyPoints (y : X) : Set (SchemeComplexPoint f) :=
  {q | y ⤳ schemeComplexPointImage f q}

variable {f}

/-- Complex points are dense in every subvariety: every open set meeting `Y = closure {y}`
(i.e. containing `y`) contains a complex point of `Y` (Nullstellensatz). -/
theorem exists_mem_subvarietyPoints [LocallyOfFiniteType f] {y : X} {W : X.Opens} (hy : y ∈ W) :
    ∃ q ∈ subvarietyPoints f y, schemeComplexPointImage f q ∈ W := by
  obtain ⟨_, ⟨V, hV, rfl⟩, hyV, hVW⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hy W.isOpen
  set P := hV.primeIdealOf ⟨y, hyV⟩
  obtain ⟨M, hM, hPM⟩ := Ideal.exists_le_maximal P.asIdeal P.isPrime.ne_top
  obtain ⟨q, hq⟩ := exists_schemeComplexPoint_fromSpec f hV M hM
  refine ⟨q, ?_, ?_⟩
  · show y ⤳ schemeComplexPointImage f q
    have hy' : hV.fromSpec P = y := hV.fromSpec_primeIdealOf ⟨y, hyV⟩
    rw [hq, ← hy']
    exact ((PrimeSpectrum.le_iff_specializes P ⟨M, hM.isPrime⟩).mp hPM).map
      hV.fromSpec.continuous
  · rw [hq]
    apply hVW
    rw [← hV.range_fromSpec]
    exact ⟨_, rfl⟩

end ComplexPoints

section Multiplier

variable {X : Scheme.{0}} {f : X ⟶ Spec (.of ℂ)} {n : ℕ} [SmoothOfRelativeDimension n f]
  {E : ClosedProjectiveEmbedding f} [IsProper f]

local instance nansPointTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance nansPointCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f n
local instance nansPointManifold : IsComplexManifold n (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f n

/-- **The algebraic model of `𝓘(cφ)` along `Y`**: for quasi-psh `φ` and `c > 0`, the algebraic
coherent ideal `𝔞` with `𝔞^an = 𝓘(cφ)` is the unit ideal at the generic point of `Y` iff
`1 ∈ 𝓘(cφ)_q` (`e^{-cφ}` is integrable near `q`) for some complex point `q ∈ Y(ℂ)`. -/
theorem stalkIdeal_algebraization_multiplierIdeal_eq_top_iff {φ : SchemeComplexPoint f → EReal}
    (hφ : IsGlobalQuasiPshPotential (n := n) φ) {c : ℝ} (hc : 0 < c) (y : X) :
    stalkIdeal (algebraization f n E (multiplierIdeal (n := n) c φ)) y = ⊤ ↔
      ∃ q ∈ subvarietyPoints f y, (multiplierIdeal (n := n) c φ).mem q (fun _ => 1) := by
  have := E.locallyOfFiniteType
  have hAn := analytificationIdeal_algebraization_eq f n E
    (SGPT.GAGA.H0S.multiplierIdealAlgebraic f E n) hφ hc
  set 𝔞 := algebraization f n E (multiplierIdeal (n := n) c φ)
  constructor
  · intro h
    obtain ⟨U, r, hr, hyb⟩ := (stalkIdeal_eq_top_iff 𝔞 y).mp h
    obtain ⟨q, hyq, hqb⟩ := exists_mem_subvarietyPoints (f := f) hyb
    have hqU : schemeComplexPointImage f q ∈ (U : X.Opens) := X.basicOpen_le r hqb
    have hne := (SGPT.GAGA.H0S.schemeOpenRegularFunction_ne_zero_iff f E n U r q hqU).mpr hqb
    have hmem : (analytificationIdeal f n E 𝔞).mem q (schemeOpenRegularFunction f n E U r) := by
      refine ⟨schemeOpenRegularFunction_holomorphicAt f n E U r q hqU, 1,
        fun _ => schemeOpenRegularFunction f n E U r, fun _ => fun _ => 1, ?_, ?_, ?_⟩
      · intro _
        exact ⟨U, hqU, r, hr, rfl⟩
      · intro _
        exact holomorphicAt_const 1
      · filter_upwards with z
        simp
    rw [hAn] at hmem
    exact ⟨q, hyq, SkodaIntegrability.one_mem_multiplierIdeal_of_notMem_zeroLocus
      fun hz => hne (hz _ hmem)⟩
  · rintro ⟨q, hyq, h1⟩
    rw [← hAn] at h1
    obtain ⟨-, N, s, a, hs, -, hsum⟩ := h1
    have hval : ∑ i, a i q * s i q = 1 := hsum.self_of_nhds.symm
    obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero
      (show ∑ i, a i q * s i q ≠ 0 by rw [hval]; exact one_ne_zero)
    have hsi : s i q ≠ 0 := right_ne_zero_of_mul hi
    obtain ⟨U, hqU, r, hr, hsr⟩ := hs i
    rw [hsr] at hsi
    have hb := (SGPT.GAGA.H0S.schemeOpenRegularFunction_ne_zero_iff f E n U r q hqU).mp hsi
    have hyb : y ∈ X.basicOpen r := (show y ⤳ schemeComplexPointImage f q from hyq).mem_open
      (X.basicOpen r).isOpen hb
    exact (stalkIdeal_eq_top_iff 𝔞 y).mpr ⟨U, r, hr, hyb⟩

end Multiplier

section Zero
variable {X : Scheme.{0}} {f : X ⟶ Spec (.of ℂ)} [SmoothOfRelativeDimension 0 f]
  {E : ClosedProjectiveEmbedding f} [IsProper f]

local instance qwNAZeroPointTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance qwNAZeroPointCharts : ChartedSpace (ComplexModel 0) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f 0
local instance qwNAZeroPointManifold : IsComplexManifold 0 (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f 0

/-- In dimension zero the algebraic models of the multiplier ideals of a quasi-psh `φ` are the
unit ideal at every point: `v(𝓘(kφ)) = 0` for `k > 0` and every `v ∈ X^An`. -/
theorem multiplierIdealVal_eq_zero_of_dim_zero {φ : SchemeComplexPoint f → EReal}
    (hφ : IsGlobalQuasiPshPotential (n := 0) φ) (v : BerkovichPoint f) {k : ℕ} (hk : 0 < k) :
    v.multiplierIdealVal 0 E φ k = 0 := by
  have := E.locallyOfFiniteType
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have hk' : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  unfold BerkovichPoint.multiplierIdealVal
  rw [BerkovichPoint.idealVal_eq_zero_iff,
    stalkIdeal_algebraization_multiplierIdeal_eq_top_iff hφ hk']
  obtain ⟨q, hq, -⟩ := exists_mem_subvarietyPoints (f := f) (W := ⊤) (y := v.center) trivial
  exact ⟨q, hq, (ZeroDimensionalQuasiPshMultiplierIdeals.mem_multiplierIdeal_iff_holomorphicAt
    hφ hk' q _).mpr (holomorphicAt_const 1)⟩

/-- **In dimension zero `φ^An ≡ 0` on `X^An`** for every quasi-psh `φ`. -/
theorem potentialAn_eq_zero_of_dim_zero {φ : SchemeComplexPoint f → EReal}
    (hφ : IsGlobalQuasiPshPotential (n := 0) φ) (v : BerkovichPoint f) :
    potentialAn 0 E φ v = 0 := by
  have hlim : Tendsto (fun k : ℕ => v.multiplierIdealVal 0 E φ k / k) atTop (𝓝 0) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with k hk
    rw [multiplierIdealVal_eq_zero_of_dim_zero hφ v hk, ENNReal.zero_div]
  unfold potentialAn BerkovichPoint.potentialVal
  rw [hlim.limUnder_eq]
  simp

variable [MeasurableSpace (SchemeComplexPoint f)] [BorelSpace (SchemeComplexPoint f)]
  [CompactSpace (SchemeComplexPoint f)] [ConnectedSpace (SchemeComplexPoint f)]
  {θ : AtlasClosedRealOneOneForm (ofFixedModel 0 (SchemeComplexPoint f))}

/-- `sup_{τ < a} τ = a` in `[-∞, ∞]`. -/
theorem iSup_Iio_coe_eq (a : ℝ) : (⨆ τ : Iio a, ((τ : ℝ) : EReal)) = (a : EReal) := by
  refine le_antisymm (iSup_le fun τ => EReal.coe_le_coe_iff.mpr τ.2.le) ?_
  refine le_of_forall_lt fun b hb => ?_
  obtain ⟨r, hbr, hra⟩ := EReal.lt_iff_exists_real_btwn.mp hb
  exact lt_iSup_iff.mpr ⟨⟨r, EReal.coe_lt_coe_iff.mp hra⟩, hbr⟩

/-- **In dimension zero `Γ^An ≡ Γ_max` on `X^An`** (`eq:psiandef`, every Kähler index). -/
theorem naPotentialAnAt_eq_of_dim_zero (Γ : SourceNAPotential θ)
    (ω : SourceKahlerForm 0 (SchemeComplexPoint f)) (v : BerkovichPoint f) :
    naPotentialAnAt 0 E Γ ω v = ((Γ.component ω).val.max : EReal) := by
  unfold naPotentialAnAt
  have h : ∀ τ : Iio (Γ.component ω).val.max,
      potentialAn 0 E ((Γ.component ω).val.potential τ) v + ((τ : ℝ) : EReal) =
        ((τ : ℝ) : EReal) := fun τ => by
    have hτ := naComponent_potential_isThetaPshPotential 0 Γ ω τ
    rw [potentialAn_eq_zero_of_dim_zero ⟨hτ.1.quasiPlurisubharmonic, hτ.2⟩ v, zero_add]
  simp_rw [h]
  exact iSup_Iio_coe_eq _


end Zero
end SGPT.NAPotential.BJ.SourceZeroModels
end
