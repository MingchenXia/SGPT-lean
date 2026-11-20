import SGPT.IGood.DXMainUpper
import SGPT.IGood.DXMainTensorMetric

/-!
# The twisted asymptotic Riemann–Roch formula `thm:DXmain1`: the upper bound

Source `thm:DXmain1` with an arbitrary twisting line bundle `T`:
`limsup_{k → ∞} n! h⁰(X, T ⊗ L^k ⊗ 𝓘(kφ)) / kⁿ ≤ vol θ_φ`. Blueprint `claude-dxmain:twisted`.

Setting as in `SGPT.IGood.DXMainUpper`. `T ⊗ L^k = bundleTensor T (bundleTensorPower L k)` and
`H⁰(X, T ⊗ L^k ⊗ 𝓘(kφ))` is the space of its (degree-one) sections whose coefficient in every
local frame lies in `𝓘(kφ)` — the condition of the twisted polytopes `Δ_{k,T}(θ, φ)` of
`def:DeltakT` (`SGPT.Okounkov.twistedMultiplierValues`).

## Main results

* `twistedMultiplierSubmodule`, `twistedMultiplierH0`: the space `H⁰(X, T ⊗ L^k ⊗ 𝓘(kφ))` and its
  dimension.
* `limsup_le_iVolume_of_latticeCount`: the counting part of the upper bound, abstracted.
* **`limsup_twistedMultiplierH0_le`**: the upper bound of `thm:DXmain1` for every `T`.

The potential of a twisted section `s` is `k⁻¹ log |s|²_{h_T ⊗ h^k}`, whose curvature is
`θ + k⁻¹ c₁(T, h_T)` (`SchemeLineBundleMetric.curvature_tensorProduct`); the error `k⁻¹ c₁(T, h_T)` is
absorbed by the slack `ε ω` of the Kähler approximation for `k ≫ 0`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.IGood.DXMain

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Set Filter MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
open SGPT.Okounkov SGPT.LineBundle SGPT.PSH
open SGPT.Okounkov.TranscendentalCore SGPT.Okounkov.TranscendentalPartial
open scoped Topology ENNReal NNReal Pointwise

variable {X : Scheme} (f : X ⟶ Spec (.of ℂ)) (n : ℕ) [SmoothOfRelativeDimension n f]
  (E : ClosedProjectiveEmbedding f)

local instance dxTwTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance dxTwCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f n
local instance dxTwManifold [IsSeparated f] [QuasiCompact f] :
    IsComplexManifold n (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f n

section IdealSections

variable {L : X.Modules}

/-- The zero section lies in `H⁰(X, L^d ⊗ 𝓘(cφ))` for `c > 0`. -/
theorem isIdealSection_multiplierIdeal_zero (φ : SchemeComplexPoint f → EReal) {c : ℝ}
    (hc : 0 < c) (d : ℕ) :
    IsIdealSection f n E (multiplierIdeal (n := n) c φ) d (0 : bundlePowerGlobalSections L d) := by
  let := E.isSeparated
  let := E.quasiCompact
  intro U α p hp
  set e := complexChartAt (n := n) p
  have hpe : p ∈ e.val.source := mem_complexChartAt_source p
  have hDopen : IsOpen (e.val.target ∩ e.val.symm ⁻¹' (schemeComplexPointImage f ⁻¹' U)) :=
    e.val.isOpen_inter_preimage_symm (U.isOpen.preimage (schemeComplexPointImage_continuous f))
  have hz0D : e.val p ∈ e.val.target ∩ e.val.symm ⁻¹' (schemeComplexPointImage f ⁻¹' U) := by
    refine ⟨e.val.map_source hpe, ?_⟩
    change schemeComplexPointImage f (e.val.symm (e.val p)) ∈ U
    rw [e.val.left_inv hpe]
    exact hp
  refine ⟨schemeOpenRegularFunction_holomorphicAt f n E U _ p hp, ?_⟩
  refine (multiplierIntegrableAt_zero (chartFunction φ e) hc (e.val p) volume).congr
    (Filter.EventuallyEq.refl _ _) ?_
  filter_upwards [hDopen.mem_nhds hz0D] with z hz
  exact (SGPT.IGood.sectionFrameCoefficient_zero α d hz.2).symm

/-- Sums of sections of `L^d ⊗ 𝓘(cφ)` (quasi-psh `φ`). -/
theorem isIdealSection_multiplierIdeal_add {φ : SchemeComplexPoint f → EReal}
    (hφ : letI := E.isSeparated; letI := E.quasiCompact;
      ManifoldQuasiPlurisubharmonic (n := n) φ)
    {c : ℝ} {d : ℕ} {s t : bundlePowerGlobalSections L d}
    (hs : IsIdealSection f n E (multiplierIdeal (n := n) c φ) d s)
    (ht : IsIdealSection f n E (multiplierIdeal (n := n) c φ) d t) :
    IsIdealSection f n E (multiplierIdeal (n := n) c φ) d (s + t) := by
  let := E.isSeparated
  let := E.quasiCompact
  intro U α p hp
  obtain ⟨-, hsi⟩ := hs U α p hp
  obtain ⟨-, hti⟩ := ht U α p hp
  set e := complexChartAt (n := n) p
  have hpe : p ∈ e.val.source := mem_complexChartAt_source p
  have hz := e.val.map_source hpe
  have hD : IsOpen (e.val.target ∩ e.val.symm ⁻¹' (schemeComplexPointImage f ⁻¹' U)) :=
    e.val.isOpen_inter_preimage_symm (U.isOpen.preimage (schemeComplexPointImage_continuous f))
  have hz0D : e.val p ∈ e.val.target ∩ e.val.symm ⁻¹' (schemeComplexPointImage f ⁻¹' U) := by
    refine ⟨hz, ?_⟩
    change schemeComplexPointImage f (e.val.symm (e.val p)) ∈ U
    rw [e.val.left_inv hpe]
    exact hp
  refine ⟨schemeOpenRegularFunction_holomorphicAt f n E U _ p hp, ?_⟩
  refine (multiplierIntegrableAt_add (hφ e _ hz) hsi hti).congr
    (Filter.EventuallyEq.refl _ _) ?_
  filter_upwards [hD.mem_nhds hz0D] with z hz'
  exact (sectionFrameCoefficient_add f n E α d s t hz'.2).symm

/-- Complex multiples of sections of `L^d ⊗ 𝓘(cφ)`. -/
theorem isIdealSection_multiplierIdeal_smul {φ : SchemeComplexPoint f → EReal} {c : ℝ} {d : ℕ}
    (b : ℂ) {s : SectionSpace f L d}
    (hs : IsIdealSection f n E (multiplierIdeal (n := n) c φ) d s) :
    IsIdealSection f n E (multiplierIdeal (n := n) c φ) d (b • s : SectionSpace f L d) := by
  let := E.isSeparated
  let := E.quasiCompact
  intro U α p hp
  obtain ⟨-, hsi⟩ := hs U α p hp
  set e := complexChartAt (n := n) p
  have hpe : p ∈ e.val.source := mem_complexChartAt_source p
  have hz := e.val.map_source hpe
  have hD : IsOpen (e.val.target ∩ e.val.symm ⁻¹' (schemeComplexPointImage f ⁻¹' U)) :=
    e.val.isOpen_inter_preimage_symm (U.isOpen.preimage (schemeComplexPointImage_continuous f))
  have hz0D : e.val p ∈ e.val.target ∩ e.val.symm ⁻¹' (schemeComplexPointImage f ⁻¹' U) := by
    refine ⟨hz, ?_⟩
    change schemeComplexPointImage f (e.val.symm (e.val p)) ∈ U
    rw [e.val.left_inv hpe]
    exact hp
  refine ⟨schemeOpenRegularFunction_holomorphicAt f n E U _ p hp, ?_⟩
  refine (multiplierIntegrableAt_const_mul hsi b).congr (Filter.EventuallyEq.refl _ _) ?_
  filter_upwards [hD.mem_nhds hz0D] with z hz'
  exact (sectionFrameCoefficient_smul f n E α d b s hz'.2).symm

/-- **`H⁰(X, T ⊗ L^k ⊗ 𝓘(kφ))`** (the twisted section spaces of `thm:DXmain1` and `def:DeltakT`):
the degree-one sections of `T ⊗ L^k` whose coefficient in every local frame lies in `𝓘(kφ)`
(with `𝓘(0·φ) = 𝒪_X`), a complex subspace of `H⁰(X, T ⊗ L^k)`. -/
def twistedMultiplierSubmodule {φ : SchemeComplexPoint f → EReal}
    (hφ : letI := E.isSeparated; letI := E.quasiCompact;
      ManifoldQuasiPlurisubharmonic (n := n) φ) (T L : X.Modules) (k : ℕ) :
    Submodule ℂ (SectionSpace f (bundleTensor T (bundleTensorPower L k)) 1) where
  carrier := {s | k = 0 ∨ IsIdealSection f n E (multiplierIdeal (n := n) (k : ℝ) φ) 1 s}
  zero_mem' := by
    rcases Nat.eq_zero_or_pos k with h0 | hk
    · exact Or.inl h0
    · exact Or.inr (isIdealSection_multiplierIdeal_zero f n E φ (by exact_mod_cast hk) 1)
  add_mem' := by
    rintro s t (h0 | hs) (h0' | ht)
    · exact Or.inl h0
    · exact Or.inl h0
    · exact Or.inl h0'
    · exact Or.inr (isIdealSection_multiplierIdeal_add f n E hφ hs ht)
  smul_mem' := by
    rintro b s (h0 | hs)
    · exact Or.inl h0
    · exact Or.inr (isIdealSection_multiplierIdeal_smul f n E b hs)

/-- **`h⁰(X, T ⊗ L^k ⊗ 𝓘(kφ))`**. -/
def twistedMultiplierH0 {φ : SchemeComplexPoint f → EReal}
    (hφ : letI := E.isSeparated; letI := E.quasiCompact;
      ManifoldQuasiPlurisubharmonic (n := n) φ) (T L : X.Modules) (k : ℕ) : ℕ :=
  Module.finrank ℂ (twistedMultiplierSubmodule f n E hφ T L k)

end IdealSections

section Comparison

/-- **From `𝓘` to `𝓘_∞`, uniformly in the bundle**: for `ψ` with analytic singularities and
`t ∈ (0, 1)` there is `k₀` such that for all `k ≥ k₀`, every line bundle `L'` with metric `K`, every
degree `d` and every `s ∈ H⁰(X, L'^d ⊗ 𝓘(kψ))`, `k⁻¹ log |s|²_K ≤ (1 - t) ψ + C`. -/
theorem exists_singularityLE_scaledLogNormSq {ψ : SchemeComplexPoint f → EReal}
    (hψ : QuasiEquisingularApproximation.HasManifoldAnalyticSingularityType (n := n) ψ)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    ∃ k₀ : ℕ, 0 < k₀ ∧ ∀ k : ℕ, k₀ ≤ k → ∀ {L' : X.Modules} (a' : LineBundleAtlas L')
      (K : SchemeLineBundleMetric f n E L') (d : ℕ) (s : bundlePowerGlobalSections L' d),
      IsIdealSection f n E (multiplierIdeal (n := n) (k : ℝ) ψ) d s →
        SingularityLE (fun p => (((k : ℝ)⁻¹ : ℝ) : EReal) * K.sectionLogNormSq a' d s p)
          (fun x => ((1 - t : ℝ) : EReal) * ψ x) := by
  let := E.isSeparated
  let := E.quasiCompact
  let := E.analyticCompact
  have h1t : 0 < 1 - t := by linarith
  set ε : ℝ := t / (1 - t) with hε
  have hε0 : 0 < ε := div_pos ht0 h1t
  have hψ' : (VariableComplexAtlas.ofFixedModel n (SchemeComplexPoint f)).HasRationalAnalyticChartType
      ψ := fun e z hz => hψ e z hz
  obtain ⟨s₀, hs₀, hI⟩ := SGPT.PSH.MultiplierIdealInf.exists_multiplierIdeal_le_inftyIdeal hψ' hε0
  refine ⟨⌈s₀ / (1 - t)⌉₊ + 1, Nat.succ_pos _, fun k hk L' a' K d s hs => ?_⟩
  have hkpos : 0 < k := lt_of_lt_of_le (Nat.succ_pos _) hk
  have hkR : (0 : ℝ) < k := by exact_mod_cast hkpos
  set σ : ℝ := k * (1 - t) with hσ
  have hσs₀ : s₀ ≤ σ := by
    have h1 : s₀ / (1 - t) ≤ k := by
      calc s₀ / (1 - t) ≤ ⌈s₀ / (1 - t)⌉₊ := Nat.le_ceil _
        _ ≤ (k : ℝ) := by exact_mod_cast (Nat.le_succ _).trans hk
    rw [div_le_iff₀ h1t] at h1
    linarith
  have hσk : σ * (1 + ε) = k := by
    rw [hσ, hε]
    field_simp
    ring
  have hI' := hI σ hσs₀
  rw [hσk] at hI'
  refine RestrictedIdealWeight.moreSingularOn_of_forall_moreSingularAlong_nhdsWithin
    isCompact_univ fun p _ => ?_
  rw [nhdsWithin_univ]
  let U := schemePointFrameOpen f p a'
  let α := schemePointFrame f p a'
  have hp : schemeComplexPointImage f p ∈ U := schemePointFrame_mem f p a'
  have hmem := hs U α p hp
  have hmem1 : (multiplierIdeal (n := n) 1 fun x => ((k : ℝ) : EReal) * ψ x).mem p
      (sectionFrameCoefficient f n E α d s) := by
    refine ⟨hmem.1, ?_⟩
    have h := hmem.2
    refine (SGPT.PSH.MultiplierIdealInf.multiplierIntegrableAt_coe_mul_iff one_pos hkR).mpr ?_
    rw [one_mul]
    exact h
  obtain ⟨C, hC⟩ := (SGPT.PSH.mem_inftyIdeal_iff_log_bound.mp (hI' p _ hmem1)).2
  obtain ⟨B, hB⟩ := eventually_log_frameNormSq_le f n E K α hp
  have hUo : IsOpen (schemeComplexPointImage f ⁻¹' U) :=
    U.isOpen.preimage (schemeComplexPointImage_continuous f)
  refine ⟨(k : ℝ)⁻¹ * C + (k : ℝ)⁻¹ * ((d : ℝ) * |B|), ?_⟩
  filter_upwards [hC, hB, hUo.mem_nhds hp] with q hqC hqB hqU
  rw [K.sectionLogNormSq_frame a' α d s q hqU]
  have hkinv : (0 : ℝ) < (k : ℝ)⁻¹ := inv_pos.mpr hkR
  rw [SGPT.PSH.MultiplierIdealInf.coe_mul_add_coe hkinv]
  have hA : (((k : ℝ)⁻¹ : ℝ) : EReal) *
      SGPT.Foundations.Analysis.logNormSq (sectionFrameCoefficient f n E α d s q) ≤
      (((k : ℝ)⁻¹ : ℝ) : EReal) * ((σ : EReal) * ψ q + (C : EReal)) :=
    mul_le_mul_of_nonneg_left hqC (EReal.coe_nonneg.mpr hkinv.le)
  rw [SGPT.PSH.MultiplierIdealInf.coe_mul_add_coe hkinv, ← mul_assoc, ← EReal.coe_mul] at hA
  have hks : (k : ℝ)⁻¹ * σ = 1 - t := by
    rw [hσ]
    field_simp
  rw [hks] at hA
  have hlog : (k : ℝ)⁻¹ * ((d : ℝ) * Real.log (K.frameNormSq α q)) ≤
      (k : ℝ)⁻¹ * ((d : ℝ) * |B|) := by
    gcongr
    exact hqB.trans (le_abs_self B)
  calc (((k : ℝ)⁻¹ : ℝ) : EReal) *
        SGPT.Foundations.Analysis.logNormSq (sectionFrameCoefficient f n E α d s q) +
        (((k : ℝ)⁻¹ * ((d : ℝ) * Real.log (K.frameNormSq α q)) : ℝ) : EReal)
      ≤ ((1 - t : ℝ) : EReal) * ψ q + (((k : ℝ)⁻¹ * C : ℝ) : EReal) +
          (((k : ℝ)⁻¹ * ((d : ℝ) * |B|) : ℝ) : EReal) :=
        add_le_add hA (EReal.coe_le_coe_iff.mpr hlog)
    _ = ((1 - t : ℝ) : EReal) * ψ q + (((k : ℝ)⁻¹ * C + (k : ℝ)⁻¹ * ((d : ℝ) * |B|) : ℝ) : EReal) := by
        rw [EReal.coe_add, add_assoc]

end Comparison

section Count

variable [IsIntegral X] (Y : Fin (n + 1) → Set (SchemeComplexPoint f)) (hY : IsSmoothFlag Y)

/-- The lattice count for an arbitrary subspace: if every nonzero `s ∈ V ⊆ H⁰(X, L'^d)` has
`k⁻¹ ν(s) ∈ K`, then `dim V ≤ #(ℤⁿ ∩ k K)`. -/
theorem finrank_le_integerLatticeCount {L' : X.Modules} (a' : LineBundleAtlas L') {d : ℕ}
    (V : Submodule ℂ (SectionSpace f L' d)) {K : Set (Fin n → ℝ)} (hK : IsCompact K) {k : ℕ}
    (hk : 0 < k)
    (hmem : ∀ (s : SectionSpace f L' d) (hs : s ≠ 0), s ∈ V →
      (k : ℝ)⁻¹ • (fun i => (schemeFubiniStudySectionVector f n E Y hY a' d s hs i : ℝ)) ∈ K) :
    Module.finrank ℂ V ≤ SGPT.AlmostSemigroup.Counting.integerLatticeCount K k := by
  rw [← card_sectionValues_eq_finrank f n E Y hY a' d V,
    SGPT.AlmostSemigroup.Counting.integerLatticeCount]
  have hfin := SGPT.AlmostSemigroup.Counting.finite_integerPoints_dilate hK k
  have : Finite (SGPT.AlmostSemigroup.Counting.integerPoints ((k : ℝ) • K)) := hfin.to_subtype
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  refine Nat.card_le_card_of_injective
    (fun v => ⟨fun i => ((v.1 i : ℕ) : ℤ), ?_⟩) ?_
  · obtain ⟨s, hs, hsV, hv⟩ := v.2
    have h := hmem s hs hsV
    change SGPT.AlmostSemigroup.Counting.integerCast (fun i => ((v.1 i : ℕ) : ℤ)) ∈ (k : ℝ) • K
    have heq : SGPT.AlmostSemigroup.Counting.integerCast (fun i => ((v.1 i : ℕ) : ℤ)) =
        (k : ℝ) • ((k : ℝ)⁻¹ •
          (fun i => (schemeFubiniStudySectionVector f n E Y hY a' d s hs i : ℝ))) := by
      rw [smul_smul, mul_inv_cancel₀ hkR, one_smul, hv]
      funext i
      simp [SGPT.AlmostSemigroup.Counting.integerCast]
    rw [heq]
    exact Set.smul_mem_smul_set h
  · intro v w hvw
    apply Subtype.ext
    funext i
    have h : ((v.1 i : ℕ) : ℤ) = ((w.1 i : ℕ) : ℤ) := congrFun (congrArg Subtype.val hvw) i
    exact_mod_cast h

end Count

section Twisted

variable [IsIntegral X] {m : ℕ} [SmoothOfRelativeDimension (m + 1) f]
  (Y : Fin (m + 1 + 1) → Set (SchemeComplexPoint f)) (hY : IsSmoothFlag Y)
  {T L : X.Modules} (aT : LineBundleAtlas T) (HT : SchemeLineBundleMetric f (m + 1) E T)
  (a : LineBundleAtlas L) (H : SchemeLineBundleMetric f (m + 1) E L)

omit [IsIntegral X] in
/-- `I(cφ) ⊆ I(cψ)` on sections of any degree, for `φ ⪯ ψ` with `ψ` quasi-psh. -/
theorem isIdealSection_mono_of_singularityLE {φ ψ : SchemeComplexPoint f → EReal}
    (hψ : letI := E.isSeparated; letI := E.quasiCompact;
      ManifoldQuasiPlurisubharmonic (n := m + 1) ψ)
    (hle : SingularityLE φ ψ) {c : ℝ} {L' : X.Modules} {d : ℕ}
    {s : bundlePowerGlobalSections L' d}
    (hs : IsIdealSection f (m + 1) E (multiplierIdeal (n := m + 1) c φ) d s) :
    IsIdealSection f (m + 1) E (multiplierIdeal (n := m + 1) c ψ) d s := by
  let := E.isSeparated
  let := E.quasiCompact
  intro U α p hp
  obtain ⟨hhol, hint⟩ := hs U α p hp
  refine ⟨hhol, ?_⟩
  set e := complexChartAt (n := m + 1) p
  have hz := e.val.map_source (mem_complexChartAt_source p)
  obtain ⟨C, hC⟩ := (singularityLE_iff_exists_real φ ψ).mp hle
  exact multiplierIntegrableAt_of_moreSingularAt (hψ e _ hz)
    ⟨C, Filter.Eventually.of_forall fun z => hC _⟩ hint

/-- The product metric `h_T ⊗ h^k` on `T ⊗ L^k`. -/
def twistMetric (k : ℕ) :
    SchemeLineBundleMetric f (m + 1) E (bundleTensor T (bundleTensorPower L k)) :=
  HT.tensorProduct (H.tensorPower a k) aT (a.tensorPower k)

/-- The atlas of `T ⊗ L^k` by the tensor frames of the atlases of `T` and `L^k`. -/
def twistAtlas (k : ℕ) : LineBundleAtlas (bundleTensor T (bundleTensorPower L k)) :=
  pairwiseTensorAtlas aT (a.tensorPower k)

/-- The normalized potential `k⁻¹ log |s|²_{h_T ⊗ h^k}` of a section of `T ⊗ L^k`. -/
def twistedPotential (k : ℕ) (s : bundlePowerGlobalSections (bundleTensor T (bundleTensorPower L k)) 1) :
    SchemeComplexPoint f → EReal :=
  fun p => (((k : ℝ)⁻¹ : ℝ) : EReal) *
    (twistMetric f E aT HT a H k).sectionLogNormSq (twistAtlas aT a k) 1 s p

omit [IsIntegral X] in
/-- `c₁(T ⊗ L^k, h_T ⊗ h^k) = c₁(T, h_T) + k c₁(L, h)`. -/
theorem curvature_twistMetric (k : ℕ) :
    letI := E.isSeparated
    letI := E.quasiCompact
    ((twistMetric f E aT HT a H k).curvature (twistAtlas aT a k)).val.GeometricallyEq
      (HT.curvature aT + (k : ℝ) • H.curvature a).val := by
  let := E.isSeparated
  let := E.quasiCompact
  have h1 := HT.curvature_tensorProduct (H.tensorPower a k) aT (a.tensorPower k)
    (twistAtlas aT a k)
  have h2 := H.curvature_tensorPower a k
  intro e u hu
  have e1 := h1 e hu
  have e2 := h2 e hu
  change ((twistMetric f E aT HT a H k).curvature (twistAtlas aT a k)).val.coeff e u =
    (HT.curvature aT + (k : ℝ) • H.curvature a).val.coeff e u
  refine e1.trans ?_
  rw [ClosedRealOneOneForm.coeff_add, ClosedRealOneOneForm.coeff_add, e2]

theorem isThetaPshPotential_twistedPotential {k : ℕ} (hk : 0 < k)
    {s : bundlePowerGlobalSections (bundleTensor T (bundleTensorPower L k)) 1} (hs : s ≠ 0) :
    letI := E.isSeparated
    letI := E.quasiCompact
    IsThetaPshPotential (H.curvature a + ((k : ℝ)⁻¹) • HT.curvature aT).val
      (twistedPotential f E aT HT a H k s) := by
  let := E.isSeparated
  let := E.quasiCompact
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hu := (twistMetric f E aT HT a H k).isThetaPshPotential_sectionLogNormSq
    (twistAtlas aT a k) 1 s hs
  have h2 := TranscendentalCore.isThetaPshPotential_nonneg_smul hu (inv_nonneg.mpr hkR.le)
  have hgeq : (((k : ℝ)⁻¹) • (((1 : ℕ) : ℝ) •
      (twistMetric f E aT HT a H k).curvature (twistAtlas aT a k))).val.GeometricallyEq
      (H.curvature a + ((k : ℝ)⁻¹) • HT.curvature aT).val := by
    intro e u hu'
    have hc := curvature_twistMetric f E aT HT a H k e hu'
    change (((k : ℝ)⁻¹) • (((1 : ℕ) : ℝ) •
      (twistMetric f E aT HT a H k).curvature (twistAtlas aT a k))).val.coeff e u =
        (H.curvature a + ((k : ℝ)⁻¹) • HT.curvature aT).val.coeff e u
    rw [ClosedRealOneOneForm.coeff_smul, ClosedRealOneOneForm.coeff_smul, hc,
      ClosedRealOneOneForm.coeff_add, ClosedRealOneOneForm.coeff_add,
      ClosedRealOneOneForm.coeff_smul, ClosedRealOneOneForm.coeff_smul,
      Nat.cast_one, one_smul, smul_add, smul_smul, inv_mul_cancel₀ hkR.ne', one_smul]
    exact add_comm _ _
  exact (hgeq.thetaPshPotential_iff _).mp h2

theorem hasManifoldAnalyticSingularityType_twistedPotential (k : ℕ)
    {s : bundlePowerGlobalSections (bundleTensor T (bundleTensorPower L k)) 1} (hs : s ≠ 0) :
    letI := E.isSeparated
    letI := E.quasiCompact
    QuasiEquisingularApproximation.HasManifoldAnalyticSingularityType (n := m + 1)
      (twistedPotential f E aT HT a H k s) := by
  let := E.isSeparated
  let := E.quasiCompact
  have h := ((twistMetric f E aT HT a H k).sectionLogNormSq_hasAnalyticSingularities
    (twistAtlas aT a k) 1 s hs).hasManifoldAnalyticSingularityType
  have h' := TranscendentalCore.hasManifoldAnalyticSingularityType_nonneg_rat_smul h
    (r := ((k : ℚ))⁻¹) (by positivity)
  have hcast : ((((k : ℚ))⁻¹ : ℚ) : ℝ) = (k : ℝ)⁻¹ := by push_cast; ring
  have hfun : twistedPotential f E aT HT a H k s =
      fun x => (((((k : ℚ))⁻¹ : ℚ) : ℝ) : EReal) *
        (twistMetric f E aT HT a H k).sectionLogNormSq (twistAtlas aT a k) 1 s x := by
    funext x
    rw [hcast]
    rfl
  rw [hfun]
  exact h'

/-- `ν(ψ_s) = k⁻¹ ν(s)` for twisted sections. -/
theorem flagValuation_twistedPotential (k : ℕ)
    (s : bundlePowerGlobalSections (bundleTensor T (bundleTensorPower L k)) 1) (hs : s ≠ 0) :
    TranscendentalCore.flagValuation (schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY)
        (twistedPotential f E aT HT a H k s) =
      (k : ℝ)⁻¹ • (fun i =>
        (schemeFubiniStudySectionVector f (m + 1) E Y hY (twistAtlas aT a k) 1 s hs i : ℝ)) := by
  let := E.isSeparated
  let := E.quasiCompact
  have hu := (twistMetric f E aT HT a H k).isThetaPshPotential_sectionLogNormSq
    (twistAtlas aT a k) 1 s hs
  have hkR : (0 : ℝ) ≤ (k : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg k)
  have h := TranscendentalCore.flagValuation_smul
    (F := schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY) hu hkR
  rw [schemeFubiniStudySectionVector_eq_flagValuation f m E Y hY (twistAtlas aT a k)
    (twistMetric f E aT HT a H k) 1 s hs]
  exact h

/-- **Twisted containment**: as `eventually_normalized_mem_smul_partialOkounkovBody`, for the
sections of `T ⊗ L^k ⊗ 𝓘(kφ)`; the curvature `k⁻¹ c₁(T, h_T)` of the twist is absorbed by the slack
`ε ω` for `k ≫ 0`. -/
theorem eventually_twisted_mem_smul_partialOkounkovBody {φ ψ : SchemeComplexPoint f → EReal}
    {ε : ℝ} (hε : 0 < ε)
    (hψ : letI := E.isSeparated; letI := E.quasiCompact;
      ψ ∈ globalAnalyticCurrents (H.curvature a +
        ε • (schemeProjectiveTNKahlerBackground f (m + 1) E).form))
    (hle : SingularityLE φ ψ) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : letI := E.isSeparated; letI := E.quasiCompact;
      (-(H.curvature a + (ε / 2) • (schemeProjectiveTNKahlerBackground f (m + 1) E).form) +
        C • (schemeProjectiveTNKahlerBackground f (m + 1) E).form).val.IsSemipositive)
    {q : ℚ} (hq0 : 0 < q) (hq1 : q ≤ 1 / 2) (hqC : 2 * (q : ℝ) * C ≤ ε / 2) :
    letI := E.isSeparated
    letI := E.quasiCompact
    ∃ k₀ : ℕ, 0 < k₀ ∧ ∀ k : ℕ, k₀ ≤ k →
      ∀ (s : bundlePowerGlobalSections (bundleTensor T (bundleTensorPower L k)) 1) (hs : s ≠ 0),
      (k = 0 ∨ IsIdealSection f (m + 1) E (multiplierIdeal (n := m + 1) (k : ℝ) φ) 1 s) →
        (k : ℝ)⁻¹ • (fun i =>
          (schemeFubiniStudySectionVector f (m + 1) E Y hY (twistAtlas aT a k) 1 s hs i : ℝ)) ∈
          (1 - (q : ℝ)) • partialOkounkovBody (schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY)
            (H.curvature a + ε • (schemeProjectiveTNKahlerBackground f (m + 1) E).form) ψ := by
  let := E.isSeparated
  let := E.quasiCompact
  have : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  -- an auxiliary smooth metric on `T`
  let HT : SchemeLineBundleMetric f (m + 1) E T := schemeLineBundleMetric f (m + 1) E aT
  set 𝔽 := schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY with h𝔽
  set ω := schemeProjectiveTNKahlerBackground f (m + 1) E with hω
  set θ := H.curvature a with hθ
  have hq0R : (0 : ℝ) < q := by exact_mod_cast hq0
  have hq1R : (q : ℝ) < 1 := by
    have h := (Rat.cast_le (K := ℝ)).mpr hq1
    push_cast at h
    linarith
  have hψq : ManifoldQuasiPlurisubharmonic (n := m + 1) ψ := hψ.1.1.quasiPlurisubharmonic
  have hψan := (globalAnalyticCurrents_subset_analyticCurrents _ hψ).2
  obtain ⟨k₁, hk₁, hcomp⟩ := exists_singularityLE_scaledLogNormSq f (m + 1) E hψan hq0R hq1R
  obtain ⟨CT, hCT, hCTsemi⟩ :=
    KahlerDomination.exists_pos_isSemipositive_add_smul ω (-(HT.curvature aT))
  refine ⟨max k₁ (⌈4 * CT / ε⌉₊ + 1), lt_of_lt_of_le hk₁ (le_max_left _ _),
    fun k hk s hs hmult => ?_⟩
  have hkpos : 0 < k := lt_of_lt_of_le hk₁ ((le_max_left _ _).trans hk)
  have hkR : (0 : ℝ) < k := by exact_mod_cast hkpos
  have hk2 : 4 * CT / ε ≤ k := by
    calc 4 * CT / ε ≤ ⌈4 * CT / ε⌉₊ := Nat.le_ceil _
      _ ≤ (k : ℝ) := by exact_mod_cast (Nat.le_succ _).trans ((le_max_right _ _).trans hk)
  have hmult' : IsIdealSection f (m + 1) E (multiplierIdeal (n := m + 1) (k : ℝ) φ) 1 s :=
    hmult.resolve_left hkpos.ne'
  have hI := isIdealSection_mono_of_singularityLE f E hψq hle hmult'
  have hSL := hcomp k ((le_max_left _ _).trans hk) (twistAtlas aT a k)
    (twistMetric f E aT HT a H k) 1 s hI
  have hε4 : 0 < ε / 4 := by positivity
  -- the twisted potential is `(θ + (ε/4) ω)`-psh
  have hpsh := isThetaPshPotential_twistedPotential f E aT HT a H hkpos hs
  have hpsh4 : IsThetaPshPotential (θ + (ε / 4) • ω.form).val
      (twistedPotential f E aT HT a H k s) := by
    refine TranscendentalBody.isThetaPshPotential_of_le hpsh ?_
    have hkinv : (k : ℝ)⁻¹ * CT ≤ ε / 4 := by
      rw [inv_mul_le_iff₀ hkR]
      rw [div_le_iff₀ hε] at hk2
      nlinarith
    have heq : θ + (ε / 4) • ω.form - (θ + (k : ℝ)⁻¹ • HT.curvature aT) =
        (k : ℝ)⁻¹ • (-(HT.curvature aT) + CT • ω.form) + (ε / 4 - (k : ℝ)⁻¹ * CT) • ω.form := by
      module
    rw [heq]
    exact UniformPerturbedKahlerLowerBound.isSemipositive_add
      (KahlerDomination.isSemipositive_smul hCTsemi (inv_nonneg.mpr hkR.le))
      (KahlerDomination.isSemipositive_smul ω.isSemipositive (by linarith))
  have hθ2 : θ + (ε / 4) • ω.form + (ε / 4) • ω.form = θ + (ε / 2) • ω.form := by
    rw [add_assoc, ← add_smul]
    congr 2
    ring
  have hK : IsKahlerCurrentPotential (θ + (ε / 2) • ω.form) (twistedPotential f E aT HT a H k s) := by
    have h := PartialBody.isKahlerCurrentPotential_add_smul hpsh4 ω hε4
    rwa [hθ2] at h
  have hA : twistedPotential f E aT HT a H k s ∈ analyticCurrents (θ + (ε / 2) • ω.form) := by
    refine ⟨TranscendentalBody.isThetaPshPotential_of_le hpsh4 ?_,
      hasManifoldAnalyticSingularityType_twistedPotential f E aT HT a H k hs⟩
    have heq : θ + (ε / 2) • ω.form - (θ + (ε / 4) • ω.form) = (ε / 4) • ω.form := by module
    rw [heq]
    exact KahlerDomination.isSemipositive_smul ω.isSemipositive hε4.le
  have hmem := flagValuation_self_mem_partialOkounkovBody_of_analytic (F := 𝔽) hK hA
  have hmem2 := partialOkounkovBody_mono (F := 𝔽) (θ + (ε / 2) • ω.form) hSL hmem
  have hmem3 := PartialBody.inv_smul_mem_partialOkounkovBody_add (F := 𝔽) hC0 hC hq0 hq1 hqC hmem2
  have hθeq : θ + (ε / 2) • ω.form + (ε / 2) • ω.form = θ + ε • ω.form := by
    rw [add_assoc, ← add_smul, add_halves]
  change _ ∈ partialOkounkovBody 𝔽 (θ + (ε / 2) • ω.form + (ε / 2) • ω.form) ψ at hmem3
  rw [hθeq, flagValuation_twistedPotential f E Y hY aT HT a H k s hs] at hmem3
  have hne : (1 - (q : ℝ)) ≠ 0 := by linarith
  refine ⟨_, hmem3, ?_⟩
  change (1 - (q : ℝ)) • ((1 - (q : ℝ))⁻¹ • ((k : ℝ)⁻¹ •
    (fun i => (schemeFubiniStudySectionVector f (m + 1) E Y hY (twistAtlas aT a k) 1 s hs i :
      ℝ)))) = _
  rw [smul_smul, mul_inv_cancel₀ hne, one_smul]

end Twisted

end SGPT.IGood.DXMain
