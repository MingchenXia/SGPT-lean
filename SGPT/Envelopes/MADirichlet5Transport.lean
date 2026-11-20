import SGPT.Envelopes.MADirichlet4Limit
import SGPT.Foundations.Analysis.Pending.ActualLocalBoundedMixedCapacityContinuity
import SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorBiholomorphicTransport
import SGPT.Foundations.Analysis.Pending.FlatCurveRegularizerPotential
import SGPT.Foundations.Analysis.Pending.MixedNonPluripolar

/-!
# Bounded mixed capacity continuity on open subsets of `ℂⁿ`

TN's continuity theorem for bounded mixed Bedford–Taylor measures along sequences converging in
relative capacity
(`ActualLocalBoundedMixedCapacityContinuity.tendsto_integral_of_relative_capacity`, the bounded
case of Xia, *Foundations of pluripotential theory* (FPT),
`cor:mixed-products-energy-capacity-continuity`) is stated on a chart domain of a compact Kähler
manifold carrying a smooth local potential of the Kähler form. We transport it to an arbitrary
open set `D ⊆ ℂⁿ`:

* `D` is replaced by the bounded open set `D₀ = D ∩ B(0, ρ₀) ⊇ K` (locality of the mixed
  measures, TN `canonicalMixedBedfordTaylorMeasure_restrict`);
* an affine map `τ(ξ) = c + sξ` carries a small ball inside the target of a chart of TN's flat
  torus `ℂⁿ/Λ` (whose Kähler form has the potential `π|z|²` in every chart,
  `isSmoothLocalPotential_flat`) onto a neighbourhood of `D₀`;
* mixed measures are transported by TN's `canonicalMixedMeasure_pushforward`, and relative
  capacities do not increase under the pull-back (`relCapacity_preimage_affineTo_le`).

Main result: `tendsto_integral_mixed_of_relCapacity`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Metric MeasureTheory TopologicalSpace
open scoped Topology ENNReal

namespace SGPT.Envelopes.MADirichlet

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.FirstPass.MixedMongeAmpere
open SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.MongeAmpere
open SGPT.Foundations.Analysis.Pending.MixedMongeAmpere
open SGPT.Foundations.Analysis.Pending.BedfordTaylor

variable {n : ℕ}

/-- The open preimage of an open set under `τ(ξ) = c + sξ`. -/
def affinePreimage (c : ComplexModel n) (s : ℝ) (V : Opens (ComplexModel n)) :
    Opens (ComplexModel n) :=
  ⟨affineTo c s ⁻¹' V, V.isOpen.preimage (continuous_affineTo c)⟩

/-- `τ(ξ) = c + sξ` and `σ(z) = s⁻¹(z - c)` are inverse biholomorphisms between `τ⁻¹(V)` and
`V`. -/
theorem isBiholomorphicPair_affinePreimage (c : ComplexModel n) {s : ℝ} (hs : s ≠ 0)
    (V : Opens (ComplexModel n)) :
    IsBiholomorphicPair (affinePreimage c s V) V (affineTo c s) (affineFrom c s) where
  holo := (contDiff_affineTo c).contDiffOn
  holo_inv := (contDiff_affineFrom c).contDiffOn
  mapsTo := fun _ hz => hz
  mapsTo_inv := fun z hz => by
    show affineTo c s (affineFrom c s z) ∈ V
    rwa [affineTo_affineFrom c hs]
  left_inv := fun ξ _ => affineFrom_affineTo c hs ξ
  right_inv := fun z _ => affineTo_affineFrom c hs z

/-- The reverse pair. -/
theorem isBiholomorphicPair_affinePreimage_symm (c : ComplexModel n) {s : ℝ} (hs : s ≠ 0)
    (V : Opens (ComplexModel n)) :
    IsBiholomorphicPair V (affinePreimage c s V) (affineFrom c s) (affineTo c s) :=
  let h := isBiholomorphicPair_affinePreimage c hs V
  { holo := h.holo_inv, holo_inv := h.holo, mapsTo := h.mapsTo_inv, mapsTo_inv := h.mapsTo,
    left_inv := h.right_inv, right_inv := h.left_inv }

/-- `τ` is a measurable embedding. -/
theorem measurableEmbedding_affineTo (c : ComplexModel n) {s : ℝ} (hs : s ≠ 0) :
    MeasurableEmbedding (affineTo c s) :=
  (affineHomeomorph c hs).symm.measurableEmbedding

/-- `σ` is a measurable embedding. -/
theorem measurableEmbedding_affineFrom (c : ComplexModel n) {s : ℝ} (hs : s ≠ 0) :
    MeasurableEmbedding (affineFrom c s) :=
  (affineHomeomorph c hs).measurableEmbedding

/-- Composition with the first map of a biholomorphic pair preserves local boundedness and
plurisubharmonicity. -/
theorem isLocallyBoundedPshOn_comp_of_isBiholomorphicPair {A B : Opens (ComplexModel n)}
    {τ σ : ComplexModel n → ComplexModel n} (h : IsBiholomorphicPair A B τ σ)
    {w : ComplexModel n → ℝ} (hw : IsLocallyBoundedPshOn B w) :
    IsLocallyBoundedPshOn A (fun x => w (τ x)) := by
  refine ⟨HolomorphicPullback.plurisubharmonicOn_comp_holomorphic
    (u := fun z => (w z : EReal)) A.isOpen
    (h.holo.differentiableOn (by simp)) h.mapsTo hw.1, fun z hz => ?_⟩
  obtain ⟨V, hzV, hVB, C, hC⟩ := hw.2 (τ z) (h.mapsTo hz)
  have hopen : IsOpen ((A : Set (ComplexModel n)) ∩ τ ⁻¹' V) :=
    h.holo.continuousOn.isOpen_inter_preimage A.isOpen V.isOpen
  exact ⟨⟨_, hopen⟩, ⟨hz, hzV⟩, fun y hy => hy.1, C, fun y hy => hC _ hy.2⟩

/-- The diagonal Monge–Ampère measure is transported by a biholomorphic pair. -/
theorem canonicalBedfordTaylorMeasure_pushforward {A B : Opens (ComplexModel n)}
    {τ σ : ComplexModel n → ComplexModel n} (h : IsBiholomorphicPair A B τ σ)
    {w : ComplexModel n → ℝ} (hw : IsLocallyBoundedPshOn B w)
    (hwA : IsLocallyBoundedPshOn A (fun x => w (τ x))) :
    ((canonicalBedfordTaylorMeasure A _ hwA).restrict (A : Set (ComplexModel n))).map τ =
      canonicalBedfordTaylorMeasure B w hw := by
  obtain ⟨hwA', -, -, hmap⟩ :=
    LocalBedfordTaylorBiholomorphicTransport.canonicalMixedMeasure_pushforward h
      (u := fun _ => w) (fun _ => hw)
  rw [← canonicalMixedBedfordTaylorMeasure_diagonal A _ hwA,
    ← canonicalMixedBedfordTaylorMeasure_diagonal B w hw]
  exact hmap

/-- **Relative capacities do not increase under affine pull-back**: for `V' = τ⁻¹(V)`,
`Cap_{V'}(E) ≤ Cap_V(τ(E))`. A competitor `w` on `V'` gives the competitor `w ∘ σ` on `V`,
whose Monge–Ampère measure is the push-forward of that of `w` (TN
`canonicalMixedMeasure_pushforward`). -/
theorem relCapacity_preimage_affineTo_le (c : ComplexModel n) {s : ℝ} (hs : s ≠ 0)
    (V : Opens (ComplexModel n)) (E : Set (ComplexModel n)) :
    relCapacity (affinePreimage c s V) E ≤ relCapacity V (affineTo c s '' E) := by
  refine relCapacity_le_of_forall fun w hw hwb => ?_
  set V' := affinePreimage c s V
  have hpair := isBiholomorphicPair_affinePreimage_symm c hs V
  have hwσ : IsLocallyBoundedPshOn V (fun x => w (affineFrom c s x)) :=
    isLocallyBoundedPshOn_comp_of_isBiholomorphicPair hpair hw
  have hmap := canonicalBedfordTaylorMeasure_pushforward hpair hw hwσ
  have hb : ∀ z ∈ V, -1 ≤ w (affineFrom c s z) ∧ w (affineFrom c s z) ≤ 0 :=
    fun z hz => hwb _ (hpair.mapsTo hz)
  have hpre : affineFrom c s ⁻¹' E = affineTo c s '' E := by
    ext z
    constructor
    · intro hz
      exact ⟨affineFrom c s z, hz, affineTo_affineFrom c hs z⟩
    · rintro ⟨ξ, hξ, rfl⟩
      show affineFrom c s (affineTo c s ξ) ∈ E
      rwa [affineFrom_affineTo c hs]
  calc canonicalBedfordTaylorMeasure V' w hw E
      = (((canonicalBedfordTaylorMeasure V _ hwσ).restrict (V : Set (ComplexModel n))).map
          (affineFrom c s)) E := by rw [hmap]
    _ = ((canonicalBedfordTaylorMeasure V _ hwσ).restrict (V : Set (ComplexModel n)))
          (affineFrom c s ⁻¹' E) :=
        (measurableEmbedding_affineFrom c hs).map_apply _ _
    _ ≤ canonicalBedfordTaylorMeasure V _ hwσ (affineFrom c s ⁻¹' E) :=
        Measure.restrict_le_self _
    _ ≤ relCapacity V _ := canonicalBedfordTaylorMeasure_le_relCapacity hwσ hb _
    _ = relCapacity V (affineTo c s '' E) := by rw [hpre]

/-- Integrals against mixed measures are transported by `τ(ξ) = c + sξ`. -/
theorem integral_canonicalMixed_affine (c : ComplexModel n) {s : ℝ} (hs : s ≠ 0)
    (V : Opens (ComplexModel n)) {w : Fin n → ComplexModel n → ℝ}
    (hw : IsLocallyBoundedMixedPshOn V w)
    (hw' : IsLocallyBoundedMixedPshOn (affinePreimage c s V) (fun i ξ => w i (affineTo c s ξ)))
    (h : ComplexModel n → ℝ) :
    ∫ z, h z ∂canonicalMixedBedfordTaylorMeasure V w hw =
      ∫ ξ, h (affineTo c s ξ) ∂canonicalMixedBedfordTaylorMeasure (affinePreimage c s V)
        (fun i ξ => w i (affineTo c s ξ)) hw' := by
  obtain ⟨hA, -, -, hmap⟩ :=
    LocalBedfordTaylorBiholomorphicTransport.canonicalMixedMeasure_pushforward
      (isBiholomorphicPair_affinePreimage c hs V) hw
  rw [← hmap, (measurableEmbedding_affineTo c hs).integral_map,
    Measure.restrict_eq_self_of_ae_mem (ae_iff.mpr
      (canonicalMixedBedfordTaylorMeasure_compl (affinePreimage c s V) _ hA))]

/-- **Bounded mixed capacity continuity on an open subset of `ℂⁿ`** (the bounded case of FPT
`cor:mixed-products-energy-capacity-continuity`; TN's
`ActualLocalBoundedMixedCapacityContinuity.tendsto_integral_of_relative_capacity`, transported
from a chart of the flat torus): let `D ⊆ ℂⁿ` be open, `uⱼ = (uⱼ,₁, …, uⱼ,ₙ)` and
`v = (v₁, …, vₙ)` tuples of plurisubharmonic functions on `D` with `|uⱼ,ᵢ|, |vᵢ| ≤ B`, such that
for every open `V ⊆ D`, compact `T ⊆ V` and `a > 0`,
`Cap_V(T ∩ {|uⱼ,ᵢ - vᵢ| > a}) → 0`. Then `ddᶜuⱼ,₁ ∧ ⋯ ∧ ddᶜuⱼ,ₙ → ddᶜv₁ ∧ ⋯ ∧ ddᶜvₙ`
against continuous compactly supported test functions in `D`. -/
theorem tendsto_integral_mixed_of_relCapacity {D : Opens (ComplexModel n)}
    {K : Set (ComplexModel n)} (hK : IsCompact K) (hKD : K ⊆ D)
    {u : ℕ → Fin n → ComplexModel n → ℝ} {v : Fin n → ComplexModel n → ℝ}
    (hu : ∀ j, IsLocallyBoundedMixedPshOn D (u j))
    (hv : IsLocallyBoundedMixedPshOn D v) {B : ℝ} (hB : 0 ≤ B)
    (huB : ∀ j i z, z ∈ D → -B ≤ u j i z ∧ u j i z ≤ B)
    (hvB : ∀ i z, z ∈ D → -B ≤ v i z ∧ v i z ≤ B)
    (hcap : ∀ i (V : Opens (ComplexModel n)), V ≤ D → ∀ T : Set (ComplexModel n),
      IsCompact T → T ⊆ V → ∀ a : ℝ, 0 < a →
      Tendsto (fun j => relCapacity V {z | z ∈ T ∧ a < |u j i z - v i z|}) atTop (𝓝 0))
    {h : ComplexModel n → ℝ} (hc : Continuous h) (hk : HasCompactSupport h)
    (ht : tsupport h ⊆ K) :
    Tendsto (fun j => ∫ z, h z ∂canonicalMixedBedfordTaylorMeasure D (u j) (hu j))
      atTop (𝓝 (∫ z, h z ∂canonicalMixedBedfordTaylorMeasure D v hv)) := by
  classical
  -- a bounded open neighbourhood `D₀` of `K`
  obtain ⟨ρ₀, hρ₀, hKρ⟩ := hK.isBounded.subset_ball_lt 0 0
  set D₀ : Opens (ComplexModel n) := D ⊓ ⟨ball 0 ρ₀, isOpen_ball⟩ with hD₀def
  have hD₀D : D₀ ≤ D := inf_le_left
  have hKD₀ : K ⊆ D₀ := fun z hz => ⟨hKD hz, hKρ hz⟩
  have hloc : ∀ (w : Fin n → ComplexModel n → ℝ) (hw : IsLocallyBoundedMixedPshOn D w)
      (hw₀ : IsLocallyBoundedMixedPshOn D₀ w),
      ∫ z, h z ∂canonicalMixedBedfordTaylorMeasure D w hw =
        ∫ z, h z ∂canonicalMixedBedfordTaylorMeasure D₀ w hw₀ := by
    intro w hw hw₀
    rw [← MixedNonPluripolar.canonicalMixedBedfordTaylorMeasure_restrict hD₀D hw hw₀,
      setIntegral_eq_integral_of_forall_compl_eq_zero]
    intro z hz
    exact image_eq_zero_of_notMem_tsupport fun h' => hz (hKD₀ (ht h'))
  have hu₀ : ∀ j, IsLocallyBoundedMixedPshOn D₀ (u j) := fun j i =>
    BedfordTaylor.IsLocallyBoundedPshOn.mono_opens (hu j i) hD₀D
  have hv₀ : IsLocallyBoundedMixedPshOn D₀ v := fun i => BedfordTaylor.IsLocallyBoundedPshOn.mono_opens (hv i) hD₀D
  -- a chart of the flat torus and an affine map onto a neighbourhood of `D₀`
  let Mt := FlatComplexTorus.Torus n
  let _ : MeasurableSpace Mt := borel Mt
  have _ : BorelSpace Mt := ⟨rfl⟩
  let e := complexChartAt (n := n) (0 : Mt)
  set z₀ : ComplexModel n := e.val (0 : Mt) with hz₀def
  have hz₀ : z₀ ∈ e.val.target := e.val.map_source (mem_complexChartAt_source (0 : Mt))
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp e.val.open_target z₀ hz₀
  set s : ℝ := 2 * ρ₀ / r with hsdef
  have hs : 0 < s := by positivity
  set c : ComplexModel n := -(s • z₀) with hcdef
  set D' : Opens (ComplexModel n) := affinePreimage c s D₀ with hD'def
  have hD't : (D' : Set (ComplexModel n)) ⊆ e.val.target := by
    intro ξ hξ
    apply hball
    have h1 : affineTo c s ξ ∈ ball (0 : ComplexModel n) ρ₀ := hξ.2
    have h2 : affineTo c s ξ = s • (ξ - z₀) := by
      simp only [affineTo, hcdef, smul_sub]; abel
    rw [h2, mem_ball, dist_zero_right, norm_smul, Real.norm_of_nonneg hs.le] at h1
    rw [mem_ball, dist_eq_norm]
    have h3 : s * ‖ξ - z₀‖ < s * (r / 2) := by
      calc s * ‖ξ - z₀‖ < ρ₀ := h1
        _ = s * (r / 2) := by rw [hsdef]; field_simp
    have := lt_of_mul_lt_mul_left h3 hs.le
    linarith
  have hρ : IsSmoothLocalPotential (FlatComplexTorus.flatKahlerBackground n).form.val e D'
      (fun z => Real.pi * ‖z‖ ^ 2) :=
    (FlatCurveRegularizerPotential.isSmoothLocalPotential_flat e).mono D'.isOpen hD't
  have hpair := isBiholomorphicPair_affinePreimage c hs.ne' D₀
  set u' : ℕ → Fin n → ComplexModel n → ℝ := fun j i ξ => u j i (affineTo c s ξ) with hu'def
  set v' : Fin n → ComplexModel n → ℝ := fun i ξ => v i (affineTo c s ξ) with hv'def
  have hu' : ∀ j, IsLocallyBoundedMixedPshOn D' (u' j) := fun j i =>
    isLocallyBoundedPshOn_comp_of_isBiholomorphicPair hpair (hu₀ j i)
  have hv' : IsLocallyBoundedMixedPshOn D' v' := fun i =>
    isLocallyBoundedPshOn_comp_of_isBiholomorphicPair hpair (hv₀ i)
  -- the transported compact set and test function
  set K' : Set (ComplexModel n) := affineFrom c s '' K with hK'def
  have hK' : IsCompact K' := hK.image (continuous_affineFrom c)
  have hK'D' : K' ⊆ D' := by
    rintro _ ⟨x, hx, rfl⟩
    show affineTo c s (affineFrom c s x) ∈ D₀
    rw [affineTo_affineFrom c hs.ne']
    exact hKD₀ hx
  set h' : ComplexModel n → ℝ := fun ξ => h (affineTo c s ξ) with hh'def
  have hc' : Continuous h' := hc.comp (continuous_affineTo c)
  have hk' : HasCompactSupport h' := hk.comp_homeomorph (affineHomeomorph c hs.ne').symm
  have ht' : tsupport h' ⊆ K' := by
    refine closure_minimal (fun ξ hξ => ?_) (hK'.isClosed)
    refine ⟨affineTo c s ξ, ht (subset_tsupport _ hξ), affineFrom_affineTo c hs.ne' ξ⟩
  -- bounds
  have huB' : ∀ j i ξ, ξ ∈ D' → -B ≤ u' j i ξ ∧ u' j i ξ ≤ B := fun j i ξ hξ =>
    huB j i _ (hD₀D hξ)
  have hvB' : ∀ i ξ, ξ ∈ D' → -B ≤ v' i ξ ∧ v' i ξ ≤ B := fun i ξ hξ => hvB i _ (hD₀D hξ)
  -- capacities
  have hcap' : ∀ i (V' : Opens (ComplexModel n)), V' ≤ D' → ∀ T' : Set (ComplexModel n),
      IsCompact T' → T' ⊆ V' → ∀ a : ℝ, 0 < a →
      Tendsto (fun j => relCapacity V' {ξ | ξ ∈ T' ∧ a < |u' j i ξ - v' i ξ|})
        atTop (𝓝 0) := by
    intro i V' hV'D' T' hT' hT'V' a ha
    set V : Opens (ComplexModel n) :=
      ⟨affineFrom c s ⁻¹' V', V'.isOpen.preimage (continuous_affineFrom c)⟩ with hVdef
    have hVV' : affinePreimage c s V = V' := by
      ext ξ
      show affineFrom c s (affineTo c s ξ) ∈ V' ↔ ξ ∈ V'
      rw [affineFrom_affineTo c hs.ne']
    have hVD : V ≤ D := by
      intro z hz
      have h1 : affineTo c s (affineFrom c s z) ∈ D₀ := hV'D' hz
      rw [affineTo_affineFrom c hs.ne'] at h1
      exact hD₀D h1
    have hT : IsCompact (affineTo c s '' T') := hT'.image (continuous_affineTo c)
    have hTV : affineTo c s '' T' ⊆ V := by
      rintro _ ⟨ξ, hξ, rfl⟩
      show affineFrom c s (affineTo c s ξ) ∈ V'
      rw [affineFrom_affineTo c hs.ne']
      exact hT'V' hξ
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (hcap i V hVD _ hT hTV a ha) (fun _ => zero_le) (fun j => ?_)
    rw [← hVV']
    refine (relCapacity_preimage_affineTo_le c hs.ne' V _).trans (relCapacity_mono ?_)
    rintro _ ⟨ξ, ⟨hξT, hξa⟩, rfl⟩
    exact ⟨⟨ξ, hξT, rfl⟩, hξa⟩
  have hl := ActualLocalBoundedMixedCapacityContinuity.tendsto_integral_of_relative_capacity
    (FlatComplexTorus.flatKahlerBackground n) e hD't hρ hK' hK'D' hu' hv' hB huB' hvB' hcap'
    hc' hk' ht'
  have hIu : ∀ j, ∫ z, h z ∂canonicalMixedBedfordTaylorMeasure D (u j) (hu j) =
      ∫ ξ, h' ξ ∂canonicalMixedBedfordTaylorMeasure D' (u' j) (hu' j) := fun j => by
    rw [hloc _ (hu j) (hu₀ j)]
    exact integral_canonicalMixed_affine c hs.ne' D₀ (hu₀ j) (hu' j) h
  have hIv : ∫ z, h z ∂canonicalMixedBedfordTaylorMeasure D v hv =
      ∫ ξ, h' ξ ∂canonicalMixedBedfordTaylorMeasure D' v' hv' := by
    rw [hloc _ hv hv₀]
    exact integral_canonicalMixed_affine c hs.ne' D₀ hv₀ hv' h
  simp_rw [hIu, hIv]
  exact hl

end SGPT.Envelopes.MADirichlet
