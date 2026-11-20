import SGPT.Foundations.Analysis.Pending.FiniteGeodesicEnergyAffine
import SGPT.Foundations.Analysis.Pending.FiniteGeodesicDecreasingEndpoints
import SGPT.Foundations.Analysis.Pending.FiniteEnergyCharacterization

set_option autoImplicit false

/-!
# The Monge--Ampère energy is affine along finite-energy geodesics (bounded model potential)

Let `(X, ω)` be a connected compact Kähler manifold, `θ` a smooth closed real `(1,1)`-form, `φ` a
bounded model potential and `E = E_θ^φ` the extended Monge--Ampère energy (Xia (3.30),
`RelativeEnergy.relativeMongeAmpereEnergy`), with values in `[-∞, 0]`.

* `relativeMongeAmpereEnergy_finiteGeodesic` — **if `u₀, u₁ ∈ PSH(X, θ; φ)` and their Perron
  geodesic `(u_t)` is a subgeodesic from `u₀` to `u₁`, then `E(u_t) = (1 - t) E(u₀) + t E(u₁)`
  for `0 < t < 1`**, in `[-∞, 0]`.
* `relativeMongeAmpereEnergy_finiteGeodesic_of_relativeFullMass` — this applies to endpoints in
  the full-mass class `E(X, θ; φ)`.
* `relativeMongeAmpereEnergy_finiteGeodesic_of_relativeFiniteEnergy` and `_toReal` — for endpoints
  in `E^1(X, θ; φ)` all three energies are finite and the identity holds in `ℝ` (Xia, SGPT,
  Proposition 4.3.3, for a bounded model potential).
* `relativeMongeAmpereEnergy_closedSubgeodesicSlice_of_relativeFiniteEnergy` — the same on the
  closed interval `[0, 1]`, the slices at `0` and `1` being the endpoints.

Proof (Xia's Step 3, `xia-sgpt:page-0173`): the truncations `uᵢᵏ = max(uᵢ, φ - k)` are bounded and
lie in `E^∞(X, θ; φ)`, so their Perron geodesics `uᵏ_t` are subgeodesics and
`E(uᵏ_t) = (1 - t) E(u₀ᵏ) + t E(u₁ᵏ)` (`FiniteGeodesicEnergyAffine`). The truncations decrease to the
endpoints, so `uᵏ_t` decreases to `u_t` (`FiniteGeodesicDecreasingEndpoints`), and the energy is
continuous along decreasing sequences (`MongeAmpereEnergyDecreasing`), at the slices and at the
endpoints.
-/

open Set Filter MeasureTheory
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.FiniteGeodesicEnergyAffineE1

open FirstPass FirstPass.PositiveClasses BoundedGlobalProduct RelativeEnergy BoundedMongeAmpereEnergy
  MongeAmpereEnergyDecreasing FiniteEnergyCharacterization FiniteGeodesicDecreasingEndpoints
  FiniteGeodesicEnergyEndpoints

noncomputable section

/-- The chord of a value with itself is that value, at interior times. -/
theorem eRealChord_self (a : EReal) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) : eRealChord a a t = a := by
  have h1 : (0 : ℝ) < 1 - t := sub_pos.mpr ht.2
  induction a with
  | bot =>
    simp only [eRealChord, EReal.coe_mul_bot_of_pos h1, EReal.coe_mul_bot_of_pos ht.1,
      EReal.add_bot]
  | top =>
    simp only [eRealChord, EReal.coe_mul_top_of_pos h1, EReal.coe_mul_top_of_pos ht.1,
      EReal.top_add_top]
  | coe r =>
    simp only [eRealChord]
    norm_cast
    ring_nf

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- The interior slices of a Perron geodesic between two relative potentials which is an interior
subgeodesic are relative potentials. -/
theorem relativePSH_finiteGeodesic {θ : ClosedRealOneOneForm n M} {φ u₀ u₁ : M → EReal}
    (hint : IsSubgeodesicInterior θ.val (finiteGeodesic θ.val u₀ u₁))
    (hu₀ : RelativePSH θ φ u₀) (hu₁ : RelativePSH θ φ u₁) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    RelativePSH θ φ (finiteGeodesic θ.val u₀ u₁ t) :=
  ⟨hint.thetaPshPotential ht, fun x =>
    (finiteGeodesic_le_eRealChord hu₀.1 hu₁.1 ht x).trans <|
      (eRealChord_mono (hu₀.2 x) (hu₁.2 x) ht.1.le ht.2.le).trans (eRealChord_self _ ht).le⟩

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

omit [BorelSpace M] in
/-- The extended energy only depends on the potential. -/
theorem relativeMongeAmpereEnergy_congr {θ : ClosedRealOneOneForm n M} {φ u v : M → EReal}
    {hφ : IsModelPotential θ φ} (huv : u = v) (hu : RelativePSH θ φ u) (hv : RelativePSH θ φ v) :
    relativeMongeAmpereEnergy θ φ u hφ hu = relativeMongeAmpereEnergy θ φ v hφ hv := by
  subst huv
  rfl

omit [BorelSpace M] in
/-- A truncation `max(u, φ - k)` of a relative potential, for a bounded model potential `φ`, lies
in `E^∞(X, θ; φ)`. -/
theorem relativeEInfinity_truncation (θ : ClosedRealOneOneForm n M) {φ u : M → EReal}
    (hφ : IsModelPotential θ φ) (hφb : IsBoundedPotential φ) (hu : RelativePSH θ φ u) (k : ℕ) :
    RelativeEInfinity θ φ (truncation φ u k) :=
  ⟨isThetaPshPotential_truncation hφ.plurisubharmonic.1 hu.1.1 hφb hu.2 k,
    sameSingularityType_of_bounded (truncation_bounded hφb hu.2 k) hφb⟩

/-- **The energy is affine along Perron geodesics between relative potentials** (bounded model
potential). If `u₀, u₁ ∈ PSH(X, θ; φ)` and their Perron geodesic `(u_t)` is a subgeodesic from
`u₀` to `u₁`, then `E(u_t) = (1 - t) E(u₀) + t E(u₁)` for `0 < t < 1`, in `[-∞, 0]`. -/
theorem relativeMongeAmpereEnergy_finiteGeodesic [ConnectedSpace M]
    (omega : KahlerBackground n M) (θ : ClosedRealOneOneForm n M) {φ u₀ u₁ : M → EReal}
    (hφ : IsModelPotential θ φ) (hφb : IsBoundedPotential φ)
    (hu₀ : RelativePSH θ φ u₀) (hu₁ : RelativePSH θ φ u₁)
    (hsub : IsSubgeodesicFrom θ.val (finiteGeodesic θ.val u₀ u₁) u₀ u₁)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) (hUt : RelativePSH θ φ (finiteGeodesic θ.val u₀ u₁ t)) :
    relativeMongeAmpereEnergy θ φ _ hφ hUt =
      ((1 - t : ℝ) : EReal) * relativeMongeAmpereEnergy θ φ u₀ hφ hu₀ +
        ((t : ℝ) : EReal) * relativeMongeAmpereEnergy θ φ u₁ hφ hu₁ := by
  set v₀ : ℕ → M → EReal := truncation φ u₀ with hv₀
  set v₁ : ℕ → M → EReal := truncation φ u₁ with hv₁
  have hE₀ : ∀ k, RelativeEInfinity θ φ (v₀ k) := relativeEInfinity_truncation θ hφ hφb hu₀
  have hE₁ : ∀ k, RelativeEInfinity θ φ (v₁ k) := relativeEInfinity_truncation θ hφ hφb hu₁
  have hR₀ : ∀ k, RelativePSH θ φ (v₀ k) := fun k => ⟨(hE₀ k).1, truncation_le hu₀.2 k⟩
  have hR₁ : ∀ k, RelativePSH θ φ (v₁ k) := fun k => ⟨(hE₁ k).1, truncation_le hu₁.2 k⟩
  have hb₀ : ∀ k, IsBoundedPotential (v₀ k) := truncation_bounded hφb hu₀.2
  have hb₁ : ∀ k, IsBoundedPotential (v₁ k) := truncation_bounded hφb hu₁.2
  have hsubk : ∀ k, IsSubgeodesicFrom θ.val (finiteGeodesic θ.val (v₀ k) (v₁ k)) (v₀ k) (v₁ k) :=
    fun k => FiniteGeodesicsFullMassAnyDim.finiteGeodesic_isSubgeodesicFrom_of_relativeEInfinity
      omega θ φ _ _ hφ (hE₀ k) (hE₁ k)
  have hGrel : ∀ k, RelativePSH θ φ (finiteGeodesic θ.val (v₀ k) (v₁ k) t) := fun k =>
    relativePSH_finiteGeodesic (hsubk k).2.2.1 (hR₀ k) (hR₁ k) ht
  -- the slices decrease to the slice of the limit
  have hconv : ∀ x, Tendsto (fun k => finiteGeodesic θ.val (v₀ k) (v₁ k) t x) atTop
      (𝓝 (finiteGeodesic θ.val u₀ u₁ t x)) := fun x =>
    tendsto_finiteGeodesic_of_antitone hsub (fun k => (hE₀ k).1) (fun k => (hE₁ k).1)
      (truncation_antitone φ u₀) (truncation_antitone φ u₁) (tendsto_truncation hφb)
      (tendsto_truncation hφb) (fun k => (hsubk k).2.2.1) t x
  have hanti : ∀ x, Antitone fun k => finiteGeodesic θ.val (v₀ k) (v₁ k) t x :=
    fun x i j hij => finiteGeodesic_mono (fun y => truncation_antitone φ u₀ y hij)
      (fun y => truncation_antitone φ u₁ y hij) t x
  -- energies of the slices
  have hL := relativeMongeAmpereEnergy_tendsto_of_antitone omega θ hφ hφb hUt hGrel hanti hconv
  -- the bounded case at each level
  have hk : ∀ k, relativeMongeAmpereEnergy θ φ _ hφ (hGrel k) =
      eRealChord (relativeEnergyOfMinimalType θ φ (v₀ k) hφ.plurisubharmonic (hE₀ k).1 : EReal)
        (relativeEnergyOfMinimalType θ φ (v₁ k) hφ.plurisubharmonic (hE₁ k).1 : EReal) t := by
    intro k
    obtain ⟨A, B, hAB⟩ := finiteGeodesic_uniformly_bounded (hsubk k) (hb₀ k) (hb₁ k)
    rw [relativeMongeAmpereEnergy_eq_of_bounded omega θ hφ (hGrel k) hφb
      ⟨A, B, hAB t ht⟩,
      FiniteGeodesicEnergyAffine.relativeEnergyOfMinimalType_finiteGeodesic omega θ
        hφ.plurisubharmonic hφb (hsubk k) (hb₀ k) (hb₁ k) ht (hGrel k).1]
    simp only [eRealChord, EReal.coe_add, EReal.coe_mul]
  -- the endpoint energies
  have hT₀ := tendsto_relativeEnergyOfMinimalType_truncation omega θ hφ hu₀ hφb
  have hT₁ := tendsto_relativeEnergyOfMinimalType_truncation omega θ hφ hu₁ hφb
  have hne₀ : relativeMongeAmpereEnergy θ φ u₀ hφ hu₀ ≠ ⊤ :=
    ne_top_of_le_ne_top EReal.zero_ne_top (relativeMongeAmpereEnergy_le_zero θ hφ hu₀)
  have hne₁ : relativeMongeAmpereEnergy θ φ u₁ hφ hu₁ ≠ ⊤ :=
    ne_top_of_le_ne_top EReal.zero_ne_top (relativeMongeAmpereEnergy_le_zero θ hφ hu₁)
  have hR := tendsto_eRealChord hT₀ hT₁ hne₀ hne₁ (s := t) ⟨ht.1.le, ht.2.le⟩
  refine tendsto_nhds_unique hL ?_
  refine hR.congr fun k => ?_
  rw [hk k]

/-- **The energy is affine along full-mass geodesics** (bounded model potential): for endpoints in
`E(X, θ; φ)`, `E(u_t) = (1 - t) E(u₀) + t E(u₁)` for `0 < t < 1`, in `[-∞, 0]`. -/
theorem relativeMongeAmpereEnergy_finiteGeodesic_of_relativeFullMass [ConnectedSpace M]
    (omega : KahlerBackground n M) (θ : ClosedRealOneOneForm n M) {φ u₀ u₁ : M → EReal}
    (hφ : IsModelPotential θ φ) (hφb : IsBoundedPotential φ)
    (hu₀ : RelativeFullMass θ φ u₀ hφ) (hu₁ : RelativeFullMass θ φ u₁ hφ)
    (hr₀ : RelativePSH θ φ u₀) (hr₁ : RelativePSH θ φ u₁)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) (hUt : RelativePSH θ φ (finiteGeodesic θ.val u₀ u₁ t)) :
    relativeMongeAmpereEnergy θ φ _ hφ hUt =
      ((1 - t : ℝ) : EReal) * relativeMongeAmpereEnergy θ φ u₀ hφ hr₀ +
        ((t : ℝ) : EReal) * relativeMongeAmpereEnergy θ φ u₁ hφ hr₁ :=
  relativeMongeAmpereEnergy_finiteGeodesic omega θ hφ hφb hr₀ hr₁
    (FiniteGeodesicsFullMassAnyDim.finiteGeodesic_isSubgeodesicFrom_of_relativeFullMass omega θ φ
      u₀ u₁ hφ hu₀ hu₁) ht hUt

/-- **The energy is affine along finite-energy geodesics** (Xia, SGPT, Proposition 4.3.3, for a
bounded model potential): for endpoints in `E^1(X, θ; φ)`,
`E(u_t) = (1 - t) E(u₀) + t E(u₁)` for `0 < t < 1`. -/
theorem relativeMongeAmpereEnergy_finiteGeodesic_of_relativeFiniteEnergy [ConnectedSpace M]
    (omega : KahlerBackground n M) (θ : ClosedRealOneOneForm n M) {φ u₀ u₁ : M → EReal}
    (hφ : IsModelPotential θ φ) (hφb : IsBoundedPotential φ)
    (hu₀ : RelativeFiniteEnergy θ φ u₀ hφ) (hu₁ : RelativeFiniteEnergy θ φ u₁ hφ)
    (hr₀ : RelativePSH θ φ u₀) (hr₁ : RelativePSH θ φ u₁)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) (hUt : RelativePSH θ φ (finiteGeodesic θ.val u₀ u₁ t)) :
    relativeMongeAmpereEnergy θ φ _ hφ hUt =
      ((1 - t : ℝ) : EReal) * relativeMongeAmpereEnergy θ φ u₀ hφ hr₀ +
        ((t : ℝ) : EReal) * relativeMongeAmpereEnergy θ φ u₁ hφ hr₁ :=
  relativeMongeAmpereEnergy_finiteGeodesic_of_relativeFullMass omega θ hφ hφb hu₀.1 hu₁.1 hr₀ hr₁
    ht hUt

/-- **The energy is affine along finite-energy geodesics**, real form: for endpoints in
`E^1(X, θ; φ)` (bounded model potential) the energies are finite and
`E(u_t) = (1 - t) E(u₀) + t E(u₁)` in `ℝ`. -/
theorem relativeMongeAmpereEnergy_finiteGeodesic_toReal [ConnectedSpace M]
    (omega : KahlerBackground n M) (θ : ClosedRealOneOneForm n M) {φ u₀ u₁ : M → EReal}
    (hφ : IsModelPotential θ φ) (hφb : IsBoundedPotential φ)
    (hu₀ : RelativeFiniteEnergy θ φ u₀ hφ) (hu₁ : RelativeFiniteEnergy θ φ u₁ hφ)
    (hr₀ : RelativePSH θ φ u₀) (hr₁ : RelativePSH θ φ u₁)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) (hUt : RelativePSH θ φ (finiteGeodesic θ.val u₀ u₁ t)) :
    ⊥ < relativeMongeAmpereEnergy θ φ _ hφ hUt ∧
      (relativeMongeAmpereEnergy θ φ _ hφ hUt).toReal =
        (1 - t) * (relativeMongeAmpereEnergy θ φ u₀ hφ hr₀).toReal +
          t * (relativeMongeAmpereEnergy θ φ u₁ hφ hr₁).toReal := by
  have h := relativeMongeAmpereEnergy_finiteGeodesic_of_relativeFiniteEnergy omega θ hφ hφb hu₀ hu₁
    hr₀ hr₁ ht hUt
  have hb₀ := (relativeFiniteEnergy_iff_bot_lt_energy omega θ hφ hφb hr₀).1 hu₀
  have hb₁ := (relativeFiniteEnergy_iff_bot_lt_energy omega θ hφ hφb hr₁).1 hu₁
  have ht₀ : relativeMongeAmpereEnergy θ φ u₀ hφ hr₀ ≠ ⊤ :=
    ne_top_of_le_ne_top EReal.zero_ne_top (relativeMongeAmpereEnergy_le_zero θ hφ hr₀)
  have ht₁ : relativeMongeAmpereEnergy θ φ u₁ hφ hr₁ ≠ ⊤ :=
    ne_top_of_le_ne_top EReal.zero_ne_top (relativeMongeAmpereEnergy_le_zero θ hφ hr₁)
  set e₀ := (relativeMongeAmpereEnergy θ φ u₀ hφ hr₀).toReal
  set e₁ := (relativeMongeAmpereEnergy θ φ u₁ hφ hr₁).toReal
  have he₀ : relativeMongeAmpereEnergy θ φ u₀ hφ hr₀ = (e₀ : EReal) :=
    (EReal.coe_toReal ht₀ hb₀.ne').symm
  have he₁ : relativeMongeAmpereEnergy θ φ u₁ hφ hr₁ = (e₁ : EReal) :=
    (EReal.coe_toReal ht₁ hb₁.ne').symm
  rw [he₀, he₁] at h
  have h' : relativeMongeAmpereEnergy θ φ _ hφ hUt = (((1 - t) * e₀ + t * e₁ : ℝ) : EReal) := by
    rw [h]
    norm_cast
  rw [h']
  exact ⟨EReal.bot_lt_coe _, EReal.toReal_coe _⟩

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] in
/-- The relative potentials `closedSubgeodesicSlice (finiteGeodesic θ u₀ u₁) u₀ u₁ t`, `t ∈ [0, 1]`:
the endpoints at `0` and `1`, the Perron slices in between. -/
theorem relativePSH_closedSubgeodesicSlice {θ : ClosedRealOneOneForm n M} {φ u₀ u₁ : M → EReal}
    (hint : IsSubgeodesicInterior θ.val (finiteGeodesic θ.val u₀ u₁))
    (hu₀ : RelativePSH θ φ u₀) (hu₁ : RelativePSH θ φ u₁) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    RelativePSH θ φ (closedSubgeodesicSlice (finiteGeodesic θ.val u₀ u₁) u₀ u₁ t) := by
  unfold closedSubgeodesicSlice
  split_ifs with h0 h1
  · exact hu₀
  · exact hu₁
  · exact relativePSH_finiteGeodesic hint hu₀ hu₁
      ⟨lt_of_le_of_ne ht.1 (Ne.symm h0), lt_of_le_of_ne ht.2 h1⟩

/-- **The energy is affine on the closed interval** (bounded model potential): for endpoints in
`E^1(X, θ; φ)` and the geodesic `(u_t)_{t ∈ [0, 1]}` with `u_0`, `u_1` the endpoints and the Perron
slices in between, `E(u_t) = (1 - t) E(u₀) + t E(u₁)` for every `t ∈ [0, 1]`. -/
theorem relativeMongeAmpereEnergy_closedSubgeodesicSlice_of_relativeFiniteEnergy
    [ConnectedSpace M] (omega : KahlerBackground n M) (θ : ClosedRealOneOneForm n M)
    {φ u₀ u₁ : M → EReal} (hφ : IsModelPotential θ φ) (hφb : IsBoundedPotential φ)
    (hu₀ : RelativeFiniteEnergy θ φ u₀ hφ) (hu₁ : RelativeFiniteEnergy θ φ u₁ hφ)
    (hr₀ : RelativePSH θ φ u₀) (hr₁ : RelativePSH θ φ u₁) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (hUt : RelativePSH θ φ (closedSubgeodesicSlice (finiteGeodesic θ.val u₀ u₁) u₀ u₁ t)) :
    relativeMongeAmpereEnergy θ φ _ hφ hUt =
      ((1 - t : ℝ) : EReal) * relativeMongeAmpereEnergy θ φ u₀ hφ hr₀ +
        ((t : ℝ) : EReal) * relativeMongeAmpereEnergy θ φ u₁ hφ hr₁ := by
  by_cases h0 : t = 0
  · subst h0
    rw [relativeMongeAmpereEnergy_congr (closedSubgeodesicSlice_zero _ _ _) hUt hr₀]
    simp only [sub_zero, EReal.coe_one, one_mul, EReal.coe_zero, zero_mul, add_zero]
  by_cases h1 : t = 1
  · subst h1
    rw [relativeMongeAmpereEnergy_congr (closedSubgeodesicSlice_one _ _ _) hUt hr₁]
    simp only [sub_self, EReal.coe_one, one_mul, EReal.coe_zero, zero_mul, zero_add]
  have hIoo : t ∈ Ioo (0 : ℝ) 1 := ⟨lt_of_le_of_ne ht.1 (Ne.symm h0), lt_of_le_of_ne ht.2 h1⟩
  have hsl : closedSubgeodesicSlice (finiteGeodesic θ.val u₀ u₁) u₀ u₁ t =
      finiteGeodesic θ.val u₀ u₁ t := by
    simp only [closedSubgeodesicSlice, h0, h1, if_false]
  have hUt' : RelativePSH θ φ (finiteGeodesic θ.val u₀ u₁ t) := hsl ▸ hUt
  rw [relativeMongeAmpereEnergy_congr hsl hUt hUt']
  exact relativeMongeAmpereEnergy_finiteGeodesic_of_relativeFiniteEnergy omega θ hφ hφb hu₀ hu₁
    hr₀ hr₁ hIoo hUt'

end

end SGPT.Foundations.Analysis.Pending.FiniteGeodesicEnergyAffineE1
