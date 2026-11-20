import SGPT.Foundations.Analysis.FirstPass.FiniteGeodesicRooftopEndpoint
import SGPT.Foundations.Analysis.Pending.SubgeodesicChartPotential
import SGPT.Foundations.Analysis.Pending.ThetaPshDecreasingLimit

set_option autoImplicit false

/-!
# Perron geodesics along decreasing endpoints

Let `θ` be a smooth real `2`-form on a complex manifold `M` and let `u₀`, `u₁` be `θ`-PSH
potentials whose Perron geodesic `U = finiteGeodesic θ u₀ u₁` is a subgeodesic from `u₀` to `u₁`.
If `θ`-PSH potentials `v₀ᵏ`, `v₁ᵏ` decrease pointwise to `u₀`, `u₁` and every Perron geodesic
`Uᵏ = finiteGeodesic θ v₀ᵏ v₁ᵏ` is an interior subgeodesic, then `Uᵏ_t` decreases pointwise to
`U_t` for every time `t` (`finiteGeodesic_eq_iInf_of_antitone`,
`tendsto_finiteGeodesic_of_antitone`); the infimum of the `Uᵏ` is itself a subgeodesic from `u₀`
to `u₁` (`isSubgeodesicFrom_iInf_finiteGeodesic`).

This is the stability step of Xia's proof of Proposition 4.3.3 (Step 3, `xia-sgpt:page-0173`).
Perron monotonicity gives `U_t ≤ Uᵏ⁺¹_t ≤ Uᵏ_t`. The infimum `h` of the `Uᵏ` is again an interior
subgeodesic: a decreasing limit of strip-psh functions is strip-psh, and one smooth local potential
tests the whole sequence (`SubgeodesicChartPotential.plurisubharmonicOn_subgeodesicChartFunction`);
its slices are nondegenerate because `h ≥ U`. Its endpoint limits are squeezed: `U_t ≤ h_t ≤
(1 - t) u₀ + t u₁` (the chord bound of the `Uᵏ` passes to the limit), and both bounds converge to
`u₀` in chart-local `L¹` as `t → 0+` (`manifoldL1LocallyTendsto_left_of_le_le_eRealChord`), and
to `u₁` as `t → 1-` by time reversal. So `h` is a Perron competitor for `(u₀, u₁)` and `h_t ≤ U_t`.

No model potential, no Kähler form and no compactness is used.
-/

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis.Pending.FiniteGeodesicDecreasingEndpoints

open FirstPass

noncomputable section

/-! ### The extended-real chord -/

/-- The chord read backwards: `(1 - (1 - s)) a + (1 - s) b = (1 - s) b + s a`. -/
theorem eRealChord_one_sub (a b : EReal) (s : ℝ) :
    eRealChord a b (1 - s) = eRealChord b a s := by
  simp only [eRealChord, sub_sub_cancel]
  exact add_comm _ _

/-- The chord is continuous in its two endpoint values at finite-from-above endpoints, for
interior times. -/
theorem tendsto_eRealChord {α : Type*} {l : Filter α} {a b : α → EReal} {a₀ b₀ : EReal}
    (ha : Tendsto a l (𝓝 a₀)) (hb : Tendsto b l (𝓝 b₀)) (ha₀ : a₀ ≠ ⊤) (hb₀ : b₀ ≠ ⊤)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    Tendsto (fun i => eRealChord (a i) (b i) s) l (𝓝 (eRealChord a₀ b₀ s)) := by
  have hA : Tendsto (fun i => ((1 - s : ℝ) : EReal) * a i) l
      (𝓝 (((1 - s : ℝ) : EReal) * a₀)) :=
    EReal.Tendsto.const_mul ha (Or.inl (EReal.coe_ne_bot _)) (Or.inl (EReal.coe_ne_top _))
  have hB : Tendsto (fun i => ((s : ℝ) : EReal) * b i) l (𝓝 (((s : ℝ) : EReal) * b₀)) :=
    EReal.Tendsto.const_mul hb (Or.inl (EReal.coe_ne_bot _)) (Or.inl (EReal.coe_ne_top _))
  have hA₀ : ((1 - s : ℝ) : EReal) * a₀ ≠ ⊤ := eReal_const_mul_ne_top (sub_nonneg.mpr hs.2) ha₀
  have hB₀ : ((s : ℝ) : EReal) * b₀ ≠ ⊤ := eReal_const_mul_ne_top hs.1 hb₀
  exact (EReal.continuousAt_add (Or.inl hA₀) (Or.inr hB₀)).tendsto.comp (hA.prodMk_nhds hB)

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-! ### The endpoint squeeze -/

/-- **Endpoint squeeze.** If `l_t ≤ w_t ≤ (1 - t) u₀ + t u₁` for `0 < t < 1`, the `l_t` are
`θ`-PSH potentials and `l_t → u₀` in chart-local `L¹` as `t → 0+`, then `w_t → u₀` in chart-local
`L¹` as `t → 0+`. -/
theorem manifoldL1LocallyTendsto_left_of_le_le_eRealChord {θ : SmoothRealForm n M 2}
    {u₀ u₁ : M → EReal} {l w : ℝ → M → EReal}
    (hu₀ : IsThetaPshPotential θ u₀) (hu₁ : IsThetaPshPotential θ u₁)
    (hl : ∀ s ∈ Ioo (0 : ℝ) 1, IsThetaPshPotential θ (l s))
    (hlt : ManifoldL1LocallyTendsto (n := n) l (𝓝[>] (0 : ℝ)) u₀)
    (hlw : ∀ s ∈ Ioo (0 : ℝ) 1, l s ≤ w s)
    (hwc : ∀ s ∈ Ioo (0 : ℝ) 1, w s ≤ fun x => eRealChord (u₀ x) (u₁ x) s) :
    ManifoldL1LocallyTendsto (n := n) w (𝓝[>] (0 : ℝ)) u₀ := by
  intro e K hK hKe
  have hIoo : ∀ᶠ s in 𝓝[>] (0 : ℝ), s ∈ Ioo (0 : ℝ) 1 := Ioo_mem_nhdsGT zero_lt_one
  have hbound : Tendsto (fun s => chartL1EDistance (l s) u₀ e K +
      chartL1EDistance (fun x => eRealChord (u₀ x) (u₁ x) s) u₀ e K) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa using (hlt e K hK hKe).add
      (hu₀.manifoldL1LocallyTendsto_eRealChord_left hu₁ e K hK hKe)
  have hsqueeze : ∀ᶠ s in 𝓝[>] (0 : ℝ), chartL1EDistance (w s) u₀ e K ≤
      chartL1EDistance (l s) u₀ e K +
        chartL1EDistance (fun x => eRealChord (u₀ x) (u₁ x) s) u₀ e K := by
    filter_upwards [hIoo] with s hs
    have htop : ∀ x, w s x ≠ ⊤ := fun x hx => by
      have hle := hwc s hs x
      rw [hx] at hle
      exact eRealChord_ne_top (hu₀.quasiPshPotential.1.ne_top x)
        (hu₁.quasiPshPotential.1.ne_top x) hs.1.le hs.2.le (top_unique hle)
    exact chartL1EDistance_le_add_of_le_le_eRealChord s hu₀.quasiPshPotential
      hu₁.quasiPshPotential (hl s hs).quasiPshPotential htop (hlw s hs) (hwc s hs) e hKe
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hbound
    (Eventually.of_forall fun _ => zero_le) hsqueeze

/-- The right-endpoint form of the squeeze, by time reversal. -/
theorem manifoldL1LocallyTendsto_right_of_le_le_eRealChord {θ : SmoothRealForm n M 2}
    {u₀ u₁ : M → EReal} {l w : ℝ → M → EReal}
    (hu₀ : IsThetaPshPotential θ u₀) (hu₁ : IsThetaPshPotential θ u₁)
    (hl : ∀ s ∈ Ioo (0 : ℝ) 1, IsThetaPshPotential θ (l s))
    (hlt : ManifoldL1LocallyTendsto (n := n) l (𝓝[<] (1 : ℝ)) u₁)
    (hlw : ∀ s ∈ Ioo (0 : ℝ) 1, l s ≤ w s)
    (hwc : ∀ s ∈ Ioo (0 : ℝ) 1, w s ≤ fun x => eRealChord (u₀ x) (u₁ x) s) :
    ManifoldL1LocallyTendsto (n := n) w (𝓝[<] (1 : ℝ)) u₁ := by
  have hmem : ∀ s ∈ Ioo (0 : ℝ) 1, 1 - s ∈ Ioo (0 : ℝ) 1 := fun s hs =>
    ⟨sub_pos.mpr hs.2, by linarith [hs.1]⟩
  have hrev := manifoldL1LocallyTendsto_left_of_le_le_eRealChord (n := n) (θ := θ)
    (l := timeReversedCurve l) (w := timeReversedCurve w) hu₁ hu₀
    (fun s hs => hl (1 - s) (hmem s hs))
    (hlt.comp tendsto_one_sub_nhdsGT_zero)
    (fun s hs => hlw (1 - s) (hmem s hs))
    (fun s hs x => by
      show w (1 - s) x ≤ eRealChord (u₁ x) (u₀ x) s
      rw [← eRealChord_one_sub]
      exact hwc (1 - s) (hmem s hs) x)
  refine (hrev.comp tendsto_one_sub_nhdsLT_one).congr fun s => ?_
  funext x
  simp only [timeReversedCurve_apply, sub_sub_cancel]

/-! ### Decreasing limits of interior subgeodesics -/

/-- **A decreasing limit of interior subgeodesics is an interior subgeodesic**, provided its
interior slices are nondegenerate (for instance, if they lie above `θ`-PSH potentials). -/
theorem isSubgeodesicInterior_iInf_of_antitone {θ : SmoothRealForm n M 2}
    {c : ℕ → ℝ → M → EReal} (hc : ∀ k, IsSubgeodesicInterior θ (c k))
    (hanti : ∀ t x, Antitone fun k => c k t x)
    (hnd : ∀ t ∈ Ioo (0 : ℝ) 1, LocallyNondegenerate fun x => ⨅ k, c k t x) :
    IsSubgeodesicInterior θ (fun t x => ⨅ k, c k t x) := by
  refine ⟨fun t ht => ⟨ThetaPshDecreasingLimit.thetaPlurisubharmonic_iInf_of_antitone
    (fun k => ((hc k).thetaPshPotential ht).1) (hanti t), hnd t ht⟩, ?_⟩
  intro e z hz
  obtain ⟨W, ρ, hzW, hρ, -⟩ := (hc 0).complexified_psh e hz
  refine ⟨W, ρ, hzW, hρ, ?_⟩
  have hk : ∀ k, PlurisubharmonicOn (subgeodesicChartFunction (c k) e ρ)
      (geodesicChartDomain W) := fun k =>
    SubgeodesicChartPotential.plurisubharmonicOn_subgeodesicChartFunction (hc k) e hρ
  have hlim := DiscPshOn.plurisubharmonicOn_iInf_of_antitone (isOpen_geodesicChartDomain hρ.1)
    (fun k => (hk k).discPshOn) (fun p _ i j hij => add_le_add (hanti _ _ hij) le_rfl)
  have heq : (fun p => ⨅ k, subgeodesicChartFunction (c k) e ρ p) =
      subgeodesicChartFunction (fun t x => ⨅ k, c k t x) e ρ := by
    funext p
    obtain ⟨y, τ⟩ := p
    simp only [subgeodesicChartFunction_apply]
    rw [ThetaPshDecreasingLimit.iInf_add_coe]
    rfl
  rwa [heq] at hlim

/-! ### Perron geodesics along decreasing endpoints -/

omit [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] in
/-- A pointwise decreasing limit lies below every member. -/
theorem le_of_antitone_of_tendsto {v : ℕ → M → EReal} {u : M → EReal}
    (hanti : ∀ x, Antitone fun k => v k x) (hlim : ∀ x, Tendsto (fun k => v k x) atTop (𝓝 (u x)))
    (k : ℕ) : u ≤ v k := fun x => (hanti x).le_of_tendsto (hlim x) k

/-- **Perron geodesics along decreasing endpoints.** Let `U` be the Perron geodesic of `θ`-PSH
potentials `u₀`, `u₁`, a subgeodesic from `u₀` to `u₁`. If `θ`-PSH potentials `v₀ᵏ`, `v₁ᵏ` decrease
pointwise to `u₀`, `u₁` and every Perron geodesic `Uᵏ` of `(v₀ᵏ, v₁ᵏ)` is an interior subgeodesic,
then the infimum of the `Uᵏ` is a subgeodesic from `u₀` to `u₁`. -/
theorem isSubgeodesicFrom_iInf_finiteGeodesic {θ : SmoothRealForm n M 2}
    {u₀ u₁ : M → EReal} {v₀ v₁ : ℕ → M → EReal}
    (hsub : IsSubgeodesicFrom θ (finiteGeodesic θ u₀ u₁) u₀ u₁)
    (hv₀ : ∀ k, IsThetaPshPotential θ (v₀ k)) (hv₁ : ∀ k, IsThetaPshPotential θ (v₁ k))
    (hanti₀ : ∀ x, Antitone fun k => v₀ k x) (hanti₁ : ∀ x, Antitone fun k => v₁ k x)
    (hlim₀ : ∀ x, Tendsto (fun k => v₀ k x) atTop (𝓝 (u₀ x)))
    (hlim₁ : ∀ x, Tendsto (fun k => v₁ k x) atTop (𝓝 (u₁ x)))
    (hint : ∀ k, IsSubgeodesicInterior θ (finiteGeodesic θ (v₀ k) (v₁ k))) :
    IsSubgeodesicFrom θ (fun t x => ⨅ k, finiteGeodesic θ (v₀ k) (v₁ k) t x) u₀ u₁ := by
  set U := finiteGeodesic θ u₀ u₁ with hU
  set h : ℝ → M → EReal := fun t x => ⨅ k, finiteGeodesic θ (v₀ k) (v₁ k) t x with hh
  have hu₀ := hsub.1
  have hu₁ := hsub.2.1
  -- Perron monotonicity
  have hUle : ∀ t, U t ≤ h t := fun t x => le_iInf fun k =>
    finiteGeodesic_mono (le_of_antitone_of_tendsto hanti₀ hlim₀ k)
      (le_of_antitone_of_tendsto hanti₁ hlim₁ k) t x
  have hGanti : ∀ t x, Antitone fun k => finiteGeodesic θ (v₀ k) (v₁ k) t x :=
    fun t x i j hij => finiteGeodesic_mono (fun y => hanti₀ y hij) (fun y => hanti₁ y hij) t x
  -- the chord bound passes to the limit
  have hchord : ∀ s ∈ Ioo (0 : ℝ) 1, h s ≤ fun x => eRealChord (u₀ x) (u₁ x) s := by
    intro s hs x
    have hlim := tendsto_eRealChord (hlim₀ x) (hlim₁ x) (hu₀.quasiPshPotential.1.ne_top x)
      (hu₁.quasiPshPotential.1.ne_top x) (s := s) ⟨hs.1.le, hs.2.le⟩
    refine ge_of_tendsto' hlim fun k => ?_
    exact (iInf_le _ k).trans (finiteGeodesic_le_eRealChord (hv₀ k) (hv₁ k) hs x)
  have hUpot : ∀ s ∈ Ioo (0 : ℝ) 1, IsThetaPshPotential θ (U s) := fun s hs =>
    hsub.2.2.1.thetaPshPotential hs
  have hinth : IsSubgeodesicInterior θ h :=
    isSubgeodesicInterior_iInf_of_antitone hint hGanti fun t ht =>
      (hUpot t ht).2.mono (hUle t)
  exact ⟨hu₀, hu₁, hinth,
    manifoldL1LocallyTendsto_left_of_le_le_eRealChord hu₀ hu₁ hUpot hsub.tendsto_left
      (fun s _ => hUle s) hchord,
    manifoldL1LocallyTendsto_right_of_le_le_eRealChord hu₀ hu₁ hUpot hsub.tendsto_right
      (fun s _ => hUle s) hchord⟩

/-- **Perron geodesics along decreasing endpoints**, slice form: under the hypotheses of
`isSubgeodesicFrom_iInf_finiteGeodesic`, `U_t = inf_k Uᵏ_t` for every `t`: the infimum is a Perron
competitor for `(u₀, u₁)`, and Perron monotonicity gives the other inequality. -/
theorem finiteGeodesic_eq_iInf_of_antitone {θ : SmoothRealForm n M 2}
    {u₀ u₁ : M → EReal} {v₀ v₁ : ℕ → M → EReal}
    (hsub : IsSubgeodesicFrom θ (finiteGeodesic θ u₀ u₁) u₀ u₁)
    (hv₀ : ∀ k, IsThetaPshPotential θ (v₀ k)) (hv₁ : ∀ k, IsThetaPshPotential θ (v₁ k))
    (hanti₀ : ∀ x, Antitone fun k => v₀ k x) (hanti₁ : ∀ x, Antitone fun k => v₁ k x)
    (hlim₀ : ∀ x, Tendsto (fun k => v₀ k x) atTop (𝓝 (u₀ x)))
    (hlim₁ : ∀ x, Tendsto (fun k => v₁ k x) atTop (𝓝 (u₁ x)))
    (hint : ∀ k, IsSubgeodesicInterior θ (finiteGeodesic θ (v₀ k) (v₁ k))) (t : ℝ) :
    (fun x => ⨅ k, finiteGeodesic θ (v₀ k) (v₁ k) t x) = finiteGeodesic θ u₀ u₁ t := by
  refine le_antisymm ?_ fun x => le_iInf fun k =>
    finiteGeodesic_mono (le_of_antitone_of_tendsto hanti₀ hlim₀ k)
      (le_of_antitone_of_tendsto hanti₁ hlim₁ k) t x
  exact subgeodesic_slice_le_finiteGeodesic
    (isSubgeodesicFrom_iInf_finiteGeodesic hsub hv₀ hv₁ hanti₀ hanti₁ hlim₀ hlim₁ hint) t

/-- **Perron geodesics along decreasing endpoints**, convergence form: `Uᵏ_t(x)` decreases to
`U_t(x)` for every `t` and every `x`. -/
theorem tendsto_finiteGeodesic_of_antitone {θ : SmoothRealForm n M 2}
    {u₀ u₁ : M → EReal} {v₀ v₁ : ℕ → M → EReal}
    (hsub : IsSubgeodesicFrom θ (finiteGeodesic θ u₀ u₁) u₀ u₁)
    (hv₀ : ∀ k, IsThetaPshPotential θ (v₀ k)) (hv₁ : ∀ k, IsThetaPshPotential θ (v₁ k))
    (hanti₀ : ∀ x, Antitone fun k => v₀ k x) (hanti₁ : ∀ x, Antitone fun k => v₁ k x)
    (hlim₀ : ∀ x, Tendsto (fun k => v₀ k x) atTop (𝓝 (u₀ x)))
    (hlim₁ : ∀ x, Tendsto (fun k => v₁ k x) atTop (𝓝 (u₁ x)))
    (hint : ∀ k, IsSubgeodesicInterior θ (finiteGeodesic θ (v₀ k) (v₁ k))) (t : ℝ) (x : M) :
    Tendsto (fun k => finiteGeodesic θ (v₀ k) (v₁ k) t x) atTop
      (𝓝 (finiteGeodesic θ u₀ u₁ t x)) := by
  have heq := congrFun (finiteGeodesic_eq_iInf_of_antitone hsub hv₀ hv₁ hanti₀ hanti₁ hlim₀ hlim₁
    hint t) x
  rw [← heq]
  exact tendsto_atTop_iInf fun i j hij =>
    finiteGeodesic_mono (fun y => hanti₀ y hij) (fun y => hanti₁ y hij) t x

end

end SGPT.Foundations.Analysis.Pending.FiniteGeodesicDecreasingEndpoints
