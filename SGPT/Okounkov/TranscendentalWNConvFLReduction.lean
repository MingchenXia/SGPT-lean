import SGPT.Okounkov.TranscendentalWNConvFLStatement

/-!
# The fibre limit from smallness and local convergence

Blueprint `claude-tok-wn-fl`, node `tok-wn-fl:reduction` (the final limit of the proof of the hard
inequality of WN21 Theorem 1.7, §7); refines `tok-wn-conv7:fibre-limit`.

`fibreLimit_of_fibreVolumeSmall_of_local` proves
`FibreVolumeSmallStatement F → StrictFibreConvergenceStatement F →
  ExceptionalFibreConvergenceStatement F → FibreLimitStatement F`.

## Proof

Choose a subsequence `k_l` with `e^{k_l/2}|τ_{k_l}| ≤ 2^{-l}` (summable).  Fix `δ > 0`.  The pole set
`K = X₀ ∩ {Ψ = -∞}` has pluripolar traces on `X'` and `ℰ` (`Ψ ∘ ι` and `Ψ|_ℰ` are genuine
potentials, as in `TranscendentalWNConv7Core`), so `FibreVolumeSmallStatement` gives an open
`U ⊇ (X' ∩ ℰ) ∪ K` on which the fibre volumes `∫_{X_τ ∩ U} (Θ|_{X_τ})ⁿ` are `≤ δ` for small `τ`; on
the contact set `D'_k ∩ X_{τ_k}` the obstacle is the constant `g_k(τ_k)`, so
`⟨((Θ + dd^c v_k)|_{X_{τ_k}})ⁿ⟩ ≤ (Θ|_{X_{τ_k}})ⁿ` there (`tok-wn:contact-upper`,
`diagonalPotentialMeasure_restrict_contact_le`) and the contact mass in `U` is `≤ δ` eventually.
Every point of the compact set `X₀ \ U` lies in `X' \ ℰ` or `ℰ \ X'` and is not a pole of `Ψ`,
so the local statements give neighbourhoods `W_p`; a finite subcover, a closed neighbourhood
`S` of `X₀ \ U` inside it and a partition of unity `ρ_i` on `S` subordinate to it give, for large
`l` (`X_{τ_k}` lies near `X₀` for large `k`),
`ν_{k_l}(D'_{k_l}) ≤ δ + Σ_i ∫ ρ_i ∘ s_{k_l} dν_{k_l}`, while
`Σ_i limsup_l ∫ ρ_i ∘ s_{k_l} dν_{k_l} ≤ Σ_i (∫ ρ_i ∘ ι dλ' + ∫_ℰ ρ_i dλ_ℰ) ≤ λ'(X) + λ_ℰ(ℰ)`
(`Σ ρ_i ≤ 1`).  The abstract part is `liminf_le_of_local_testBound`.
-/

set_option autoImplicit false

noncomputable section

universe u

namespace SGPT.Okounkov.TranscendentalWN

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Manifold ContDiff ENNReal NNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.DiagonalMass
open SGPT.Foundations.Analysis.Pending.ProductTestForms
open SGPT.Foundations.Analysis.Pending.ManifoldTubePositivity
open SGPT.Okounkov.TranscendentalMain
open SGPT.Okounkov.TranscendentalCore

/-! ### The abstract limit argument -/

section Abstract

variable {Y V : Type*} [TopologicalSpace Y] [TopologicalSpace V] [MeasurableSpace V]
  [OpensMeasurableSpace V]

/-- A point `p` is *test-bounded* for the measures `ν_{φ l}` transported by `s_{φ l}` and the
functional `L`: some open `W ∋ p` has `limsup_l ∫ ρ ∘ s_{φ l} dν_{φ l} ≤ L ρ` for every continuous
`ρ ≥ 0` supported in `W`. -/
def IsTestBoundedAt (ν : ℕ → Measure V) (s : ℕ → V → Y) (φ : ℕ → ℕ) (L : (Y → ℝ) → ℝ≥0∞)
    (p : Y) : Prop :=
  ∃ W : Set Y, IsOpen W ∧ p ∈ W ∧ ∀ ρ : Y → ℝ, Continuous ρ → (∀ z, 0 ≤ ρ z) → tsupport ρ ⊆ W →
    limsup (fun l => ∫⁻ x, ENNReal.ofReal (ρ (s (φ l) x)) ∂(ν (φ l))) atTop ≤ L ρ

/-- **The final limit of WN21 §7, abstractly.**  Let `ν_k` be measures on `V`, `s_k : V → Y`
continuous into a compact Hausdorff space, `A_k ⊆ V`, `C ⊆ Y` closed such that `s_k(V)` lies in any
given neighbourhood of `C` for large `k`, `φ` strictly increasing and `L` a functional with
`Σ_i L(ρ_i) ≤ B` for finite families of continuous `ρ_i ≥ 0` with `Σ ρ_i ≤ 1`.  If for every
`δ > 0` there is an open `U` with `ν_k(A_k ∩ s_k⁻¹ U) ≤ δ` eventually and every point of `C \ U`
test-bounded, then `liminf_k ν_k(A_k) ≤ B`. -/
theorem liminf_le_of_local_testBound [CompactSpace Y] [T2Space Y] (ν : ℕ → Measure V)
    (s : ℕ → V → Y) (hs : ∀ k, Continuous (s k)) (A : ℕ → Set V) {C : Set Y} (hC : IsClosed C)
    {φ : ℕ → ℕ} (hφ : StrictMono φ) (L : (Y → ℝ) → ℝ≥0∞) (B : ℝ≥0∞)
    (hL : ∀ (t : Finset Y) (ρ : t → Y → ℝ), (∀ i, Continuous (ρ i)) → (∀ i z, 0 ≤ ρ i z) →
      (∀ z, ∑ i, ρ i z ≤ 1) → ∑ i, L (ρ i) ≤ B)
    (hconc : ∀ N : Set Y, IsOpen N → C ⊆ N → ∀ᶠ k in atTop, ∀ x, s k x ∈ N)
    (hsmall : ∀ δ : ℝ≥0∞, 0 < δ → ∃ U : Set Y, IsOpen U ∧
      (∀ p ∈ C, p ∉ U → IsTestBoundedAt ν s φ L p) ∧
      ∀ᶠ k in atTop, ν k (A k ∩ s k ⁻¹' U) ≤ δ) :
    liminf (fun k => ν k (A k)) atTop ≤ B := by
  classical
  refine ENNReal.le_of_forall_pos_le_add fun ε hε hB => ?_
  have hε2 : (0 : ℝ≥0∞) < ((ε / 2 : ℝ≥0) : ℝ≥0∞) := by
    exact_mod_cast half_pos hε
  obtain ⟨U, hUo, hgood, hUsmall⟩ := hsmall _ hε2
  -- the compact set `C \ U` and the neighbourhoods of its points
  have hKc : IsCompact (C ∩ Uᶜ) := (hC.inter hUo.isClosed_compl).isCompact
  have hgood' : ∀ p ∈ C ∩ Uᶜ, IsTestBoundedAt ν s φ L p := fun p hp => hgood p hp.1 hp.2
  choose! W hWo hpW hWbd using hgood'
  obtain ⟨t, htK, hcov⟩ := hKc.elim_nhds_subcover W fun p hp => (hWo p hp).mem_nhds (hpW p hp)
  set O : Set Y := U ∪ ⋃ p ∈ t, W p with hO
  have hOo : IsOpen O := hUo.union (isOpen_biUnion fun p hp => hWo p (htK p hp))
  have hCO : C ⊆ O := fun p hp => by
    by_cases hpU : p ∈ U
    · exact Or.inl hpU
    · exact Or.inr (hcov ⟨hp, hpU⟩)
  obtain ⟨N, hNo, hCN, hNO⟩ := normal_exists_closure_subset hC hOo hCO
  set S : Set Y := closure N ∩ Uᶜ with hS
  have hSc : IsClosed S := isClosed_closure.inter hUo.isClosed_compl
  have hScov : S ⊆ ⋃ i : t, W i := fun z hz => by
    have hzO := hNO hz.1
    rcases hzO with hzU | hzW
    · exact absurd hzU hz.2
    · obtain ⟨p, hp, hzp⟩ := mem_iUnion₂.mp hzW
      exact mem_iUnion.mpr ⟨⟨p, hp⟩, hzp⟩
  obtain ⟨f, hf⟩ := PartitionOfUnity.exists_isSubordinate hSc (fun i : t => W i)
    (fun i => hWo i (htK i i.2)) hScov
  -- the partition of unity
  set ρ : t → Y → ℝ := fun i => f i with hρ
  have hρc : ∀ i, Continuous (ρ i) := fun i => (f i).continuous
  have hρ0 : ∀ i z, 0 ≤ ρ i z := fun i z => f.nonneg i z
  have hρsum : ∀ z, ∑ i, ρ i z = ∑ᶠ i, f i z := fun z => (finsum_eq_sum_of_fintype _).symm
  have hρle : ∀ z, ∑ i, ρ i z ≤ 1 := fun z => (hρsum z).trans_le (f.sum_le_one z)
  have hρone : ∀ z ∈ S, ∑ i, ρ i z = 1 := fun z hz => (hρsum z).trans (f.sum_eq_one hz)
  have hLB : ∑ i, L (ρ i) ≤ B := hL t ρ hρc hρ0 hρle
  have hLfin : ∀ i, L (ρ i) < ⊤ := fun i =>
    lt_of_le_of_lt ((Finset.single_le_sum (fun j _ => zero_le) (Finset.mem_univ i)).trans hLB) hB
  -- the limsup bounds along the subsequence
  set b : t → ℕ → ℝ≥0∞ := fun i k => ∫⁻ x, ENNReal.ofReal (ρ i (s k x)) ∂(ν k) with hb
  have hlimsup : ∀ i, limsup (fun l => b i (φ l)) atTop ≤ L (ρ i) := fun i =>
    hWbd i (htK i i.2) (ρ i) (hρc i) (hρ0 i) (hf i)
  set η : ℝ≥0 := ε / (2 * ((Fintype.card t : ℝ≥0) + 1)) with hη
  have hηpos : 0 < η := by
    rw [hη]
    exact div_pos hε (by positivity)
  have hev_b : ∀ᶠ l in atTop, ∀ i, b i (φ l) < L (ρ i) + η := by
    rw [eventually_all]
    intro i
    refine eventually_lt_of_limsup_lt ((hlimsup i).trans_lt ?_)
    exact ENNReal.lt_add_right (hLfin i).ne (by exact_mod_cast hηpos.ne')
  have hev_k : ∀ᶠ k in atTop, ν k (A k ∩ s k ⁻¹' U) ≤ ((ε / 2 : ℝ≥0) : ℝ≥0∞) ∧
      ∀ x, s k x ∈ N := hUsmall.and (hconc N hNo hCN)
  have hev_l := (hφ.tendsto_atTop.eventually hev_k).and hev_b
  -- the bound along the subsequence
  have hkey : ∀ᶠ l in atTop, ν (φ l) (A (φ l)) ≤ B + ε := by
    filter_upwards [hev_l] with l hl
    obtain ⟨⟨hsm, hN⟩, hbl⟩ := hl
    set k := φ l with hk
    have hmeas : Measurable fun x => ∑ i, ENNReal.ofReal (ρ i (s k x)) :=
      (continuous_finsetSum _ fun i _ =>
        ENNReal.continuous_ofReal.comp ((hρc i).comp (hs k))).measurable
    have hsplit : ν k (A k) ≤ ν k (A k ∩ s k ⁻¹' U) + ν k (A k \ s k ⁻¹' U) := by
      calc ν k (A k) ≤ ν k ((A k ∩ s k ⁻¹' U) ∪ (A k \ s k ⁻¹' U)) :=
            measure_mono fun x hx => by
              by_cases hxU : s k x ∈ U
              · exact Or.inl ⟨hx, hxU⟩
              · exact Or.inr ⟨hx, hxU⟩
        _ ≤ _ := measure_union_le _ _
    have hout : ν k (A k \ s k ⁻¹' U) ≤ ∑ i, b i k := by
      have hsub : A k \ s k ⁻¹' U ⊆ {x | 1 ≤ ∑ i, ENNReal.ofReal (ρ i (s k x))} := by
        intro x hx
        have hxS : s k x ∈ S := ⟨subset_closure (hN x), hx.2⟩
        simp only [mem_ofPred_eq]
        rw [← ENNReal.ofReal_sum_of_nonneg fun i _ => hρ0 i _, hρone _ hxS, ENNReal.ofReal_one]
      calc ν k (A k \ s k ⁻¹' U) ≤ ν k {x | 1 ≤ ∑ i, ENNReal.ofReal (ρ i (s k x))} :=
            measure_mono hsub
        _ = 1 * ν k {x | 1 ≤ ∑ i, ENNReal.ofReal (ρ i (s k x))} := (one_mul _).symm
        _ ≤ ∫⁻ x, ∑ i, ENNReal.ofReal (ρ i (s k x)) ∂(ν k) :=
            mul_meas_ge_le_lintegral₀ hmeas.aemeasurable 1
        _ = ∑ i, b i k := lintegral_finsetSum _ fun i _ =>
            (ENNReal.continuous_ofReal.comp ((hρc i).comp (hs k))).measurable
    have hsum : ∑ i, b i k ≤ ∑ i, (L (ρ i) + η) :=
      Finset.sum_le_sum fun i _ => (hbl i).le
    have hsum' : ∑ i, (L (ρ i) + (η : ℝ≥0∞)) ≤ B + ((ε / 2 : ℝ≥0) : ℝ≥0∞) := by
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      refine add_le_add hLB ?_
      have h1 : ((Fintype.card t : ℝ≥0) * η) ≤ ε / 2 := by
        rw [hη, mul_div_assoc']
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]
        have : (0 : ℝ≥0) ≤ ε := zero_le
        calc (Fintype.card t : ℝ≥0) * ε * 2 ≤ ((Fintype.card t : ℝ≥0) + 1) * ε * 2 := by
              gcongr; exact le_self_add
          _ = ε * (2 * ((Fintype.card t : ℝ≥0) + 1)) := by ring
      have h2 : ((Fintype.card t : ℝ≥0∞) * (η : ℝ≥0∞)) =
          (((Fintype.card t : ℝ≥0) * η : ℝ≥0) : ℝ≥0∞) := by push_cast; rfl
      rw [h2]
      exact_mod_cast h1
    calc ν k (A k) ≤ ((ε / 2 : ℝ≥0) : ℝ≥0∞) + ∑ i, b i k :=
          hsplit.trans (add_le_add hsm hout)
      _ ≤ ((ε / 2 : ℝ≥0) : ℝ≥0∞) + (B + ((ε / 2 : ℝ≥0) : ℝ≥0∞)) :=
          add_le_add le_rfl (hsum.trans hsum')
      _ = B + ε := by
          rw [add_comm, add_assoc, ← ENNReal.coe_add, add_halves]
  exact liminf_le_of_frequently_le' (hφ.tendsto_atTop.frequently hkey.frequently)

end Abstract

/-! ### Auxiliary facts -/

/-- `τ ↦ [τ : 1]` is continuous. -/
theorem continuous_affineLinePoint' : Continuous affineLinePoint :=
  SGPT.Toric.projectiveLineHomeomorph.continuous.comp OnePoint.continuous_coe

/-- A potential less singular than one which is genuine on `ι(V)` is genuine on `ι(V)` (as in
`TranscendentalWNConv7Core`). -/
theorem isThetaPshPotential_comp_of_singularityLE_two {N k : ℕ} {X : Type*} [TopologicalSpace X]
    [ChartedSpace (ComplexModel N) X] [IsComplexManifold N X] {V : Type*} [TopologicalSpace V]
    [ChartedSpace (ComplexModel k) V] [IsComplexManifold k V] {ι : V → X}
    (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel N) ∞ ι)
    {Θ₀ Θ : ClosedRealOneOneForm N X} {φ ψ : X → EReal} (hψ : IsThetaPshPotential Θ.val ψ)
    (hφι : IsThetaPshPotential (ClosedRealOneOneForm.pullback hι Θ₀).val (fun y => φ (ι y)))
    (hle : SGPT.PSH.SingularityLE φ ψ) :
    IsThetaPshPotential (ClosedRealOneOneForm.pullback hι Θ).val (fun y => ψ (ι y)) := by
  obtain ⟨C, hC⟩ := (SGPT.PSH.singularityLE_iff_exists_real _ _).mp hle
  refine ⟨GlobalPotentialPullback.thetaPlurisubharmonic_comp hι hψ.1, fun x U hU hx => ?_⟩
  obtain ⟨y, hyU, hy⟩ := hφι.2 x U hU hx
  refine ⟨y, hyU, fun hbot => hy ?_⟩
  have h := hC (ι y)
  have hbot' : ψ (ι y) = ⊥ := hbot
  rw [hbot', EReal.bot_add] at h
  exact le_bot_iff.mp h

/-- From `e^{k/2}|τ_k| → 0`: a subsequence with `Σ_l e^{k_l/2}|τ_{k_l}| < ∞`. -/
theorem exists_strictMono_summable {e : ℕ → ℝ} (he0 : ∀ k, 0 ≤ e k)
    (he : Tendsto e atTop (𝓝 0)) : ∃ φ : ℕ → ℕ, StrictMono φ ∧ Summable (fun l => e (φ l)) := by
  obtain ⟨φ, hφ, hφle⟩ := Filter.extraction_forall_of_eventually
    (P := fun n k => e k ≤ (1 / 2 : ℝ) ^ n) fun n =>
      he.eventually (Iic_mem_nhds (pow_pos (by norm_num) n))
  exact ⟨φ, hφ, Summable.of_nonneg_of_le (fun l => he0 _) hφle
    (summable_geometric_of_lt_one (by norm_num) (by norm_num))⟩

/-- `Σ_i ∫ ρ_i ∘ j dλ ≤ λ(V)` when `Σ_i ρ_i ≤ 1`. -/
theorem sum_restrictedTestMass_le {k N : ℕ} {V : Type*} [TopologicalSpace V]
    [ChartedSpace (ComplexModel k) V] [IsComplexManifold k V] [CompactSpace V] {𝒳 : Type*}
    [TopologicalSpace 𝒳] [ChartedSpace (ComplexModel N) 𝒳] [IsComplexManifold N 𝒳]
    {j : V → 𝒳} (hj : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel N) ∞ j)
    (Θ : ClosedRealOneOneForm N 𝒳) (w : V → EReal)
    (hw : IsThetaPshPotential (ClosedRealOneOneForm.pullback hj Θ).val w) {ι : Type*}
    (t : Finset ι) (ρ : ι → 𝒳 → ℝ) (hρc : ∀ i, Continuous (ρ i)) (hρ0 : ∀ i z, 0 ≤ ρ i z)
    (hρle : ∀ z, ∑ i ∈ t, ρ i z ≤ 1) :
    ∑ i ∈ t, restrictedTestMass hj Θ w hw (ρ i) ≤
      (letI : MeasurableSpace V := borel V
       haveI : BorelSpace V := ⟨rfl⟩
       diagonalPotentialMass (ClosedRealOneOneForm.pullback hj Θ) w hw) := by
  let : MeasurableSpace V := borel V
  have : BorelSpace V := ⟨rfl⟩
  unfold restrictedTestMass diagonalPotentialMass
  rw [← lintegral_finsetSum t (f := fun i y => ENNReal.ofReal (ρ i (j y))) fun i _ =>
    (ENNReal.continuous_ofReal.comp ((hρc i).comp hj.continuous)).measurable, ← lintegral_one]
  refine lintegral_mono fun y => ?_
  rw [← ENNReal.ofReal_sum_of_nonneg fun i _ => hρ0 i _, ← ENNReal.ofReal_one]
  exact ENNReal.ofReal_le_ofReal (hρle _)

variable {m : ℕ} (F : OriginalFlagGeometry.{u} (m + 1))

/-- The fibres `X_{τ_k}` approach `X₀`: if `τ_k → 0`, then for every open `N ⊇ X₀`, eventually
every section `s_k` over `τ_k` maps into `N`. -/
theorem eventually_mem_of_centralFibre_subset {𝒳 : Type u} [TopologicalSpace 𝒳]
    [CompactSpace 𝒳] {μ : 𝒳 → F.carrier × ProjectiveLine} (hμc : Continuous μ) {τ : ℕ → ℂ}
    (hτ : Tendsto τ atTop (𝓝 0)) (s : ℕ → F.carrier → 𝒳)
    (hμs : ∀ k x, μ (s k x) = (x, affineLinePoint (τ k))) {N : Set 𝒳} (hN : IsOpen N)
    (hCN : centralFibre F μ ⊆ N) : ∀ᶠ k in atTop, ∀ x, s k x ∈ N := by
  have hq : Continuous fun z => (μ z).2 := continuous_snd.comp hμc
  have hK : IsCompact ((fun z => (μ z).2) '' Nᶜ) := (hN.isClosed_compl.isCompact).image hq
  have h0 : projectiveZero ∉ (fun z => (μ z).2) '' Nᶜ := by
    rintro ⟨z, hz, hz0⟩
    exact hz (hCN (by simp [centralFibre, centralBase, hz0]))
  have hlim : Tendsto (fun k => affineLinePoint (τ k)) atTop (𝓝 projectiveZero) := by
    have := (continuous_affineLinePoint'.tendsto 0).comp hτ
    rwa [affineLinePoint_zero] at this
  filter_upwards [hlim.eventually (hK.isClosed.isOpen_compl.mem_nhds h0)] with k hk x
  by_contra hx
  exact hk ⟨s k x, hx, show (μ (s k x)).2 = _ by rw [hμs]⟩

/-! ### The reduction -/

/-- **`tok-wn-fl:reduction`**: `FibreLimitStatement F` (WN21 §7, the final limit of the proof of
the hard inequality of Theorem 1.7) from the smallness estimate (eqeq) and the two local
convergence statements (WN21 Proposition 7.4 near `X' \ ℰ` and near `ℰ \ X'`). -/
theorem fibreLimit_of_fibreVolumeSmall_of_local (h1 : FibreVolumeSmallStatement F)
    (h2 : StrictFibreConvergenceStatement F) (h3 : ExceptionalFibreConvergenceStatement F) :
    FibreLimitStatement F := by
  intro E hE hE0 𝒳 _ _ _ μ hμ Eℰ hEℰ θ b c hc hcb hξ hξc ι hι hμι η' ε hε Ψ hΨ hVΨ 𝒵 _ _ _ π hπ
    D' h hh h𝒵c h𝒵conn hExc hΨπ hK χ hχ τ hτ0 hτlim s hs hμs hw hX' hℰ
  set θ₀ := deformationForm F hμ.contMDiff θ b c Eℰ with hθ₀
  set Θ := θ₀ + ε • η'.form with hΘ
  have := compactSpace_normalCone F hμ
  have := connectedSpace_normalCone F hμ
  -- `β` is big and its Kähler locus meets `X'` and `ℰ`
  obtain ⟨hbig, -, hX'K, hEK⟩ := betaBig F E hE 𝒳 μ hμ Eℰ hEℰ.isDivisorMetric θ b c hc
    (by linarith) hξ hξc.1
  have hbigC : IsBigClass (RealBottChern.ofRepresentative θ₀) :=
    (SGPT.PSH.BookCurrent.isBig_iff_isBigClass _).mp hbig
  have hVle : ∀ φ : 𝒳 → EReal, IsThetaPshPotential θ₀.val φ →
      SGPT.PSH.SingularityLE φ (thetaPshSupremum θ₀.val) := fun φ hφ => by
    obtain ⟨Mφ, hMφ⟩ := hφ.exists_global_upper_bound
    have hle0 : (fun z => φ z + ((-Mφ : ℝ) : EReal)) ≤ 0 := fun z => by
      have h := add_le_add (hMφ z) (le_refl ((-Mφ : ℝ) : EReal))
      rwa [← EReal.coe_add, add_neg_cancel, EReal.coe_zero] at h
    have hV' := le_thetaPshSupremum (hφ.add_const (-Mφ)) hle0
    refine (SGPT.PSH.singularityLE_iff_exists_real _ _).mpr ⟨Mφ, fun z => ?_⟩
    have h1 := add_le_add (hV' z) (le_refl ((Mφ : ℝ) : EReal))
    rwa [add_assoc, ← EReal.coe_add, neg_add_cancel, EReal.coe_zero, add_zero] at h1
  -- `Ψ` is genuine on `X'`
  have hZX' : ∃ y : F.carrier, ι y ∉ nonKahlerLocus (RealBottChern.ofRepresentative θ₀) := by
    obtain ⟨z, hz, hzK⟩ := hX'K
    rw [← (range_centralLift F hμ hι hμι).1] at hz
    obtain ⟨y, rfl⟩ := hz
    exact ⟨y, hzK⟩
  obtain ⟨φX, hφX, hφXι⟩ := exists_gentle_nondegenerate hι θ₀ hbigC hZX'
  have hΨι : IsThetaPshPotential (ClosedRealOneOneForm.pullback hι Θ).val (fun y => Ψ (ι y)) :=
    isThetaPshPotential_comp_of_singularityLE_two hι hΨ hφXι
      (SGPT.PSH.singularityLE_trans (hVle φX hφX.1.1) hVΨ)
  -- `Ψ` is genuine on `ℰ`
  have hΨE : letI := exceptionalChartedSpace F hμ
      haveI := isComplexManifold_exceptional F hμ
      IsThetaPshPotential (ClosedRealOneOneForm.pullback (contMDiff_exceptionalInclusion F hμ)
        Θ).val (fun y : exceptionalSet F μ => Ψ y) := by
    let := exceptionalChartedSpace F hμ
    have := isComplexManifold_exceptional F hμ
    have := connectedSpace_exceptional F hμ
    have hZE : ∃ y : exceptionalSet F μ,
        (y : 𝒳) ∉ nonKahlerLocus (RealBottChern.ofRepresentative θ₀) := by
      obtain ⟨z, hz, hzK⟩ := hEK
      exact ⟨⟨z, hz⟩, hzK⟩
    obtain ⟨φE, hφE, hφEι⟩ :=
      exists_gentle_nondegenerate (contMDiff_exceptionalInclusion F hμ) θ₀ hbigC hZE
    exact isThetaPshPotential_comp_of_singularityLE_two (contMDiff_exceptionalInclusion F hμ) hΨ
      hφEι (SGPT.PSH.singularityLE_trans (hVle φE hφE.1.1) hVΨ)
  -- the pole set of `Ψ` on `X₀` has pluripolar traces
  set K : Set 𝒳 := centralFibre F μ ∩ {z | Ψ z = ⊥} with hKdef
  have hKX : ManifoldLocallyPluripolar (n := m + 1) (ι ⁻¹' K) :=
    (quasiPsh_poles_manifoldLocallyPluripolar ⟨hΨι.1.quasiPlurisubharmonic, hΨι.2⟩).mono
      fun y hy => hy.2
  have hKE : letI := exceptionalChartedSpace F hμ
      haveI := isComplexManifold_exceptional F hμ
      ManifoldLocallyPluripolar (n := m + 1) ((Subtype.val : exceptionalSet F μ → 𝒳) ⁻¹' K) := by
    let := exceptionalChartedSpace F hμ
    have := isComplexManifold_exceptional F hμ
    exact (quasiPsh_poles_manifoldLocallyPluripolar
      ⟨hΨE.1.quasiPlurisubharmonic, hΨE.2⟩).mono fun y hy => hy.2
  -- the sequence `τ_k → 0` and the subsequence
  have hτ : Tendsto τ atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero (fun k => norm_nonneg _) (fun k => ?_) hτlim
    have h1 : (1 : ℝ) ≤ Real.exp ((k : ℝ) / 2) := Real.one_le_exp (by positivity)
    nlinarith [norm_nonneg (τ k)]
  obtain ⟨φ, hφ, hφsum⟩ := exists_strictMono_summable
    (fun k => mul_nonneg (Real.exp_pos _).le (norm_nonneg (τ k))) hτlim
  -- the abstract argument
  let : MeasurableSpace F.carrier := borel F.carrier
  have : BorelSpace F.carrier := ⟨rfl⟩
  set ν : ℕ → Measure F.carrier := fun k =>
    diagonalPotentialMeasure (ClosedRealOneOneForm.pullback (hs k) Θ)
      (fun x => prescribedEnvelope Θ (cutoffObstacle μ χ k) Ψ (s k x)) (hw k) with hν
  set A : ℕ → Set F.carrier := fun k =>
    s k ⁻¹' prescribedContactSet Θ (cutoffObstacle μ χ k) Ψ with hA
  set L : (𝒳 → ℝ) → ℝ≥0∞ := centralLimitTestMass F hμ Θ χ Ψ ι hι hX' hℰ with hLdef
  show liminf (fun k => ν k (A k)) atTop ≤ _
  refine liminf_le_of_local_testBound ν s (fun k => (hs k).continuous) A
    (isClosed_centralFibre F hμ) hφ L _ ?_
    (fun N hN hCN => eventually_mem_of_centralFibre_subset F hμ.continuous hτ s hμs hN hCN) ?_
  · -- the functional is bounded by the total masses
    intro t ρ hρc hρ0 hρle
    simp only [hLdef, centralLimitTestMass]
    rw [Finset.sum_add_distrib]
    refine add_le_add ?_ ?_
    · exact sum_restrictedTestMass_le hι Θ _ hX' Finset.univ ρ hρc hρ0 hρle
    · let := exceptionalChartedSpace F hμ
      have := isComplexManifold_exceptional F hμ
      have := compactSpace_exceptional F hμ
      exact sum_restrictedTestMass_le (contMDiff_exceptionalInclusion F hμ) Θ _ hℰ Finset.univ ρ
        hρc hρ0 hρle
  · -- smallness near `(X' ∩ ℰ) ∪ K` and local convergence elsewhere
    intro δ hδ
    obtain ⟨U, hUo, hXE, hKU, r, hr, hU⟩ :=
      h1 𝒳 μ hμ Θ ι hι hμι K (fun z hz => hz.1) hKX hKE δ hδ
    refine ⟨U, hUo, fun p hpC hpU => ?_, ?_⟩
    · have hΨp : Ψ p ≠ ⊥ := fun hb => hpU (hKU ⟨hpC, hb⟩)
      rw [centralFibre_eq_union F hμ] at hpC
      rcases hpC with hpX | hpE
      · have hpE : p ∉ exceptionalSet F μ := fun hpE => hpU (hXE ⟨hpX, hpE⟩)
        obtain ⟨W, hWo, hpW, hWb⟩ := h2 E hE hE0 𝒳 μ hμ Eℰ hEℰ θ b c hc hcb hξ hξc ι hι hμι η' ε
          hε Ψ hΨ hVΨ 𝒵 π hπ D' h hh h𝒵c h𝒵conn hExc hΨπ hK χ hχ τ hτ0 hτlim s hs hμs hw hX' hℰ
          p hpX hpE hΨp
        exact ⟨W, hWo, hpW, fun ρ hρc hρ0 hρW => hWb ρ hρc hρ0 hρW φ hφ hφsum⟩
      · have hpX : p ∉ strictCentralFibre F μ := fun hpX => hpU (hXE ⟨hpX, hpE⟩)
        obtain ⟨W, hWo, hpW, hWb⟩ := h3 E hE hE0 𝒳 μ hμ Eℰ hEℰ θ b c hc hcb hξ hξc ι hι hμι η' ε
          hε Ψ hΨ hVΨ 𝒵 π hπ D' h hh h𝒵c h𝒵conn hExc hΨπ hK χ hχ τ hτ0 hτlim s hs hμs hw hX' hℰ
          p hpE hpX hΨp
        exact ⟨W, hWo, hpW, fun ρ hρc hρ0 hρW => hWb ρ hρc hρ0 hρW φ hφ hφsum⟩
    · filter_upwards [(tendsto_zero_iff_norm_tendsto_zero.mp hτ).eventually (gt_mem_nhds hr)]
        with k hk
      have hg : Continuous (cutoffObstacle μ χ k) :=
        (continuous_cutoffObstacleLine hχ k).comp (continuous_snd.comp hμ.continuous)
      set cst : ℝ := cutoffObstacleLine χ k (affineLinePoint (τ k)) with hcst
      have hgs : ∀ x, cutoffObstacle μ χ k (s k x) = cst := fun x => by
        simp only [cutoffObstacle, hμs, hcst]
      have hle : ∀ x, prescribedEnvelope Θ (cutoffObstacle μ χ k) Ψ (s k x) ≤
          (((fun _ : F.carrier => cst) x : ℝ) : EReal) := fun x => by
        have := prescribedEnvelope_le (Θ := Θ) (ψ := Ψ) hg (s k x)
        rwa [hgs] at this
      have hcu := diagonalPotentialMeasure_restrict_contact_le F.omega
        (ClosedRealOneOneForm.pullback (hs k) Θ) (hw k) (chartSmooth_const cst) hle
      rw [ddcClosedForm_const, add_zero] at hcu
      have hAeq : A k = {x | prescribedEnvelope Θ (cutoffObstacle μ χ k) Ψ (s k x) =
          (((fun _ : F.carrier => cst) x : ℝ) : EReal)} := by
        ext x
        simp only [hA, prescribedContactSet, mem_preimage, mem_ofPred_eq, hgs]
      have hTm : MeasurableSet (s k ⁻¹' U) := (hUo.preimage (hs k).continuous).measurableSet
      calc ν k (A k ∩ s k ⁻¹' U) = (ν k).restrict (A k) (s k ⁻¹' U) := by
            rw [Measure.restrict_apply hTm, inter_comm]
        _ ≤ (topFormMeasure F.omega (formPow (ClosedRealOneOneForm.pullback (hs k) Θ).val
              (m + 1))).restrict (A k) (s k ⁻¹' U) := by
            rw [hAeq]
            exact Measure.le_iff'.mp hcu _
        _ ≤ topFormMeasure F.omega (formPow (ClosedRealOneOneForm.pullback (hs k) Θ).val
              (m + 1)) (s k ⁻¹' U) := Measure.restrict_apply_le _ _
        _ ≤ δ := hU (τ k) (hτ0 k) hk (s k) (hs k) (hμs k)

end SGPT.Okounkov.TranscendentalWN
