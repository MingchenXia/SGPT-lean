import SGPT.GAGA.ChowBlMap

/-!
# Local analysis of a blow-up along its exceptional divisor


Let `π : Y → M` be the blow-up along `C`, flattened near `x ∈ C` by `Φ ∘ e` onto `ℂᵏ × 0`
(`flatCoord Φ i`, `i ≥ k`, are local equations of `C`).

* `monomialLift_eq_of_monomial_eq` (after `SGPT.Foundations.Analysis`'s
  `exists_monomialLocalInverse`, here for an arbitrary holomorphic candidate inverse): if
  `σⱼ ∘ W = Φ ∘ e ∘ π` on an open set `O`, then the lift `ℓⱼ` of the `j`-th monomial chart
  satisfies `ℓⱼ ∘ W = id` on `O` (uniqueness in the universal property).
* `eventually_eq_zero_of_mul_eq_zero`: a continuous `a` with `h a = 0` near `p`, `h` a local
  generator of an invertible ideal, vanishes near `p`.
* `sum_coeff_mul_eq_delta`: if `g_κ = ∑_l b_{κ l} t_l` and `t_l = ∑_κ c_{l κ} g_κ` near `x`
  (`t_l` the normal flattening coordinates), then `c(x) b(x) = 1`: the differentials of
  generators of `𝓘_C` span the conormal space (proof: restrict to the normal lines
  `t = s e_{l'}`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Set Filter Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open SGPT.Foundations.Analysis.Pending.BlowupFlatCoordinates
open SGPT.Foundations.Analysis.Pending.BlowupMonomialCharts
open scoped Manifold ContDiff

noncomputable section

namespace SGPT.GAGA.ChowBl

universe u

variable {n : ℕ} {M Y : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M] [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
  [IsComplexManifold n Y] {C : Set M} {π : Y → M} {x₀ : M}
  {Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x₀ x₀)} {k : ℕ}

/-- **The lift of a monomial chart inverts every local solution of `σⱼ ∘ W = Φ ∘ e ∘ π`.** -/
theorem monomialLift_eq_of_monomial_eq (hπ : IsBlowupAlong n C π) {j : Fin n}
    {ℓ : LiftedOpen.{u} (monomialDomain Φ k j) → Y}
    (hℓs : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ ℓ)
    (hℓπ : π ∘ ℓ = monomialChart Φ k j) {Wm : Y → ComplexModel n} {O : Set Y} (hO : IsOpen O)
    (hWs : ∀ z ∈ O, ContMDiffAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ Wm z)
    (hkey : ∀ z ∈ O, π z ∈ flatDomain Φ ∧
      monomial k j (Wm z) = Φ.toFun (chartAt (ComplexModel n) x₀ (π z))) :
    ∀ z ∈ O, ∀ hw : Wm z ∈ monomialDomain Φ k j, ℓ (LiftedOpen.mk _ (Wm z) hw) = z := by
  intro z hz hw
  set O' : TopologicalSpace.Opens Y := ⟨O, hO⟩
  have hmem : ∀ y : O', Wm y.1 ∈ monomialDomain Φ k j := fun y => by
    show monomial k j (Wm y.1) ∈ Φ.target
    rw [(hkey y.1 y.2).2]
    exact Φ.mapsTo_toFun (hkey y.1 y.2).1.2
  set wmap' : O' → LiftedOpen.{u} (monomialDomain Φ k j) := fun y =>
    LiftedOpen.mk _ (Wm y.1) (hmem y)
  have hwmap'smooth : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ wmap' := fun y =>
    LiftedOpen.contMDiffAt_of_toModel _
      (contMDiffAt_subtype_iff.mpr (hWs y.1 y.2) :
        ContMDiffAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ (fun y : O' => Wm y.1) y)
  have huniq := hπ.2.2.2.2 n O' (π ∘ Subtype.val) (hπ.contMDiff.comp contMDiff_subtype_val)
    (IsInvertible.pullback_comp_val O' hπ.2.2.2.1)
  have hlift : π ∘ (ℓ ∘ wmap') = π ∘ Subtype.val := by
    funext y
    have := congrFun hℓπ (wmap' y)
    simp only [Function.comp_apply] at this ⊢
    rw [this]
    show (chartAt (ComplexModel n) x₀).symm (Φ.invFun (monomial k j (Wm y.1))) = π y.1
    rw [(hkey y.1 y.2).2]
    exact flatInverse_flat Φ (hkey y.1 y.2).1
  have heq := huniq.unique ⟨hℓs.comp hwmap'smooth, hlift⟩ ⟨contMDiff_subtype_val, rfl⟩
  exact congrFun heq ⟨z, hz⟩

/-- A continuous function killed by a local generator of an invertible ideal vanishes. -/
theorem eventually_eq_zero_of_mul_eq_zero {p : Y} {U : Set Y} {h : Y → ℂ} (hU : IsOpen U)
    (hpU : p ∈ U) (hnon : ∀ W : Set Y, IsOpen W → W ⊆ U → W.Nonempty → ∃ y ∈ W, h y ≠ 0)
    {a : Y → ℂ} (ha : ∀ᶠ y in 𝓝 p, ContinuousAt a y) (h0 : ∀ᶠ y in 𝓝 p, h y * a y = 0) :
    ∀ᶠ y in 𝓝 p, a y = 0 := by
  have hev : ∀ᶠ y in 𝓝 p, y ∈ U ∧ ContinuousAt a y ∧ h y * a y = 0 :=
    Filter.Eventually.and (hU.mem_nhds hpU) (ha.and h0)
  obtain ⟨V, hVsub, hVo, hpV⟩ := mem_nhds_iff.mp hev
  filter_upwards [hVo.mem_nhds hpV] with y hy
  by_contra hne
  have hV' : ∀ᶠ y' in 𝓝 y, y' ∈ V ∧ a y' ≠ 0 :=
    Filter.Eventually.and (hVo.mem_nhds hy) ((hVsub hy).2.1.eventually_ne hne)
  obtain ⟨V', hV'sub, hV'o, hyV'⟩ := mem_nhds_iff.mp hV'
  obtain ⟨y', hy', hhy'⟩ := hnon V' hV'o (fun z hz => (hVsub (hV'sub hz).1).1) ⟨y, hyV'⟩
  have := (hVsub (hV'sub hy').1).2.2
  exact (hV'sub hy').2 ((mul_eq_zero.mp this).resolve_left hhy')

/-- **The coefficient matrices of generators of `𝓘_C` are left-inverse at `x`.**  Let `t_l`
(`l ∈ ι`, normal indices `k ≤ l`) be the normal flattening coordinates.  If `g_κ = ∑ b_{κl} t_l`
and `t_l = ∑ c_{lκ} g_κ` near `x`, with `b, c` continuous at `x`, then
`∑_κ c_{lκ}(x) b_{κl'}(x) = δ_{ll'}`. -/
theorem sum_coeff_mul_eq_delta (hΦsrc : Φ.source ⊆ (chartAt (ComplexModel n) x₀).target)
    (hΦ0 : Φ.toFun (chartAt (ComplexModel n) x₀ x₀) = 0) {κ : Type} [Fintype κ]
    {g : κ → M → ℂ} {b : κ → {l : Fin n // k ≤ l.1} → M → ℂ}
    {c : {l : Fin n // k ≤ l.1} → κ → M → ℂ}
    (hbc : ∀ q l, ContinuousAt (b q l) x₀) (hcc : ∀ l q, ContinuousAt (c l q) x₀)
    (hb : ∀ᶠ x in 𝓝 x₀, ∀ q, g q x = ∑ l, b q l x * flatCoord Φ l.1 x)
    (hc : ∀ᶠ x in 𝓝 x₀, ∀ l, flatCoord Φ l.1 x = ∑ q, c l q x * g q x)
    (l l' : {l : Fin n // k ≤ l.1}) :
    ∑ q, c l q x₀ * b q l' x₀ = if l = l' then 1 else 0 := by
  classical
  set mfun : M → ℂ := fun x => (if l = l' then 1 else 0) - ∑ q, c l q x * b q l' x with hm
  -- `∑_{l''} m_{l l''} t_{l''} = 0` near `x₀`
  have hrel : ∀ᶠ x in 𝓝 x₀, ∑ l'' : {l : Fin n // k ≤ l.1},
      ((if l = l'' then 1 else 0) - ∑ q, c l q x * b q l'' x) * flatCoord Φ l''.1 x = 0 := by
    filter_upwards [hb, hc] with x hbx hcx
    simp only [sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [hcx l, sub_eq_zero]
    simp only [hbx, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  -- the normal line through `x₀` in the direction `l'`
  set line : ℂ → ComplexModel n := fun s => WithLp.toLp 2 (fun i => if i = l'.1 then s else 0)
    with hline
  have hline0 : line 0 = 0 := by ext i; simp [hline]
  have hlinec : Continuous line := (PiLp.continuous_toLp 2 _).comp
    (continuous_pi fun i => by split_ifs <;> [exact continuous_id; exact continuous_const])
  have h0T : (0 : ComplexModel n) ∈ Φ.target := by
    rw [← hΦ0]; exact Φ.mapsTo_toFun Φ.center_mem_source
  have hT : ∀ᶠ s in 𝓝 (0 : ℂ), line s ∈ Φ.target := by
    have := hlinec.continuousAt.eventually (Φ.isOpen_target.mem_nhds (by rw [hline0]; exact h0T))
    exact this
  set pt : ℂ → M := fun s => (chartAt (ComplexModel n) x₀).symm (Φ.invFun (line s)) with hpt
  have hinv0 : Φ.invFun 0 = chartAt (ComplexModel n) x₀ x₀ := by
    rw [← hΦ0]; exact Φ.left_inv _ Φ.center_mem_source
  have hptc : ContinuousAt pt 0 := by
    have h1 : ContinuousAt Φ.invFun (line 0) := by
      rw [hline0]
      exact (Φ.invFun_holomorphic.differentiableAt (Φ.isOpen_target.mem_nhds h0T)).continuousAt
    have h2 : ContinuousAt (chartAt (ComplexModel n) x₀).symm (Φ.invFun (line 0)) := by
      rw [hline0, hinv0]
      exact (chartAt (ComplexModel n) x₀).continuousAt_symm
        ((chartAt (ComplexModel n) x₀).map_source (mem_chart_source _ x₀))
    exact ContinuousAt.comp (f := fun s => Φ.invFun (line s)) h2 (h1.comp hlinec.continuousAt)
  have hpt0 : pt 0 = x₀ := by
    simp only [hpt, hline0, hinv0]
    exact (chartAt (ComplexModel n) x₀).left_inv (mem_chart_source _ x₀)
  have hsumc : ContinuousAt (fun x => ∑ q, c l q x * b q l' x) x₀ :=
    tendsto_finsetSum _ fun q _ => (hcc l q).mul (hbc q l')
  have hmc : ContinuousAt mfun x₀ := continuousAt_const.sub hsumc
  have hpt_t : Tendsto pt (𝓝 0) (𝓝 x₀) := by
    have := hptc.tendsto
    rwa [hpt0] at this
  have hlim : Tendsto (fun s => mfun (pt s)) (𝓝[≠] (0 : ℂ)) (𝓝 (mfun x₀)) :=
    (hmc.tendsto.comp hpt_t).mono_left nhdsWithin_le_nhds
  have hzero : ∀ᶠ s in 𝓝[≠] (0 : ℂ), mfun (pt s) = 0 := by
    have h1 := (hpt_t.eventually hrel).and hT
    filter_upwards [nhdsWithin_le_nhds h1, self_mem_nhdsWithin] with s hs hs0
    obtain ⟨hrel_s, hTs⟩ := hs
    have hflat_s := (flatInverse_mem Φ hTs hΦsrc).2
    have hcoord : ∀ l'' : {l : Fin n // k ≤ l.1}, flatCoord Φ l''.1 (pt s) =
        if l''.1 = l'.1 then s else 0 := by
      intro l''
      show (Φ.toFun (chartAt (ComplexModel n) x₀ ((chartAt (ComplexModel n) x₀).symm
        (Φ.invFun (line s))))) l''.1 = _
      rw [hflat_s]
    have hrel_s' : ∑ l'' : {l : Fin n // k ≤ l.1},
        ((if l = l'' then 1 else 0) - ∑ q, c l q (pt s) * b q l'' (pt s)) *
          flatCoord Φ l''.1 (pt s) = 0 := hrel_s
    simp only [hcoord] at hrel_s'
    rw [Finset.sum_eq_single l'] at hrel_s'
    · simp only [if_true] at hrel_s'
      exact (mul_eq_zero.mp hrel_s').resolve_right hs0
    · intro l'' _ hne
      rw [if_neg (fun h => hne (Subtype.ext h)), mul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  have := tendsto_nhds_unique hlim (tendsto_const_nhds.congr' (hzero.mono fun s hs => hs.symm))
  simp only [hm, sub_eq_zero] at this
  exact this.symm

end SGPT.GAGA.ChowBl
