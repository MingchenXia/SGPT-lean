import SGPT.GAGA.ChowBlImage
import SGPT.GAGA.ChowBlLift
import SGPT.Foundations.Analysis.Pending.BlowupLocalSurjectivity

/-!
# The map of a blow-up to `ℙʳ` given by generators of `𝓘_C(m)`


Let `Ψ : M → ℙᴺ` be a holomorphic embedding of a compact complex manifold, `π : Y → M` the
blow-up of `M` along a nowhere dense closed submanifold `C` (`IsBlowupAlong`, a universal
property), and `P_0, …, P_r` homogeneous polynomials of degree `m` generating the ideal of the
cone over `Ψ(C)` (Chow's theorem, `chow_image`).  Their restrictions `f_k = P_k(Λᵢ)` generate
`𝓘_C` (`vanishingIdeal_mem_iff_isInSpanAt_genFun`), so near every `p ∈ Y`

  `f_k ∘ π = h · w_k`,  `h` a local generator of the invertible ideal `𝓘_C 𝒪_Y`,

with `w(p) ≠ 0` (`exists_coeff_of_generators`: `h` is itself a combination of the `f_k ∘ π`,
`h = G h` forces `G(p) = 1`).  The point `[w(p)] ∈ ℙʳ` does not depend on the choices
(`IsBlRep.pmk_eq`: two representations agree where both generators are nonzero, a dense set,
hence at `p` by continuity), which defines the map `blowupMap : Y → ℙʳ`; near every point it is
`[w]` for one holomorphic `w` (`IsBlRep.eventually_blowupMap_eq`).  Off the exceptional divisor
it is `x ↦ [f(π x)]`, the map given by the linear system `|𝓘_C(m)|`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Set Filter Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open SGPT.GAGA.H0S
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace
open scoped Manifold ContDiff

noncomputable section

namespace SGPT.GAGA.ChowBl

universe u

/-! ### Topological lemmas -/

section Topology

variable {Y : Type*} [TopologicalSpace Y]

/-- Two functions, the first continuous, both nonzero on a nonempty part of every nonempty open
subset of their domains, are frequently simultaneously nonzero near a common point. -/
theorem frequently_ne_zero_and {y : Y} {a b : Y → ℂ} {U V : Set Y} (hU : IsOpen U)
    (hV : IsOpen V) (hyU : y ∈ U) (hyV : y ∈ V) (ha : ContinuousOn a U)
    (ha0 : ∀ W : Set Y, IsOpen W → W ⊆ U → W.Nonempty → ∃ y' ∈ W, a y' ≠ 0)
    (hb0 : ∀ W : Set Y, IsOpen W → W ⊆ V → W.Nonempty → ∃ y' ∈ W, b y' ≠ 0) :
    ∃ᶠ y' in 𝓝 y, a y' ≠ 0 ∧ b y' ≠ 0 := by
  rw [Filter.frequently_iff]
  intro s hs
  obtain ⟨W, hWs, hWo, hyW⟩ := mem_nhds_iff.mp hs
  have hW₁ : IsOpen (W ∩ U ∩ V) := (hWo.inter hU).inter hV
  obtain ⟨y₁, hy₁, ha₁⟩ := ha0 _ hW₁ (fun _ h => h.1.2) ⟨y, ⟨hyW, hyU⟩, hyV⟩
  have hW₂ : IsOpen (W ∩ U ∩ V ∩ (U ∩ a ⁻¹' {0}ᶜ)) :=
    hW₁.inter (ha.isOpen_inter_preimage hU isOpen_compl_singleton)
  obtain ⟨y₂, hy₂, hb₂⟩ := hb0 _ hW₂ (fun _ h => h.1.2) ⟨y₁, hy₁, hy₁.1.2, ha₁⟩
  exact ⟨y₂, hWs hy₂.1.1.1, hy₂.2.2, hb₂⟩

/-- **Independence of the representation**: if `a u = b v` near `y`, with `a, b` frequently
simultaneously nonzero near `y` and `u, v` continuous and nonzero at `y`, then `[u(y)] = [v(y)]`. -/
theorem pmk_eq_of_smul_eq {r : ℕ} {y : Y} {a b : Y → ℂ} {u v : Y → Fin (r + 1) → ℂ}
    (hu : ContinuousAt u y) (hv : ContinuousAt v y) (hu0 : u y ≠ 0) (hv0 : v y ≠ 0)
    (hfreq : ∃ᶠ y' in 𝓝 y, a y' ≠ 0 ∧ b y' ≠ 0)
    (heq : ∀ᶠ y' in 𝓝 y, a y' • u y' = b y' • v y') : pmk (u y) = pmk (v y) := by
  have h1 : Tendsto (fun y' => pmk (u y')) (𝓝 y) (𝓝 (pmk (u y))) :=
    ((continuousAt_pmk hu0).comp hu).tendsto
  have h2 : Tendsto (fun y' => pmk (v y')) (𝓝 y) (𝓝 (pmk (v y))) :=
    ((continuousAt_pmk hv0).comp hv).tendsto
  refine tendsto_nhds_unique_of_frequently_eq h1 h2 ?_
  have hu' : ∀ᶠ y' in 𝓝 y, u y' ≠ 0 := hu.eventually_ne hu0
  have hv' : ∀ᶠ y' in 𝓝 y, v y' ≠ 0 := hv.eventually_ne hv0
  refine (hfreq.and_eventually (heq.and (hu'.and hv'))).mono ?_
  rintro y' ⟨⟨ha, hb⟩, he, hu0', hv0'⟩
  refine (pmk_eq_pmk_iff hu0' hv0').mpr ⟨b y' / a y', div_ne_zero hb ha, ?_⟩
  calc u y' = (a y')⁻¹ • (a y' • u y') := by rw [smul_smul, inv_mul_cancel₀ ha, one_smul]
    _ = (a y')⁻¹ • (b y' • v y') := by rw [he]
    _ = (b y' / a y') • v y' := by rw [smul_smul, div_eq_inv_mul]

/-- `h = G h` near `p`, with `h` nonzero on a part of every nonempty open subset of `U ∋ p`,
forces `G(p) = 1` (for `G` continuous at `p`). -/
theorem eq_one_of_eq_mul {p : Y} {h G : Y → ℂ} {U : Set Y} (hU : IsOpen U) (hpU : p ∈ U)
    (hnon : ∀ W : Set Y, IsOpen W → W ⊆ U → W.Nonempty → ∃ y ∈ W, h y ≠ 0)
    (hG : ContinuousAt G p) (heq : ∀ᶠ y in 𝓝 p, h y = G y * h y) : G p = 1 := by
  by_contra hne
  have hev : ∀ᶠ y in 𝓝 p, y ∈ U ∧ h y = G y * h y ∧ G y ≠ 1 :=
    Filter.Eventually.and (hU.mem_nhds hpU) (heq.and (hG.eventually (isOpen_ne.mem_nhds hne)))
  obtain ⟨W, hWsub, hWopen, hpW⟩ := mem_nhds_iff.mp hev
  obtain ⟨y, hyW, hy⟩ := hnon W hWopen (fun y hy => (hWsub hy).1) ⟨p, hpW⟩
  obtain ⟨-, h1, h2⟩ := hWsub hyW
  have : (1 - G y) * h y = 0 := by rw [sub_mul, one_mul, ← h1, sub_self]
  rcases mul_eq_zero.mp this with h' | h'
  · exact h2 (sub_eq_zero.mp h').symm
  · exact hy h'

end Topology

/-! ### Coefficients of generators of `𝓘_C` along a local generator of `𝓘_C 𝒪_Y` -/

section Coeff

variable {n : ℕ} {M Y : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M] [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
  [IsComplexManifold n Y] {C : Set M} {π : Y → M}

/-- **Coefficients along the exceptional divisor.**  Let `g_k` be germs at `π p` which lie in
`𝓘_C` and generate it, and let `h` be a local generator of the invertible ideal `𝓘_C 𝒪_Y` on
`U ∋ p`.  Then `g_k ∘ π = w_k h` near `p` with `w_k` holomorphic at `p` and `w(p) ≠ 0`. -/
theorem exists_coeff_of_generators (hπ : IsBlowupAlong n C π) {p : Y} {U : Set Y} {h : Y → ℂ}
    (hU : IsOpen U) (hpU : p ∈ U)
    (hh : MDifferentiableOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) h U)
    (hnon : ∀ W : Set Y, IsOpen W → W ⊆ U → W.Nonempty → ∃ y ∈ W, h y ≠ 0)
    (hiff : ∀ y ∈ U, ∀ g, (GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) C)).mem y g ↔
      IsInSpanAt (n := n) (· = h) y g)
    {ι : Type} [Fintype ι] {g : ι → M → ℂ}
    (hgI : ∀ k, (vanishingIdeal (n := n) C).mem (π p) (g k))
    (hgen : ∀ a, (vanishingIdeal (n := n) C).mem (π p) a → ∃ c : ι → M → ℂ,
      (∀ k, HolomorphicAt n (c k) (π p)) ∧ a =ᶠ[𝓝 (π p)] fun x => ∑ k, c k x * g k x) :
    ∃ w : Y → ι → ℂ, (∀ k, HolomorphicAt n (fun y => w y k) p) ∧
      (∀ᶠ y in 𝓝 p, ∀ k, g k (π y) = h y * w y k) ∧ w p ≠ 0 := by
  classical
  have hπs : ∀ y, ContMDiffAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ π y :=
    fun y => hπ.contMDiff y
  have hhol : HolomorphicAt n h p := by
    filter_upwards [hU.mem_nhds hpU] with y hy
    exact (hh y hy).mdifferentiableAt (hU.mem_nhds hy)
  have hcoef : ∀ k, ∃ a : Y → ℂ, HolomorphicAt n a p ∧
      (fun y => g k (π y)) =ᶠ[𝓝 p] fun y => a y * h y := by
    intro k
    have hmem : (GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) C)).mem p (g k ∘ π) :=
      isInSpanAt_of_eq_mul (S := fun s => ∃ a, (vanishingIdeal (n := n) C).mem (π p) a ∧
        s = a ∘ π) (s := g k ∘ π) ⟨g k, hgI k, rfl⟩
        ((hgI k).1.comp_contMDiff (Eventually.of_forall hπs))
        (holomorphicAt_const 1) (Eventually.of_forall fun _ => by simp)
    obtain ⟨-, a, ha, heq⟩ := isInSpanAt_eq_iff.mp ((hiff p hpU _).mp hmem)
    exact ⟨a, ha, heq⟩
  choose w hw hweq using hcoef
  refine ⟨fun y k => w k y, hw, ?_, ?_⟩
  · filter_upwards [eventually_all.2 hweq] with y hy k
    rw [hy k, mul_comm]
  · -- `h` is itself a combination of the `g_k ∘ π`
    have hmemh : IsInSpanAt (n := n) (fun s => ∃ a, (vanishingIdeal (n := n) C).mem (π p) a ∧
        s = a ∘ π) p h :=
      (hiff p hpU h).mpr (isInSpanAt_of_eq_mul rfl hhol (holomorphicAt_const 1)
        (Eventually.of_forall fun _ => by simp))
    obtain ⟨-, N', s, β, hs, hβ, hsum⟩ := hmemh
    choose a ha hsa using hs
    choose c hc hceq using fun l => hgen (a l) (ha l)
    set G : Y → ℂ := fun y => ∑ k, (∑ l, β l y * c l k (π y)) * w k y with hG
    have hGhol : HolomorphicAt n G p :=
      HolomorphicAt.sum Finset.univ fun k _ => (HolomorphicAt.sum Finset.univ fun l _ => (hβ l).mul
        ((hc l k).comp_contMDiff (Eventually.of_forall hπs))).mul (hw k)
    have hGeq : ∀ᶠ y in 𝓝 p, h y = G y * h y := by
      have hcev : ∀ᶠ y in 𝓝 p, ∀ l, a l (π y) = ∑ k, c l k (π y) * g k (π y) :=
        hπ.contMDiff.continuous.continuousAt.eventually (eventually_all.2 hceq)
      filter_upwards [hsum, hcev, eventually_all.2 hweq] with y h1 h2 h3
      conv_lhs => rw [h1]
      have e1 : ∀ l, s l y = ∑ k, c l k (π y) * (w k y * h y) := fun l => by
        rw [hsa l, Function.comp_apply, h2 l]
        exact Finset.sum_congr rfl fun k _ => by rw [h3 k]
      simp only [e1, hG, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun (k : ι) _ => Finset.sum_congr rfl fun (l : Fin N') _ => by
        ring
    have hG1 : G p = 1 := eq_one_of_eq_mul hU hpU hnon hGhol.continuousAt hGeq
    intro hw0
    have : G p = 0 := by
      refine Finset.sum_eq_zero fun k _ => ?_
      have : w k p = 0 := congrFun hw0 k
      rw [this, mul_zero]
    rw [hG1] at this
    exact one_ne_zero this

end Coeff

/-! ### The map `Y → ℙʳ` -/

section Map

variable {n N r m : ℕ} {M Y : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M] [CompactSpace M] [TopologicalSpace Y]
  [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
  {Ψ : M → ComplexProjectiveSpace N} {C : Set M} {π : Y → M}
  {P : Fin (r + 1) → MvPolynomial (Fin (N + 1)) ℂ}

/-- The chart change of the restrictions of a homogeneous polynomial of degree `m`:
`f^{(i')} = (Λ_{i'})_i^m f^{(i)}`. -/
theorem genFun_chart_change {Q : MvPolynomial (Fin (N + 1)) ℂ} (hQ : Q.IsHomogeneous m)
    {i i' : Fin (N + 1)} {x : M} (hi : Ψ x ∈ (affineChart i).source)
    (hi' : Ψ x ∈ (affineChart i').source) :
    genFun Ψ i' Q x = (coneLift Ψ i' x i) ^ m * genFun Ψ i Q x := by
  set a := affineLift i (affineChart i (Ψ x)) with ha
  set b := affineLift i' (affineChart i' (Ψ x)) with hb
  have hpa : pmk a = Ψ x := by
    rw [pmk_eq_mk (affineLift_ne_zero _ _)]; exact (affineChart i).left_inv hi
  have hpb : pmk b = Ψ x := by
    rw [pmk_eq_mk (affineLift_ne_zero _ _)]; exact (affineChart i').left_inv hi'
  obtain ⟨t, ht, hab⟩ := (pmk_eq_pmk_iff (affineLift_ne_zero _ _) (affineLift_ne_zero _ _)).mp
    (hpa.trans hpb.symm)
  have hti : t * b i = 1 := by
    have := congrFun hab i
    simp only [affineLift_same, Pi.smul_apply, smul_eq_mul] at this
    exact this.symm
  have hcone : coneLift Ψ i' x i = b i := rfl
  rw [hcone]
  show MvPolynomial.eval (fun j => b j) Q = b i ^ m * MvPolynomial.eval (fun j => a j) Q
  have : (fun j => a j) = t • b := by funext j; exact congrFun hab j
  rw [this, SGPT.GAGA.PN.eval_smul_of_isHomogeneous hQ, ← mul_assoc, ← mul_pow, mul_comm (b i),
    hti, one_pow, one_mul]

variable (Ψ π P) in
/-- `w` represents the map to `ℙʳ` at `p`: `f_k^{(i)} ∘ π = h w_k` near `p`, with `h`
continuous on a neighbourhood `U` and nonzero on a part of every nonempty open subset of `U`,
`w` continuous and nonzero at `p`. -/
def IsBlRep (p : Y) (i : Fin (N + 1)) (U : Set Y) (h : Y → ℂ) (w : Y → Fin (r + 1) → ℂ) :
    Prop :=
  Ψ (π p) ∈ (affineChart i).source ∧ IsOpen U ∧ p ∈ U ∧ ContinuousOn h U ∧
    (∀ W : Set Y, IsOpen W → W ⊆ U → W.Nonempty → ∃ y ∈ W, h y ≠ 0) ∧
    (∀ᶠ y in 𝓝 p, ContinuousAt w y) ∧
    (∀ᶠ y in 𝓝 p, ∀ k, genFun Ψ i (P k) (π y) = h y * w y k) ∧ w p ≠ 0

/-- **Two representations give the same point of `ℙʳ`.** -/
theorem IsBlRep.pmk_eq (hΨ : IsHolomorphicEmbedding (n := n) Ψ) (hπc : Continuous π)
    (hP : ∀ k, (P k).IsHomogeneous m) {p : Y} {i i' : Fin (N + 1)} {U U' : Set Y}
    {h h' : Y → ℂ} {w w' : Y → Fin (r + 1) → ℂ} (h1 : IsBlRep Ψ π P p i U h w)
    (h2 : IsBlRep Ψ π P p i' U' h' w') : pmk (w p) = pmk (w' p) := by
  obtain ⟨hi, hU, hpU, hhc, hnon, hwc, hweq, hw0⟩ := h1
  obtain ⟨hi', hU', hpU', hhc', hnon', hwc', hweq', hw0'⟩ := h2
  -- the chart change factor
  set lam : Y → ℂ := fun y => coneLift Ψ i' (π y) i ^ m with hlam
  have hlam0 : lam p ≠ 0 := by
    have : coneLift Ψ i' (π p) i ≠ 0 := by
      intro h0
      have hpa : pmk (affineLift i' (affineChart i' (Ψ (π p)))) = Ψ (π p) := by
        rw [pmk_eq_mk (affineLift_ne_zero _ _)]; exact (affineChart i').left_inv hi'
      have := (mem_affineChart_source_pmk_iff i (affineLift_ne_zero i' _)).mp
        (by rw [hpa]; exact hi)
      exact this h0
    exact pow_ne_zero _ this
  have hlamc : ContinuousAt lam p := by
    have hx : ContinuousAt (fun x => coneLift Ψ i' x i) (π p) :=
      (holomorphicAt_comp_coneLift hΨ hi' (c := fun Z => Z i)
        (Eventually.of_forall fun _ => (EuclideanSpace.proj (𝕜 := ℂ) i).differentiableAt)
        ).continuousAt
    exact (hx.comp hπc.continuousAt).pow m
  have hsrc : ∀ᶠ y in 𝓝 p, Ψ (π y) ∈ (affineChart i).source ∧ Ψ (π y) ∈ (affineChart i').source :=
    ((hΨ.continuous.comp hπc).continuousAt.eventually
      ((affineChart i).open_source.mem_nhds hi)).and
    ((hΨ.continuous.comp hπc).continuousAt.eventually
      ((affineChart i').open_source.mem_nhds hi'))
  refine pmk_eq_of_smul_eq (a := fun y => lam y * h y) (b := h') hwc.self_of_nhds
    hwc'.self_of_nhds hw0 hw0' ?_ ?_
  · have hf := frequently_ne_zero_and hU hU' hpU hpU' hhc hnon hnon'
    refine (hf.and_eventually (hlamc.eventually_ne hlam0)).mono ?_
    rintro y ⟨⟨h1, h2⟩, h3⟩
    exact ⟨mul_ne_zero h3 h1, h2⟩
  · filter_upwards [hweq, hweq', hsrc] with y hy hy' hys
    funext k
    have hc := genFun_chart_change (hP k) hys.1 hys.2
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [← hy' k, hc, hy k]
    ring

/-- A representation at `p` is a representation at every point near `p`. -/
theorem IsBlRep.eventually (hΨ : IsHolomorphicEmbedding (n := n) Ψ) (hπc : Continuous π)
    {p : Y} {i : Fin (N + 1)} {U : Set Y} {h : Y → ℂ} {w : Y → Fin (r + 1) → ℂ}
    (hrep : IsBlRep Ψ π P p i U h w) : ∀ᶠ y in 𝓝 p, IsBlRep Ψ π P y i U h w := by
  obtain ⟨hi, hU, hpU, hhc, hnon, hwc, hweq, hw0⟩ := hrep
  have hsrc : ∀ᶠ y in 𝓝 p, Ψ (π y) ∈ (affineChart i).source :=
    (hΨ.continuous.comp hπc).continuousAt.eventually ((affineChart i).open_source.mem_nhds hi)
  have hw0' : ∀ᶠ y in 𝓝 p, w y ≠ 0 := hwc.self_of_nhds.eventually_ne hw0
  filter_upwards [hsrc, hU.mem_nhds hpU, hwc.eventually_nhds, hweq.eventually_nhds, hw0']
    with y h1 h2 h3 h4 h5
  exact ⟨h1, hU, h2, hhc, hnon, h3, h4, h5⟩

/-- **Existence of representations**, from the generators of Chow's theorem. -/
theorem exists_isBlRep (hΨ : IsHolomorphicEmbedding (n := n) Ψ) (hπ : IsBlowupAlong n C π)
    (hgen : (coneIdeal (Ψ '' C)).GeneratedOn (SGPT.GAGA.PN.puncture (SGPT.GAGA.PN.ConeSpace N))
      (fun k => SGPT.GAGA.PN.polyTuple (P k)))
    (p : Y) : ∃ (U : Set Y) (h : Y → ℂ) (w : Y → Fin (r + 1) → ℂ),
      IsBlRep Ψ π P p (chartIndex (Ψ (π p))) U h w ∧
      (∀ k, HolomorphicAt n (fun y => w y k) p) := by
  classical
  set i := chartIndex (Ψ (π p))
  have hi : Ψ (π p) ∈ (affineChart i).source := mem_affineChart_chartIndex _
  obtain ⟨U, hU, hpU, h, hh, hnon, hiff⟩ := hπ.2.2.2.1 p
  have hspan := vanishingIdeal_mem_iff_isInSpanAt_genFun hΨ hgen hi
  obtain ⟨w, hw, hweq, hw0⟩ := exists_coeff_of_generators hπ hU hpU hh hnon hiff
    (g := fun k => genFun Ψ i (P k))
    (fun k => (hspan _).mpr (CoherentIdealColon.isInSpanAt_range_iff.mpr
      ⟨holomorphicAt_genFun hΨ hi _, fun l _ => if l = k then 1 else 0,
        fun l => holomorphicAt_const _, Eventually.of_forall fun x => by simp⟩))
    (fun a ha => by
      obtain ⟨-, c, hc, hca⟩ := CoherentIdealColon.isInSpanAt_range_iff.mp ((hspan a).mp ha)
      exact ⟨c, hc, hca⟩)
  have hwc : ∀ᶠ y in 𝓝 p, ContinuousAt w y := by
    have : ∀ᶠ y in 𝓝 p, ∀ k, HolomorphicAt n (fun y => w y k) y :=
      eventually_all.2 fun k => (hw k).eventually
    filter_upwards [this] with y hy
    exact continuousAt_pi.mpr fun k => (hy k).continuousAt
  refine ⟨U, h, w, ⟨hi, hU, hpU, fun y hy => ?_, hnon, hwc, hweq, hw0⟩, hw⟩
  exact ((hh y hy).mdifferentiableAt (hU.mem_nhds hy)).continuousAt.continuousWithinAt

open Classical in
/-- **The map of the blow-up to `ℙʳ`** given by the generators `P_k` of `𝓘_{Ψ(C)}(m)`: at `p`,
`[w(p)]` for any representation `f_k ∘ π = h w_k` (a point `[f(π p)]` off the exceptional
divisor). -/
def blowupMap (Ψ : M → ComplexProjectiveSpace N) (π : Y → M)
    (P : Fin (r + 1) → MvPolynomial (Fin (N + 1)) ℂ) (p : Y) : ComplexProjectiveSpace r :=
  if hex : ∃ (i : Fin (N + 1)) (U : Set Y) (h : Y → ℂ) (w : Y → Fin (r + 1) → ℂ),
      IsBlRep Ψ π P p i U h w then pmk (Classical.choose (Classical.choose_spec
        (Classical.choose_spec (Classical.choose_spec hex))) p)
  else affinePoint 0 0

/-- The map of the blow-up is given by any representation. -/
theorem blowupMap_eq (hΨ : IsHolomorphicEmbedding (n := n) Ψ) (hπc : Continuous π)
    (hP : ∀ k, (P k).IsHomogeneous m) {p : Y} {i : Fin (N + 1)} {U : Set Y} {h : Y → ℂ}
    {w : Y → Fin (r + 1) → ℂ} (hrep : IsBlRep Ψ π P p i U h w) :
    blowupMap Ψ π P p = pmk (w p) := by
  have hex : ∃ (i : Fin (N + 1)) (U : Set Y) (h : Y → ℂ) (w : Y → Fin (r + 1) → ℂ),
      IsBlRep Ψ π P p i U h w := ⟨i, U, h, w, hrep⟩
  rw [blowupMap, dif_pos hex]
  exact IsBlRep.pmk_eq hΨ hπc hP (Classical.choose_spec (Classical.choose_spec
    (Classical.choose_spec (Classical.choose_spec hex)))) hrep

/-- **Local form of the map of the blow-up**: near every point it is `[w]` for one
holomorphic `w`. -/
theorem exists_eventually_blowupMap_eq (hΨ : IsHolomorphicEmbedding (n := n) Ψ)
    (hπ : IsBlowupAlong n C π) (hP : ∀ k, (P k).IsHomogeneous m)
    (hgen : (coneIdeal (Ψ '' C)).GeneratedOn (SGPT.GAGA.PN.puncture (SGPT.GAGA.PN.ConeSpace N))
      (fun k => SGPT.GAGA.PN.polyTuple (P k)))
    (p : Y) : ∃ (U : Set Y) (h : Y → ℂ) (w : Y → Fin (r + 1) → ℂ),
      IsBlRep Ψ π P p (chartIndex (Ψ (π p))) U h w ∧
      (∀ k, HolomorphicAt n (fun y => w y k) p) ∧
      ∀ᶠ y in 𝓝 p, blowupMap Ψ π P y = pmk (w y) := by
  obtain ⟨U, h, w, hrep, hw⟩ := exists_isBlRep hΨ hπ hgen p
  refine ⟨U, h, w, hrep, hw, ?_⟩
  filter_upwards [hrep.eventually hΨ hπ.contMDiff.continuous] with y hy
  exact blowupMap_eq hΨ hπ.contMDiff.continuous hP hy

end Map

end SGPT.GAGA.ChowBl
