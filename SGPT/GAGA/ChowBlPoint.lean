import SGPT.GAGA.ChowBlNormal

/-!
# Local data of the blow-up map at points over the centre


Setting of `ChowBlMap`: `Ψ : M → ℙᴺ` a holomorphic embedding, `π : Y → M` the blow-up along `C`,
`P_q` (`q ≤ r`) homogeneous of degree `m` generating the ideal of the cone over `Ψ(C)`
(`BlData`).  Fix `x₀ ∈ C` with a flattening `Φ` of `C` at `x₀` onto `ℂᵏ × 0` (`FlatData`):
the restrictions `g_q = f_q^{(i)}` of the `P_q` satisfy `g_q = ∑_l b_{ql} t_l` and
`t_l = ∑_q c_{lq} g_q` near `x₀`, `t_l` the normal coordinates, and `c(x₀) b(x₀) = 1`.

For `p ∈ π⁻¹(x₀)` and a local generator `h` of `𝓘_C 𝒪_Y` at `p` (`exists_pointData`):
`g_q ∘ π = h w_q`, `t_l ∘ π = h α_l`, `w(p) ≠ 0`, `α(p) ≠ 0` and `w_q = ∑_l b_{ql}(π ·) α_l`
near `p`.  For a normal index `j` with `α_j(p) ≠ 0`, `W = (α_l/α_j (l ≠ j normal), t_i ∘ π)` is a
holomorphic local solution of `σⱼ ∘ W = Φ ∘ e ∘ π` (`exists_monomialInverse`), inverted by the
lift `ℓⱼ` of the `j`-th monomial chart.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Set Filter Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open SGPT.Foundations.Analysis.Pending.BlowupFlatCoordinates
open SGPT.Foundations.Analysis.Pending.BlowupMonomialCharts
open SGPT.GAGA.H0S
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace
open scoped Manifold ContDiff

noncomputable section

namespace SGPT.GAGA.ChowBl

universe u

variable {n N r m : ℕ} {M Y : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M] [CompactSpace M] [TopologicalSpace Y]
  [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
  {Ψ : M → ComplexProjectiveSpace N} {C : Set M} {π : Y → M}
  {P : Fin (r + 1) → MvPolynomial (Fin (N + 1)) ℂ}

variable (n Ψ C π P m) in
/-- The data of the projective embedding of a blow-up. -/
structure BlData : Prop where
  emb : IsHolomorphicEmbedding (n := n) Ψ
  blowup : IsBlowupAlong n C π
  hom : ∀ q, (P q).IsHomogeneous m
  gen : (coneIdeal (Ψ '' C)).GeneratedOn (SGPT.GAGA.PN.puncture (SGPT.GAGA.PN.ConeSpace N))
    (fun q => SGPT.GAGA.PN.polyTuple (P q))

/-- Sums over `Fin n` of terms vanishing below `k` are sums over the normal indices. -/
theorem sum_eq_sum_normalIdx {k : ℕ} (f : Fin n → ℂ) (hf : ∀ i : Fin n, i.1 < k → f i = 0) :
    ∑ i, f i = ∑ l : NormalIdx n k, f l.1 := by
  rw [← Fintype.sum_subtype_add_sum_subtype (fun i : Fin n => k ≤ i.1) f]
  have : ∑ i : {i : Fin n // ¬k ≤ i.1}, f i.1 = 0 :=
    Finset.sum_eq_zero fun i _ => hf i.1 (by have := i.2; omega)
  rw [this, add_zero]

/-- The restrictions `g_q` lie in `𝓘_C` and generate it, at every point of `Ψ⁻¹(U_i)`. -/
theorem genFun_mem_and_generate (hd : BlData n m Ψ C π P) {i : Fin (N + 1)} {x : M}
    (hx : Ψ x ∈ (affineChart i).source) :
    (∀ q, (vanishingIdeal (n := n) C).mem x (genFun Ψ i (P q))) ∧
    ∀ a, (vanishingIdeal (n := n) C).mem x a → ∃ c : Fin (r + 1) → M → ℂ,
      (∀ q, HolomorphicAt n (c q) x) ∧ a =ᶠ[𝓝 x] fun x' => ∑ q, c q x' * genFun Ψ i (P q) x' := by
  have hspan := vanishingIdeal_mem_iff_isInSpanAt_genFun hd.emb hd.gen hx
  refine ⟨fun q => (hspan _).mpr (CoherentIdealColon.isInSpanAt_range_iff.mpr
      ⟨holomorphicAt_genFun hd.emb hx _, fun l _ => if l = q then 1 else 0,
        fun l => holomorphicAt_const _, Eventually.of_forall fun x => by simp⟩), fun a ha => ?_⟩
  obtain ⟨-, c, hc, hca⟩ := CoherentIdealColon.isInSpanAt_range_iff.mp ((hspan a).mp ha)
  exact ⟨c, hc, hca⟩

variable (Ψ C P) in
/-- A flattening of `C` at `x₀ ∈ C` with the coefficient matrices of the generators. -/
structure FlatData (x₀ : M) (k : ℕ) (Φ : LocalHolomorphicEquivAt (n := n)
    (chartAt (ComplexModel n) x₀ x₀)) (b : Fin (r + 1) → NormalIdx n k → M → ℂ)
    (c : NormalIdx n k → Fin (r + 1) → M → ℂ) : Prop where
  mem : x₀ ∈ C
  src : Φ.source ⊆ (chartAt (ComplexModel n) x₀).target
  zero : Φ.toFun (chartAt (ComplexModel n) x₀ x₀) = 0
  flat : ∀ {y : M}, y ∈ (chartAt (ComplexModel n) x₀).source →
    chartAt (ComplexModel n) x₀ y ∈ Φ.source →
      (y ∈ C ↔ Φ.toFun (chartAt (ComplexModel n) x₀ y) ∈ complexCoordinatePlane n k)
  hb : ∀ q l, HolomorphicAt n (b q l) x₀
  hc : ∀ l q, HolomorphicAt n (c l q) x₀
  bsum : ∀ᶠ x in 𝓝 x₀, ∀ q,
    genFun Ψ (chartIndex (Ψ x₀)) (P q) x = ∑ l, b q l x * flatCoord Φ l.1 x
  csum : ∀ᶠ x in 𝓝 x₀, ∀ l,
    flatCoord Φ l.1 x = ∑ q, c l q x * genFun Ψ (chartIndex (Ψ x₀)) (P q) x
  delta : ∀ l l', ∑ q, c l q x₀ * b q l' x₀ = if l = l' then 1 else 0

/-- **Flat data exist at every point of the centre.** -/
theorem exists_flatData (hd : BlData n m Ψ C π P) {x₀ : M} (hx₀ : x₀ ∈ C) :
    ∃ (k : ℕ) (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x₀ x₀))
      (b : Fin (r + 1) → NormalIdx n k → M → ℂ) (c : NormalIdx n k → Fin (r + 1) → M → ℂ),
      FlatData Ψ C P x₀ k Φ b c := by
  classical
  obtain ⟨k, -, -, Φ, hΦsrc, hΦ0, hflat⟩ := hd.blowup.1.2 x₀ hx₀
  have hflat' : ∀ {y : M}, y ∈ (chartAt (ComplexModel n) x₀).source →
      chartAt (ComplexModel n) x₀ y ∈ Φ.source →
        (y ∈ C ↔ Φ.toFun (chartAt (ComplexModel n) x₀ y) ∈ complexCoordinatePlane n k) :=
    fun hy hy' => hflat hy hy'
  set i := chartIndex (Ψ x₀)
  have hi : Ψ x₀ ∈ (affineChart i).source := mem_affineChart_chartIndex _
  obtain ⟨hgI, hgen⟩ := genFun_mem_and_generate hd hi
  have hx₀flat : x₀ ∈ flatDomain Φ := mem_flatDomain_self Φ
  -- Hadamard coefficients of the generators
  have hbex : ∀ q, ∃ b : NormalIdx n k → M → ℂ, (∀ l, HolomorphicAt n (b l) x₀) ∧
      ∀ᶠ x in 𝓝 x₀, genFun Ψ i (P q) x = ∑ l, b l x * flatCoord Φ l.1 x := by
    intro q
    obtain ⟨b', hb'0, hb'h, hb'eq⟩ := exists_eq_sum_flatCoord Φ hΦsrc hflat' hx₀flat (hgI q)
    refine ⟨fun l => b' l.1, fun l => hb'h l.1, ?_⟩
    filter_upwards [hb'eq] with x hx
    rw [hx]
    exact sum_eq_sum_normalIdx _ fun i hi => by rw [hb'0 i hi]; simp
  choose b hb hbeq using hbex
  -- the normal coordinates in terms of the generators
  have hcex : ∀ l : NormalIdx n k, ∃ c : Fin (r + 1) → M → ℂ, (∀ q, HolomorphicAt n (c q) x₀) ∧
      ∀ᶠ x in 𝓝 x₀, flatCoord Φ l.1 x = ∑ q, c q x * genFun Ψ i (P q) x := fun l =>
    hgen _ (flatCoord_mem_vanishingIdeal Φ hflat' l.2 hx₀flat)
  choose c hc hceq using hcex
  have hbs : ∀ᶠ x in 𝓝 x₀, ∀ q, genFun Ψ i (P q) x = ∑ l, b q l x * flatCoord Φ l.1 x :=
    eventually_all.2 hbeq
  have hcs : ∀ᶠ x in 𝓝 x₀, ∀ l, flatCoord Φ l.1 x = ∑ q, c l q x * genFun Ψ i (P q) x :=
    eventually_all.2 hceq
  exact ⟨k, Φ, b, c, ⟨hx₀, hΦsrc, hΦ0, hflat', hb, hc, hbs, hcs,
    fun l l' => sum_coeff_mul_eq_delta hΦsrc hΦ0 (fun q l => (hb q l).continuousAt)
      (fun l q => (hc l q).continuousAt) hbs hcs l l'⟩⟩

/-- **Point data** at `p ∈ π⁻¹(x₀)`: coefficients `w` of the generators and `α` of the normal
coordinates along a local generator `h` of `𝓘_C 𝒪_Y`, with `w = b(π ·) α`. -/
theorem exists_pointData (hd : BlData n m Ψ C π P) {x₀ : M} {k : ℕ}
    {Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x₀ x₀)}
    {b : Fin (r + 1) → NormalIdx n k → M → ℂ} {c : NormalIdx n k → Fin (r + 1) → M → ℂ}
    (hF : FlatData Ψ C P x₀ k Φ b c) {p : Y} (hp : π p = x₀) :
    ∃ (U : Set Y) (h : Y → ℂ) (w : Y → Fin (r + 1) → ℂ) (α : Y → NormalIdx n k → ℂ),
      IsBlRep Ψ π P p (chartIndex (Ψ x₀)) U h w ∧
      MDifferentiableOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) h U ∧
      (∀ q, HolomorphicAt n (fun y => w y q) p) ∧ (∀ l, HolomorphicAt n (fun y => α y l) p) ∧
      α p ≠ 0 ∧ (∀ᶠ y in 𝓝 p, ∀ l, flatCoord Φ l.1 (π y) = h y * α y l) ∧
      (∀ᶠ y in 𝓝 p, ∀ q, w y q = ∑ l, b q l (π y) * α y l) := by
  classical
  subst hp
  set i := chartIndex (Ψ (π p))
  have hi : Ψ (π p) ∈ (affineChart i).source := mem_affineChart_chartIndex _
  obtain ⟨hgI, hgen⟩ := genFun_mem_and_generate hd hi
  obtain ⟨U, hU, hpU, h, hh, hnon, hiff⟩ := hd.blowup.2.2.2.1 p
  obtain ⟨w, hw, hweq, hw0⟩ := exists_coeff_of_generators hd.blowup hU hpU hh hnon hiff
    (g := fun q => genFun Ψ i (P q)) hgI hgen
  have hx₀flat : π p ∈ flatDomain Φ := mem_flatDomain_self Φ
  obtain ⟨α, hα, hαeq, hα0⟩ := exists_coeff_of_generators hd.blowup hU hpU hh hnon hiff
    (g := fun l : NormalIdx n k => flatCoord Φ l.1)
    (fun l => flatCoord_mem_vanishingIdeal Φ hF.flat l.2 hx₀flat)
    (fun a ha => by
      obtain ⟨b', hb'0, hb'h, hb'eq⟩ := exists_eq_sum_flatCoord Φ hF.src hF.flat hx₀flat ha
      refine ⟨fun l => b' l.1, fun l => hb'h l.1, ?_⟩
      filter_upwards [hb'eq] with x hx
      rw [hx]
      exact sum_eq_sum_normalIdx _ fun i hi => by rw [hb'0 i hi]; simp)
  have hwc : ∀ᶠ y in 𝓝 p, ContinuousAt w y := by
    filter_upwards [eventually_all.2 fun q => HolomorphicAt.eventually (hw q)] with y hy
    exact continuousAt_pi.mpr fun q => (hy q).continuousAt
  have hrep : IsBlRep Ψ π P p i U h w :=
    ⟨hi, hU, hpU, fun y hy => ((hh y hy).mdifferentiableAt (hU.mem_nhds hy)).continuousAt
      |>.continuousWithinAt, hnon, hwc, hweq, hw0⟩
  refine ⟨U, h, w, α, hrep, hh, hw, hα, hα0, hαeq, ?_⟩
  -- `w = b(π ·) α`: cancel `h`
  have hbπ : ∀ᶠ y in 𝓝 p, ∀ q, genFun Ψ i (P q) (π y) =
      ∑ l, b q l (π y) * flatCoord Φ l.1 (π y) :=
    hd.blowup.contMDiff.continuous.continuousAt.eventually hF.bsum
  have hπs : ∀ y, ContMDiffAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ π y :=
    fun y => hd.blowup.contMDiff y
  have hcont : ∀ q, ∀ᶠ y in 𝓝 p, ContinuousAt (fun y => w y q - ∑ l, b q l (π y) * α y l) y := by
    intro q
    have h1 : HolomorphicAt n (fun y => ∑ l, b q l (π y) * α y l) p :=
      HolomorphicAt.sum Finset.univ fun l _ =>
        HolomorphicAt.mul (HolomorphicAt.comp_contMDiff (hF.hb q l) (Eventually.of_forall hπs))
          (hα l)
    filter_upwards [HolomorphicAt.eventually (hw q), HolomorphicAt.eventually h1] with y hy1 hy2
    exact (HolomorphicAt.continuousAt hy1).sub (HolomorphicAt.continuousAt hy2)
  have hz : ∀ q, ∀ᶠ y in 𝓝 p, w y q - ∑ l, b q l (π y) * α y l = 0 := by
    intro q
    refine eventually_eq_zero_of_mul_eq_zero hU hpU hnon (hcont q) ?_
    filter_upwards [hweq, hbπ, hαeq] with y h1 h2 h3
    rw [mul_sub, ← h1 q, h2 q, Finset.mul_sum]
    rw [sub_eq_zero]
    exact Finset.sum_congr rfl fun l _ => by rw [h3 l]; ring
  filter_upwards [eventually_all.2 hz] with y hy q
  exact sub_eq_zero.mp (hy q)

/-- The local inverse of the `j`-th monomial chart built from `α`. -/
def monoInverse {k : ℕ} {x₀ : M}
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x₀ x₀))
    (π : Y → M) (α : Y → NormalIdx n k → ℂ) (j : NormalIdx n k) (y : Y) : ComplexModel n :=
  WithLp.toLp 2 fun i => if hi : k ≤ i.1 ∧ i ≠ j.1 then α y ⟨i, hi.1⟩ / α y j
    else flatCoord Φ i (π y)

/-- **The monomial chart inverse**: `σⱼ ∘ W = Φ ∘ e ∘ π` near `p`, `W` holomorphic, and the
lift `ℓⱼ` of the `j`-th monomial chart inverts `W`. -/
theorem exists_monomialInverse (hd : BlData n m Ψ C π P) {x₀ : M} {k : ℕ}
    {Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x₀ x₀)}
    {b : Fin (r + 1) → NormalIdx n k → M → ℂ} {c : NormalIdx n k → Fin (r + 1) → M → ℂ}
    (hF : FlatData Ψ C P x₀ k Φ b c) {p : Y} (hp : π p = x₀) {h : Y → ℂ}
    {α : Y → NormalIdx n k → ℂ} (hα : ∀ l, HolomorphicAt n (fun y => α y l) p)
    (hαeq : ∀ᶠ y in 𝓝 p, ∀ l, flatCoord Φ l.1 (π y) = h y * α y l) {j : NormalIdx n k}
    (hj : α p j ≠ 0) {ℓ : LiftedOpen.{u} (monomialDomain Φ k j.1) → Y}
    (hℓs : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ ℓ)
    (hℓπ : π ∘ ℓ = monomialChart Φ k j.1) :
    (∀ᶠ y in 𝓝 p, π y ∈ flatDomain Φ ∧
      monomial k j.1 (monoInverse Φ π α j y) = Φ.toFun (chartAt (ComplexModel n) x₀ (π y))) ∧
    (∀ i, HolomorphicAt n (fun y => monoInverse Φ π α j y i) p) ∧
    (∀ᶠ y in 𝓝 p, ∀ hw : monoInverse Φ π α j y ∈ monomialDomain Φ k j.1,
      ℓ (LiftedOpen.mk _ (monoInverse Φ π α j y) hw) = y) := by
  classical
  subst hp
  have hπs : ∀ y, ContMDiffAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ π y :=
    fun y => hd.blowup.contMDiff y
  have hflatp : π p ∈ flatDomain Φ := mem_flatDomain_self Φ
  have hflatev : ∀ᶠ y in 𝓝 p, π y ∈ flatDomain Φ :=
    hd.blowup.contMDiff.continuous.continuousAt.eventually ((isOpen_flatDomain Φ).mem_nhds hflatp)
  have hαjev : ∀ᶠ y in 𝓝 p, α y j ≠ 0 := (hα j).continuousAt.eventually_ne hj
  -- holomorphy of the coordinates of `W`, at every point of a neighbourhood
  have hWhol : ∀ y, π y ∈ flatDomain Φ → α y j ≠ 0 → (∀ l, HolomorphicAt n (fun y => α y l) y) →
      ∀ i, HolomorphicAt n (fun y => monoInverse Φ π α j y i) y := by
    intro y hy hyj hyα i
    by_cases hi : k ≤ i.1 ∧ i ≠ j.1
    · have : (fun y => monoInverse Φ π α j y i) = fun y => α y ⟨i, hi.1⟩ * (α y j)⁻¹ := by
        funext y
        show (if h : k ≤ i.1 ∧ i ≠ j.1 then α y ⟨i, h.1⟩ / α y j else flatCoord Φ i (π y)) = _
        rw [dif_pos hi, div_eq_mul_inv]
      rw [this]
      exact (hyα ⟨i, hi.1⟩).mul (HolomorphicAt.inv (hyα j) hyj)
    · have : (fun y => monoInverse Φ π α j y i) = fun y => flatCoord Φ i (π y) := by
        funext y
        show (if h : k ≤ i.1 ∧ i ≠ j.1 then α y ⟨i, h.1⟩ / α y j else flatCoord Φ i (π y)) = _
        rw [dif_neg hi]
      rw [this]
      exact (holomorphicAt_flatCoord Φ i hy).comp_contMDiff (Eventually.of_forall hπs)
  have hαev : ∀ᶠ y in 𝓝 p, ∀ l, HolomorphicAt n (fun y => α y l) y :=
    eventually_all.2 fun l => (hα l).eventually
  -- the key identity
  have hkey : ∀ y, π y ∈ flatDomain Φ → α y j ≠ 0 →
      (∀ l, flatCoord Φ l.1 (π y) = h y * α y l) →
      monomial k j.1 (monoInverse Φ π α j y) = Φ.toFun (chartAt (ComplexModel n) (π p) (π y)) := by
    intro y _ hyj hyeq
    ext i
    simp only [monomial_apply, monoInverse]
    by_cases hi : k ≤ i.1 ∧ i ≠ j.1
    · rw [if_pos hi, dif_pos hi, dif_neg (by simp)]
      have h1 := hyeq ⟨i, hi.1⟩
      have h2 := hyeq j
      change _ = flatCoord Φ i (π y)
      rw [h1, h2]
      field_simp
    · rw [if_neg hi, dif_neg hi]
      rfl
  -- the good neighbourhood
  set G : Set Y := {y | π y ∈ flatDomain Φ ∧ α y j ≠ 0 ∧
    (∀ l, flatCoord Φ l.1 (π y) = h y * α y l) ∧ ∀ l, HolomorphicAt n (fun y => α y l) y}
  have hG : G ∈ 𝓝 p := by
    filter_upwards [hflatev, hαjev, hαeq, hαev] with y h1 h2 h3 h4
    exact ⟨h1, h2, h3, h4⟩
  refine ⟨?_, hWhol p hflatp hj fun l => hα l, ?_⟩
  · filter_upwards [hG] with y hy
    exact ⟨hy.1, hkey y hy.1 hy.2.1 hy.2.2.1⟩
  · have hO : interior G ∈ 𝓝 p := interior_mem_nhds.mpr hG
    filter_upwards [hO] with y hy
    refine monomialLift_eq_of_monomial_eq hd.blowup hℓs hℓπ isOpen_interior
      (fun z hz => ?_) (fun z hz => ?_) y hy
    · have hz' : z ∈ G := interior_subset hz
      have hcm : ContMDiffAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, Fin n → ℂ) ∞
          (fun z => fun i => monoInverse Φ π α j z i) z :=
        contMDiffAt_pi_space.2 fun i =>
          contMDiffAt_of_eventually_mdifferentiableAt
            ((hWhol z hz'.1 hz'.2.1 hz'.2.2.2 i).mono fun _ h' => h')
      exact (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin n => ℂ)).symm.toContinuousLinearMap
        |>.contMDiff.contMDiffAt.comp z hcm
    · have hz' : z ∈ G := interior_subset hz
      exact ⟨hz'.1, hkey z hz'.1 hz'.2.1 hz'.2.2.1⟩

end SGPT.GAGA.ChowBl
