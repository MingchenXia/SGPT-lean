import SGPT.GAGA.SerreM1Grow
import SGPT.GAGA.PNBanach
import SGPT.GAGA.PNSchwartz
import SGPT.GAGA.PN2Laurent

/-!
# Serre's theorems on `ℙᴺ`, part 2: shells, homogeneous extension, `0`-cocycles

Infrastructure towards source `lma:GAGA` (`chapter_NApotential.tex`, lines 1143--1145) for
the finiteness of `Ȟ⁰(ℙᴺ, 𝓕)` (`SerreM1Banach`); blueprint `claude-serre-m34.tex`.

* `finiteDimensional_of_compact_decomposition`: the abstract form of the Cartan--Serre
  argument used here: a Banach space `E` with a surjection `Ψ : E → H`, a continuous linear
  `j : W → E` killed by `Ψ` and a compact operator `r : Z' → E` with `E = r(Z') + j(W)`; then
  `H` is finite-dimensional (Schwartz's theorem, `PNSchwartz`).
* The bounded open pieces `piece r t s = V_s(r) ∩ {1/t < ‖z‖ < t}` of the open cones
  `V_s(r) = openCover r s`; between two levels there is a compact set
  (`exists_isCompact_between`).
* `hext`: the homogeneous extension `z ↦ ‖z‖ⁿ f(z/‖z‖)` of a tuple `f` which is holomorphic and
  homogeneous on a piece; it is holomorphic and homogeneous on the whole cone `V_s(r)`, agrees
  with `f` on the piece, and carries membership in invariant coherent modules.
* `zeroCochain`, `zeroCocycle`, `exists_eq_zeroCocycle`: the `0`-cocycles of the Čech complex
  `coverSystem F n ρ` are exactly the families of sections `g_i` of `M(n)` over `K_i(ρ)` with
  `g_k - g_i` a section of `N(n)` over `K_i(ρ) ∩ K_k(ρ)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Set Filter Topology Metric
open SGPT.Foundations.Analysis.Pending.OkaRelationSheaf
open SGPT.GAGA.Core
open scoped BoundedContinuousFunction

noncomputable section

namespace SGPT.GAGA.PN

/-! ### The abstract finiteness lemma -/

/-- **Finiteness from a compact decomposition** (Cartan--Serre). Let `E`, `W`, `Z'` be Banach
spaces, `r : Z' → E` a compact operator, `j : W → E` continuous linear with
`E = r(Z') + j(W)`, and `Ψ : E → H` a linear surjection with `Ψ ∘ j = 0`. Then `H` is
finite-dimensional. -/
theorem finiteDimensional_of_compact_decomposition {E W Z' H : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] [NormedAddCommGroup W] [NormedSpace ℂ W]
    [CompleteSpace W] [NormedAddCommGroup Z'] [NormedSpace ℂ Z'] [CompleteSpace Z']
    [AddCommGroup H] [Module ℂ H] (Ψ : E →ₗ[ℂ] H) (hΨ : Function.Surjective Ψ)
    (j : W →L[ℂ] E) (hj : ∀ w, Ψ (j w) = 0) (r : Z' →L[ℂ] E) (hr : IsCompactOperator r)
    (hdec : ∀ e, ∃ z w, e = r z + j w) : FiniteDimensional ℂ H := by
  have hsup : LinearMap.range r.toLinearMap ⊔ LinearMap.range j.toLinearMap = ⊤ := by
    refine eq_top_iff.2 fun e _ => ?_
    obtain ⟨z, w, rfl⟩ := hdec e
    exact Submodule.add_mem_sup ⟨z, rfl⟩ ⟨w, rfl⟩
  have hfin := finiteDimensional_quotient_range_of_compact (𝕜 := ℂ) hr hsup
  have hle : LinearMap.range j.toLinearMap ≤ LinearMap.ker Ψ := by
    rintro _ ⟨w, rfl⟩
    exact hj w
  refine Module.Finite.of_surjective ((LinearMap.range j.toLinearMap).liftQ Ψ hle) ?_
  intro h
  obtain ⟨e, rfl⟩ := hΨ h
  exact ⟨Submodule.Quotient.mk e, rfl⟩

variable {N : ℕ}

/-! ### Shells and pieces -/

/-- The open shell `{1/t < ‖z‖ < t}`. -/
def shell (t : ℝ) : Set (ConeSpace N) :=
  {z | t⁻¹ < ‖z‖ ∧ ‖z‖ < t}

/-- The bounded open piece `V_s(r) ∩ shell(t)` of the open cone `V_s(r)`. -/
def piece (r t : ℝ) (s : Finset (Fin (N + 1))) : Set (ConeSpace N) :=
  openCover r s ∩ shell t

theorem isOpen_shell (t : ℝ) : IsOpen (shell (N := N) t) :=
  (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)

theorem isOpen_piece (r t : ℝ) (s : Finset (Fin (N + 1))) : IsOpen (piece r t s) :=
  (isOpen_openCover r s).inter (isOpen_shell t)

theorem piece_subset_puncture (r t : ℝ) (s : Finset (Fin (N + 1))) :
    piece r t s ⊆ puncture (ConeSpace N) :=
  fun _ hz => openCover_subset_ne r s hz.1

theorem piece_anti {r r' t t' : ℝ} (hr : r ≤ r') (ht : t ≤ t') (ht1 : 0 < t)
    {s s' : Finset (Fin (N + 1))} (hs : s ⊆ s') : piece r t s' ⊆ piece r' t' s := by
  rintro z ⟨hz, h1, h2⟩
  refine ⟨openCover_anti hr hs hz, lt_of_le_of_lt ?_ h1, h2.trans_le ht⟩
  exact inv_anti₀ ht1 ht

/-- A unit vector of `V_s(r)` lies in the piece of every shell `t > 1`. -/
theorem mem_piece_of_norm_eq_one {r t : ℝ} (ht : 1 < t) {s : Finset (Fin (N + 1))}
    {z : ConeSpace N} (hz : z ∈ openCover r s) (h1 : ‖z‖ = 1) : z ∈ piece r t s :=
  ⟨hz, by rw [h1]; exact inv_lt_one_of_one_lt₀ ht, by rw [h1]; exact ht⟩

/-- The normalized vector `z / ‖z‖`. -/
theorem norm_normalize {z : ConeSpace N} (hz : z ≠ 0) : ‖((‖z‖ : ℂ))⁻¹ • z‖ = 1 := by
  rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _),
    inv_mul_cancel₀ (norm_ne_zero_iff.2 hz)]

theorem normalize_mem_piece {r t : ℝ} (ht : 1 < t) {s : Finset (Fin (N + 1))}
    {z : ConeSpace N} (hz : z ∈ openCover r s) :
    ((‖z‖ : ℂ))⁻¹ • z ∈ piece r t s := by
  have hz0 : z ≠ 0 := openCover_subset_ne r s hz
  refine mem_piece_of_norm_eq_one ht ?_ (norm_normalize hz0)
  exact isCone_openCover r s _ (inv_ne_zero (Complex.ofReal_ne_zero.2 (norm_ne_zero_iff.2 hz0)))
    z hz

/-- **A compact set between two levels**: for `r < r'` and `1 < t < t'`, the closure of
`piece r t s` is compact and contained in `piece r' t' s`. -/
theorem exists_isCompact_between {r r' t t' : ℝ} (hr : r < r') (ht : 1 < t) (htt : t < t')
    (s : Finset (Fin (N + 1))) :
    ∃ K : Set (ConeSpace N), IsCompact K ∧ piece r t s ⊆ K ∧ K ⊆ piece r' t' s := by
  set K : Set (ConeSpace N) :=
    {z | ∀ i ∈ s, ∀ j, ‖z j‖ ≤ r * ‖z i‖} ∩ {z | t⁻¹ ≤ ‖z‖ ∧ ‖z‖ ≤ t} with hKdef
  have ht0 : 0 < t := by linarith
  refine ⟨K, ?_, ?_, ?_⟩
  · refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
    · refine IsClosed.inter ?_ ((isClosed_le continuous_const continuous_norm).inter
        (isClosed_le continuous_norm continuous_const))
      simp only [ofPred_forall]
      exact isClosed_iInter fun i => isClosed_iInter fun _ => isClosed_iInter fun j =>
        isClosed_le (by fun_prop) (by fun_prop)
    · refine (Metric.isBounded_closedBall (x := (0 : ConeSpace N)) (r := t)).subset ?_
      intro z hz
      exact mem_closedBall_zero_iff.2 hz.2.2
  · rintro z ⟨hz, h1, h2⟩
    exact ⟨fun i hi j => (hz.2 i hi j).le, h1.le, h2.le⟩
  · rintro z ⟨hz, h1, h2⟩
    have hz0 : z ≠ 0 := by
      intro h
      rw [h, norm_zero] at h1
      exact absurd h1 (not_le.2 (inv_pos.2 ht0))
    refine ⟨⟨hz0, fun i hi j => ?_⟩, lt_of_lt_of_le (inv_strictAnti₀ ht0 htt) h1,
      h2.trans_lt htt⟩
    have hzi : z i ≠ 0 := by
      intro h0
      apply hz0
      ext j
      have := hz i hi j
      rw [h0, norm_zero, mul_zero] at this
      simpa using norm_le_zero_iff.1 this
    exact (hz i hi j).trans_lt (mul_lt_mul_of_pos_right hr (norm_pos_iff.2 hzi))

/-! ### The homogeneous extension -/

section Hext

variable {τ : Type} [Fintype τ]

/-- `f` is homogeneous of degree `n` on `S`, as far as `S` allows. -/
def IsHomShell (f : τ → ConeSpace N → ℂ) (S : Set (ConeSpace N)) (n : ℤ) : Prop :=
  ∀ z ∈ S, ∀ c : ℂ, c • z ∈ S → ∀ j, f j (c • z) = c ^ n * f j z

/-- The homogeneous extension `z ↦ ‖z‖ⁿ f(z/‖z‖)`. -/
def hext (n : ℤ) (f : τ → ConeSpace N → ℂ) : τ → ConeSpace N → ℂ :=
  fun j z => ((‖z‖ : ℂ)) ^ n * f j (((‖z‖ : ℂ))⁻¹ • z)

variable {r t : ℝ} {s : Finset (Fin (N + 1))} {n : ℤ} {f : τ → ConeSpace N → ℂ}

theorem norm_ofReal_ne_zero {z : ConeSpace N} (hz : z ≠ 0) : ((‖z‖ : ℂ)) ≠ 0 :=
  Complex.ofReal_ne_zero.2 (norm_ne_zero_iff.2 hz)

/-- On the piece, the extension is `f`. -/
theorem hext_eq (ht : 1 < t) (hf : IsHomShell f (piece r t s) n) {z : ConeSpace N}
    (hz : z ∈ piece r t s) (j : τ) : hext n f j z = f j z := by
  have hz0 : z ≠ 0 := piece_subset_puncture r t s hz
  have hn := norm_ofReal_ne_zero hz0
  have h := hf z hz _ (normalize_mem_piece ht hz.1) j
  simp only [hext, h, inv_zpow', ← mul_assoc]
  rw [← zpow_add₀ hn, add_neg_cancel, zpow_zero, one_mul]

/-- A function homogeneous on an open cone `U ⊇ V_s(r)` is its own extension. -/
theorem hext_eq_of_isHomOn {U : Set (ConeSpace N)} {a : τ → ConeSpace N → ℂ}
    (ha : IsHomOn U n a) {z : ConeSpace N} (hz : z ∈ U) (j : τ) : hext n a j z = a j z := by
  have hz0 : z ≠ 0 := ha.subset hz
  have hn := norm_ofReal_ne_zero hz0
  have h := ha.hom (((‖z‖ : ℂ))⁻¹ • z) (ha.isCone _ (inv_ne_zero hn) z hz) _ hn j
  rw [smul_inv_smul₀ hn] at h
  exact h.symm

/-- Near a point `z₀` of the cone, the extension is `‖z₀‖ⁿ f(z/‖z₀‖)`. -/
theorem hext_eventuallyEq (ht : 1 < t) (hf : IsHomShell f (piece r t s) n) {z₀ : ConeSpace N}
    (hz₀ : z₀ ∈ openCover r s) :
    ∀ᶠ z in 𝓝 z₀, ∀ j, hext n f j z = ((‖z₀‖ : ℂ)) ^ n * f j (((‖z₀‖ : ℂ))⁻¹ • z) := by
  have hz₀0 : z₀ ≠ 0 := openCover_subset_ne r s hz₀
  have hn₀ := norm_ofReal_ne_zero hz₀0
  have hcont : Continuous fun z : ConeSpace N => ((‖z₀‖ : ℂ))⁻¹ • z := continuous_const_smul _
  have h1 : ∀ᶠ z in 𝓝 z₀, ((‖z₀‖ : ℂ))⁻¹ • z ∈ piece r t s :=
    hcont.continuousAt.eventually_mem ((isOpen_piece r t s).mem_nhds (normalize_mem_piece ht hz₀))
  filter_upwards [h1, (isOpen_openCover r s).mem_nhds hz₀] with z hz1 hz2 j
  have hz0 : z ≠ 0 := openCover_subset_ne r s hz2
  have hn := norm_ofReal_ne_zero hz0
  have hc : (((‖z₀‖ : ℂ)) / ((‖z‖ : ℂ))) • (((‖z₀‖ : ℂ))⁻¹ • z) = ((‖z‖ : ℂ))⁻¹ • z := by
    rw [smul_smul]
    congr 1
    field_simp
  have h := hf _ hz1 _ (hc ▸ normalize_mem_piece ht hz2) j
  rw [hc] at h
  simp only [hext, h, div_zpow, ← mul_assoc]
  field_simp

theorem isHomOn_hext (ht : 1 < t) (hf : IsHomShell f (piece r t s) n)
    (hfd : ∀ j, DifferentiableOn ℂ (f j) (piece r t s)) :
    IsHomOn (openCover r s) n (hext n f) := by
  refine ⟨isOpen_openCover r s, isCone_openCover r s, openCover_subset_ne r s,
    fun j z hz => ?_, fun z hz c hc j => ?_⟩
  · have hz0 : z ≠ 0 := openCover_subset_ne r s hz
    have hn := norm_ofReal_ne_zero hz0
    have hd : DifferentiableAt ℂ (fun w => ((‖z‖ : ℂ)) ^ n * f j (((‖z‖ : ℂ))⁻¹ • w)) z := by
      refine (differentiableAt_const _).mul ?_
      exact ((hfd j).differentiableAt ((isOpen_piece r t s).mem_nhds
        (normalize_mem_piece ht hz))).comp z
        (by fun_prop : DifferentiableAt ℂ (fun w : ConeSpace N => ((‖z‖ : ℂ))⁻¹ • w) z)
    refine (hd.congr_of_eventuallyEq ?_).differentiableWithinAt
    filter_upwards [hext_eventuallyEq ht hf hz] with w hw
    exact hw j
  · have hz0 : z ≠ 0 := openCover_subset_ne r s hz
    have hcz : c • z ∈ openCover r s := isCone_openCover r s c hc z hz
    have hn := norm_ofReal_ne_zero hz0
    have hnc := norm_ofReal_ne_zero (smul_ne_zero hc hz0)
    set u : ℂ := c / ((‖c‖ : ℂ)) with hudef
    have hc0 : ((‖c‖ : ℂ)) ≠ 0 := Complex.ofReal_ne_zero.2 (norm_ne_zero_iff.2 hc)
    have hnorm : ((‖c • z‖ : ℂ)) = ((‖c‖ : ℂ)) * ((‖z‖ : ℂ)) := by
      rw [norm_smul, Complex.ofReal_mul]
    have hrot : ((‖c • z‖ : ℂ))⁻¹ • (c • z) = u • (((‖z‖ : ℂ))⁻¹ • z) := by
      rw [smul_smul, smul_smul, hnorm, hudef]
      congr 1
      field_simp
    have h := hf _ (normalize_mem_piece ht hz) u (hrot ▸ normalize_mem_piece ht hcz) j
    simp only [hext]
    rw [hrot, h, hnorm, hudef, div_zpow, mul_zpow]
    field_simp

/-- **Membership in an invariant coherent module extends along the cone.** If `f ∈ P` at every
point of the piece of `V_s(r')` (`r' ≤ r`, `t' > 1`), then `hext n f ∈ P` at every point of
`V_s(r')`. -/
theorem mem_hext {P : GermModule (ConeSpace N) τ} (hP : P.IsCoherentOn (puncture (ConeSpace N)))
    (hPi : IsConeInvariant P) (ht : 1 < t) (hf : IsHomShell f (piece r t s) n) {r' t' : ℝ}
    (hr : r' ≤ r) (ht' : 1 < t') (hmem : ∀ y ∈ piece r' t' s, P.mem y f) {y : ConeSpace N}
    (hy : y ∈ openCover r' s) : P.mem y (hext n f) := by
  have hy0 : y ≠ 0 := openCover_subset_ne r' s hy
  have hn := norm_ofReal_ne_zero hy0
  have hw := hmem _ (normalize_mem_piece ht' hy)
  have h1 := (hPi _ (smul_ne_zero (inv_ne_zero hn) hy0) ((‖y‖ : ℂ)) hn f).1 hw
  rw [smul_inv_smul₀ hn] at h1
  have h2 := (hP y hy0).smul_mem (holAt_const (((‖y‖ : ℂ)) ^ n) y) h1
  have hyr : y ∈ openCover r s := openCover_anti hr (subset_refl s) hy
  refine (hP y hy0).congr_mem h2 fun j => ?_
  filter_upwards [hext_eventuallyEq ht hf hyr] with z hz
  exact (hz j).symm

end Hext

/-! ### `0`-cocycles of the cover `K(ρ)` -/

section ZeroCocycles

variable {k : Type*} [Ring k] {I : Type} [LinearOrder I]

/-- Converse of `cechCocycle_zero_res`: a `0`-cochain whose components agree on overlaps is a
cocycle. -/
theorem cechD_eq_zero_of_res_eq (Γ : CechSystem k I) {c : ∀ s, Γ.obj s}
    (hc : c ∈ cechCochain Γ 0)
    (h : ∀ i k : I, i ≠ k →
      Γ.res (Finset.singleton_subset_iff.2 (Finset.mem_insert_self i {k})) (c {i}) =
        Γ.res (Finset.singleton_subset_iff.2 (Finset.mem_insert_of_mem
          (Finset.mem_singleton_self k))) (c {k})) : cechD Γ c = 0 := by
  funext t
  by_cases ht : t.card = 2
  · obtain ⟨i, k, hik, rfl⟩ := Finset.card_eq_two.1 ht
    rw [cechD_apply, Finset.sum_pair hik]
    have he1 : ({i, k} : Finset I).erase i = {k} := by
      rw [Finset.erase_insert (Finset.notMem_singleton.2 hik)]
    have he2 : ({i, k} : Finset I).erase k = {i} := by
      rw [Finset.erase_insert_of_ne hik, Finset.erase_singleton, insert_empty_eq]
    rw [Γ.res_congr he1 (Finset.erase_subset i _)
        (Finset.singleton_subset_iff.2 (Finset.mem_insert_of_mem (Finset.mem_singleton_self k))),
      Γ.res_congr he2 (Finset.erase_subset k _)
        (Finset.singleton_subset_iff.2 (Finset.mem_insert_self i {k})), h i k hik, ← add_smul]
    have hs : cechSign {i, k} i + cechSign {i, k} k = 0 := by
      rw [← Finset.sum_pair hik]
      exact sum_cechSign_of_card_two (Finset.card_pair hik)
    rw [hs, zero_smul]
    rfl
  · exact cechD_mem Γ hc t ht

end ZeroCocycles

section Cover

variable {F : Subquotient (ConeSpace N) (puncture (ConeSpace N))} {n : ℤ} {ρ : ℝ}

theorem IsHomSection.neg_sub {P : GermModule (ConeSpace N) F.ι}
    (hP : P.IsCoherentOn {z | z ≠ 0}) {K : Set (ConeSpace N)} {a b : F.ι → ConeSpace N → ℂ}
    (h : IsHomSection P n K (a - b)) : IsHomSection P n K (b - a) := by
  convert h.smul hP (-1) using 1
  funext j z
  simp

/-- The `0`-cochain of `coverSystem F n ρ` with components the classes of the `g i`. -/
def zeroCochain (g : Fin (N + 1) → F.ι → ConeSpace N → ℂ)
    (hg : ∀ i, IsHomSection F.M n (coverSet ρ {i}) (g i)) :
    ∀ s, (coverSystem F n ρ).obj s := fun s =>
  if h : s.card = 1 then
    show (coverSystem F n ρ).obj s from
    sectionMk F ⟨g (s.min' (Finset.card_pos.1 (by omega))), mem_homSections.2 ((hg _).mono
      (coverSet_anti ρ (Finset.singleton_subset_iff.2 (Finset.min'_mem _ _))))⟩
  else 0

theorem zeroCochain_singleton (g : Fin (N + 1) → F.ι → ConeSpace N → ℂ)
    (hg : ∀ i, IsHomSection F.M n (coverSet ρ {i}) (g i)) (i : Fin (N + 1)) :
    zeroCochain g hg {i} = sectionMk F ⟨g i, hg i⟩ := by
  unfold zeroCochain
  split_ifs with h
  · simp only [Finset.min'_singleton]
    rfl
  · exact absurd (Finset.card_singleton i) h

theorem zeroCochain_mem (g : Fin (N + 1) → F.ι → ConeSpace N → ℂ)
    (hg : ∀ i, IsHomSection F.M n (coverSet ρ {i}) (g i)) :
    zeroCochain g hg ∈ cechCochain (coverSystem F n ρ) 0 := fun s hs => by
  unfold zeroCochain
  split_ifs with h
  · exact absurd h (by simpa using hs)
  · rfl

/-- The `0`-cocycle of `coverSystem F n ρ` given by sections `g i` of `M(n)` over `K_i(ρ)` with
`g k - g i` a section of `N(n)` over `K_i(ρ) ∩ K_k(ρ)`. -/
def zeroCocycle (g : Fin (N + 1) → F.ι → ConeSpace N → ℂ)
    (hg : ∀ i, IsHomSection F.M n (coverSet ρ {i}) (g i))
    (hcoc : ∀ i k, IsHomSection F.N n (coverSet ρ {i, k}) (g k - g i)) :
    LinearMap.ker (cechDq (coverSystem F n ρ) 0) :=
  ⟨⟨zeroCochain g hg, zeroCochain_mem g hg⟩, by
    rw [LinearMap.mem_ker]
    refine Subtype.ext (cechD_eq_zero_of_res_eq _ (c := zeroCochain g hg) (zeroCochain_mem g hg)
      fun i k _ => ?_)
    rw [zeroCochain_singleton, zeroCochain_singleton]
    exact (sectionMk_eq_iff F _ _).2 ((hcoc i k).neg_sub F.coherent_N)⟩

@[simp] theorem zeroCocycle_singleton (g : Fin (N + 1) → F.ι → ConeSpace N → ℂ)
    (hg : ∀ i, IsHomSection F.M n (coverSet ρ {i}) (g i))
    (hcoc : ∀ i k, IsHomSection F.N n (coverSet ρ {i, k}) (g k - g i)) (i : Fin (N + 1)) :
    (zeroCocycle g hg hcoc).1.1 {i} = sectionMk F ⟨g i, hg i⟩ :=
  zeroCochain_singleton g hg i

/-- Two `0`-cocycles agree if their components agree modulo `N`. -/
theorem zeroCocycle_eq {g g' : Fin (N + 1) → F.ι → ConeSpace N → ℂ}
    {hg : ∀ i, IsHomSection F.M n (coverSet ρ {i}) (g i)}
    {hcoc : ∀ i k, IsHomSection F.N n (coverSet ρ {i, k}) (g k - g i)}
    {hg' : ∀ i, IsHomSection F.M n (coverSet ρ {i}) (g' i)}
    {hcoc' : ∀ i k, IsHomSection F.N n (coverSet ρ {i, k}) (g' k - g' i)}
    (h : ∀ i, IsHomSection F.N n (coverSet ρ {i}) (g i - g' i)) :
    zeroCocycle g hg hcoc = zeroCocycle g' hg' hcoc' := by
  refine Subtype.ext (Subtype.ext (funext fun s => ?_))
  by_cases hs : s.card = 1
  · obtain ⟨i, rfl⟩ := Finset.card_eq_one.1 hs
    change zeroCochain g hg {i} = zeroCochain g' hg' {i}
    rw [zeroCochain_singleton, zeroCochain_singleton]
    exact (sectionMk_eq_iff F _ _).2 (h i)
  · change zeroCochain g hg s = zeroCochain g' hg' s
    unfold zeroCochain
    split_ifs
    rfl

/-- **Every `0`-cocycle is a `zeroCocycle`.** -/
theorem exists_eq_zeroCocycle (z : LinearMap.ker (cechDq (coverSystem F n ρ) 0)) :
    ∃ (g : Fin (N + 1) → F.ι → ConeSpace N → ℂ)
      (hg : ∀ i, IsHomSection F.M n (coverSet ρ {i}) (g i))
      (hcoc : ∀ i k, IsHomSection F.N n (coverSet ρ {i, k}) (g k - g i)),
      zeroCocycle g hg hcoc = z := by
  classical
  have hrep : ∀ i : Fin (N + 1), ∃ a : secM F n (coverSet ρ {i}) (coverSet_subset ρ {i}),
      sectionMk F a = z.1.1 {i} := fun i => Submodule.Quotient.mk_surjective _ _
  choose a ha using hrep
  have hz : cechDq (coverSystem F n ρ) 0 z.1 = 0 := LinearMap.mem_ker.1 z.2
  have hcoc : ∀ i k, IsHomSection F.N n (coverSet ρ {i, k}) ((a k).1 - (a i).1) := by
    intro i k
    by_cases hik : i = k
    · subst hik
      rw [sub_self]
      exact isHomSection_zero F.coherent_N n (coverSet_subset ρ _)
    · have h := cechCocycle_zero_res (coverSystem F n ρ) hz hik
      rw [← ha i, ← ha k] at h
      exact ((sectionMk_eq_iff F _ _).1 h).neg_sub F.coherent_N
  refine ⟨fun i => (a i).1, fun i => mem_homSections.1 (a i).2, hcoc, Subtype.ext (Subtype.ext (funext fun s => ?_))⟩
  by_cases hs : s.card = 1
  · obtain ⟨i, rfl⟩ := Finset.card_eq_one.1 hs
    change zeroCochain (fun i => (a i).1) (fun i => mem_homSections.1 (a i).2) {i} = z.1.1 {i}
    rw [zeroCochain_singleton, ← ha i]
  · change zeroCochain (fun i => (a i).1) (fun i => mem_homSections.1 (a i).2) s = z.1.1 s
    rw [z.1.2 s hs]
    unfold zeroCochain
    split_ifs
    rfl

end Cover

end SGPT.GAGA.PN
