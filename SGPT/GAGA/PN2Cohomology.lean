import SGPT.GAGA.PN2Laurent
import SGPT.GAGA.PNStructureSheaf

/-!
# `Ȟ^q(ℙᴺ, 𝒪(n)^ι)` for the cover `(K_i)` by Laurent series

Infrastructure of lane SERRE-PN2 (Serre's GAGA on `ℙᴺ`, towards source `lma:GAGA`,
`chapter_NApotential.tex` lines 1143--1145), plan node PN6 of `claude-serre-pn.tex`.

Let `ρ ≥ 1` and let `Γ = coverSystem (𝒪^ι) n ρ` be the Čech coefficient system
`s ↦ Γ(K_s, 𝒪^ι(n))` of the closed cover `K_i = {|z_j| ≤ ρ |z_i|}` of `ℙᴺ`.

* `secCoeff`: the `α`-th Laurent coefficient (on the unit torus `|z_k| = 1`, which lies in every
  `K_s`) of the `j`-th component of a section, a linear form on `Γ(K_s)` commuting with the
  restrictions (`secCoeff_res`). By `laurent_of_homogeneous`, it vanishes unless
  `∑ α = n` and `α_k ≥ 0` for `k ∉ s` (`secCoeff_ne_zero`).
* `exists_cechD_eq_free` (**the contracting homotopy**): a `(q+1)`-cocycle `z` whose
  coefficients at the multi-indices with all `α_k < 0` vanish is a coboundary. For a multi-index
  `α` let `k(α)` be the least `k` with `α_k ≥ 0`; the `q`-cochain
  `b_s = ∑_{k ∉ s} ε(k, s ∪ k) · (the part of z_{s ∪ k} with k(α) = k)` is again a family of
  sections: the monomials of the part of `z_{s ∪ k}` with `α_k ≥ 0` converge on a neighbourhood
  of `K_s` (`IsLaurent.extend`). Coefficientwise, `d b = z` by the cocycle identity and
  `ε(j, t) ε(k, (t ∖ j) ∪ k) = -ε(k, t ∪ k) ε(j, t ∪ k)`; the two sides are holomorphic and
  have the same Laurent expansion, so they agree near `K_t` (density of the points with nonzero
  coordinates).
* `cechH_free_subsingleton`: **`Ȟ^q(ℙᴺ, 𝒪(n)^ι) = 0` for `q ≥ 1`, except possibly for `q = N`
  and `n ≤ -N-1`**; i.e. `Ȟ^q = 0` for `0 < q < N` and all `n`, and `Ȟ^N = 0` for `n ≥ -N`.
  No Theorem B is used.
* `finiteDimensional_cechH_free`: `Ȟ^q(ℙᴺ, 𝒪(n)^ι)` is finite-dimensional for all `q ≥ 1`
  and all `n` (`Ȟ^N` is detected by the finitely many coefficients with all `α_k ≤ -1`,
  `∑ α = n`).

Blueprint: `claude-serre-pn2.tex`, nodes `claude-serre-pn2:coefficients`,
`claude-serre-pn2:homotopy`, `claude-serre-pn2:vanishing`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Set Filter Topology Metric Complex MeasureTheory UnitAddTorus
open SGPT.Foundations.Analysis.Pending.OkaRelationSheaf
open SGPT.GAGA.Core

noncomputable section

namespace SGPT.GAGA.PN

/-! ### Linearity of torus coefficients -/

section TorusLinear

variable {d : ℕ}

theorem tcoeff_add' {f g : EuclideanSpace ℂ (Fin d) → ℂ} {w : EuclideanSpace ℂ (Fin d)}
    (hf : Continuous fun x => f (tpt w x)) (hg : Continuous fun x => g (tpt w x))
    (α : Fin d → ℤ) : tcoeff (f + g) w α = tcoeff f w α + tcoeff g w α := by
  simp only [tcoeff_eq, Pi.add_apply, smul_add]
  exact integral_add
    (((mFourier (-α)).continuous.smul hf).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))
    (((mFourier (-α)).continuous.smul hg).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))

theorem tcoeff_const_smul (a : ℂ) (f : EuclideanSpace ℂ (Fin d) → ℂ)
    (w : EuclideanSpace ℂ (Fin d)) (α : Fin d → ℤ) : tcoeff (a • f) w α = a * tcoeff f w α := by
  simp only [tcoeff_eq, Pi.smul_apply, smul_eq_mul]
  rw [← integral_const_mul]
  congr 1
  funext x
  ring

theorem tcoeff_eq_zero_of_eq_zero {f : EuclideanSpace ℂ (Fin d) → ℂ}
    {w : EuclideanSpace ℂ (Fin d)} (hf : ∀ x, f (tpt w x) = 0) (α : Fin d → ℤ) :
    tcoeff f w α = 0 := by
  simp [tcoeff_eq, hf]

end TorusLinear

/-! ### Signs -/

section Signs

variable {I : Type} [LinearOrder I]

theorem cechSign_mul_self (t : Finset I) (j : I) : cechSign t j * cechSign t j = 1 := by
  unfold cechSign
  rw [← pow_add, ← two_mul, pow_mul]
  simp

/-- The sign identity of the contracting homotopy. -/
theorem cechSign_homotopy {u : Finset I} {j k : I} (hj : j ∈ u) (hk : k ∈ u) (hne : j ≠ k) :
    cechSign (u.erase k) j * cechSign (u.erase j) k = -(cechSign u k * cechSign u j) := by
  have h := cechSign_mul_swap hk hj hne.symm
  have hA := cechSign_mul_self u k
  have hD := cechSign_mul_self (u.erase j) k
  linear_combination (cechSign u k * cechSign (u.erase j) k) * h
    - (cechSign (u.erase k) j * cechSign (u.erase j) k) * hA
    - (cechSign u k * cechSign u j) * hD

end Signs

/-! ### Coefficients of sections of `𝒪^ι(n)` -/

variable {N : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The unit torus `|z_k| = 1` lies in every `K_s` (`ρ ≥ 1`). -/
theorem tpt_one_mem_coverSet {ρ : ℝ} (hρ : 1 ≤ ρ) (s : Finset (Fin (N + 1)))
    (x : UnitAddTorus (Fin (N + 1))) : tpt (rpt fun _ => 1) x ∈ coverSet ρ s := by
  refine ⟨fun h0 => ?_, fun i _ j => ?_⟩
  · have := congrArg (fun z : ConeSpace N => ‖z 0‖) h0
    simp only [norm_tpt_apply, rpt_apply, Complex.ofReal_one, norm_one] at this
    simp at this
  · rw [norm_tpt_apply, norm_tpt_apply]
    simpa using hρ

theorem continuous_section_torus {ρ : ℝ} (hρ : 1 ≤ ρ) {s : Finset (Fin (N + 1))}
    {P : GermModule (ConeSpace N) ι} {n : ℤ} {a : ι → ConeSpace N → ℂ}
    (ha : IsHomSection P n (coverSet ρ s) a) (j : ι) :
    Continuous fun x => a j (tpt (rpt fun _ => 1) x) := by
  obtain ⟨U, hKU, hU, -⟩ := ha
  exact (hU.diff j).continuousOn.comp_continuous (continuous_tpt_right _) fun x =>
    hKU (tpt_one_mem_coverSet hρ s x)

/-- The `α`-th Laurent coefficient of the `j`-th component, on sections of the numerator. -/
def secCoeffM {ρ : ℝ} (hρ : 1 ≤ ρ) (n : ℤ) (s : Finset (Fin (N + 1))) (α : Fin (N + 1) → ℤ)
    (j : ι) :
    secM (freeSubquotient (ConeSpace N) ι) n (coverSet ρ s) (coverSet_subset ρ s) →ₗ[ℂ] ℂ where
  toFun a := lcoeff (a.1 j) α
  map_add' a b := by
    simp only [lcoeff_eq_tcoeff]
    exact tcoeff_add' (continuous_section_torus hρ a.2 j) (continuous_section_torus hρ b.2 j) α
  map_smul' r a := by
    simp only [lcoeff_eq_tcoeff, RingHom.id_apply, smul_eq_mul]
    exact tcoeff_const_smul r (a.1 j) _ α

/-- **The Laurent coefficients of sections**: the `α`-th Laurent coefficient (on the unit
torus) of the `j`-th component, a linear form on `Γ(K_s, 𝒪^ι(n))`. -/
def secCoeff {ρ : ℝ} (hρ : 1 ≤ ρ) (n : ℤ) (s : Finset (Fin (N + 1))) (α : Fin (N + 1) → ℤ)
    (j : ι) : (coverSystem (freeSubquotient (ConeSpace N) ι) n ρ).obj s →ₗ[ℂ] ℂ :=
  Submodule.liftQ _ (secCoeffM hρ n s α j) fun a ha => by
    rw [LinearMap.mem_ker]
    obtain ⟨U, hKU, -, hU0⟩ := (show IsHomSection (GermModule.bot (ConeSpace N) ι) n
      (coverSet ρ s) a.1 from ha)
    show lcoeff (a.1 j) α = 0
    rw [lcoeff_eq_tcoeff]
    exact tcoeff_eq_zero_of_eq_zero (fun x =>
      (hU0 _ (hKU (tpt_one_mem_coverSet hρ s x)) j).eq_of_nhds) α

theorem secCoeff_mk {ρ : ℝ} (hρ : 1 ≤ ρ) (n : ℤ) (s : Finset (Fin (N + 1)))
    (α : Fin (N + 1) → ℤ) (j : ι)
    (a : secM (freeSubquotient (ConeSpace N) ι) n (coverSet ρ s) (coverSet_subset ρ s)) :
    secCoeff hρ n s α j (sectionMk _ a) = lcoeff (a.1 j) α :=
  rfl

theorem secCoeff_res {ρ : ℝ} (hρ : 1 ≤ ρ) (n : ℤ) {s t : Finset (Fin (N + 1))} (h : s ⊆ t)
    (α : Fin (N + 1) → ℤ) (j : ι) (x : (coverSystem (freeSubquotient (ConeSpace N) ι) n ρ).obj s) :
    secCoeff hρ n t α j ((coverSystem (freeSubquotient (ConeSpace N) ι) n ρ).res h x) =
      secCoeff hρ n s α j x := by
  induction x using Submodule.Quotient.induction_on with
  | _ a => rfl

theorem isHomOn_openCover_of_subset {U : Set (ConeSpace N)} {n : ℤ} {a : ι → ConeSpace N → ℂ}
    (ha : IsHomOn U n a) {ρ : ℝ} {s : Finset (Fin (N + 1))} (h : openCover ρ s ⊆ U) :
    IsHomOn (openCover ρ s) n a :=
  ⟨isOpen_openCover ρ s, isCone_openCover ρ s, openCover_subset_ne ρ s,
    fun j => (ha.diff j).mono h, fun z hz => ha.hom z (h hz)⟩

/-- The Laurent expansion of the components of a homogeneous tuple on `V_s(ρ)`. -/
theorem laurent_tuple {ρ : ℝ} (hρ : 1 < ρ) {s : Finset (Fin (N + 1))} (hs : s.Nonempty) {n : ℤ}
    {a : ι → ConeSpace N → ℂ} (ha : IsHomOn (openCover ρ s) n a) (j : ι) :
    IsLaurent ρ s (lcoeff (a j)) ∧ (∀ α, lcoeff (a j) α ≠ 0 → ∑ k, α k = n) ∧
      ∀ z ∈ openCover ρ s, (∀ k, z k ≠ 0) → HasSum (fun α => lcoeff (a j) α * mono α z) (a j z) :=
  laurent_of_homogeneous hρ hs (ha.diff j) fun z hz c hc => ha.hom z hz c hc j

/-- **Support of the coefficients of a section over `K_s`**: `secCoeff` vanishes unless
`∑ α = n` and `α_k ≥ 0` for `k ∉ s`. -/
theorem secCoeff_ne_zero {ρ : ℝ} (hρ : 1 ≤ ρ) {n : ℤ} {s : Finset (Fin (N + 1))}
    (hs : s.Nonempty) (x : (coverSystem (freeSubquotient (ConeSpace N) ι) n ρ).obj s)
    {α : Fin (N + 1) → ℤ} {j : ι} (h : secCoeff hρ n s α j x ≠ 0) :
    (∀ k ∉ s, 0 ≤ α k) ∧ ∑ k, α k = n := by
  induction x using Submodule.Quotient.induction_on with
  | _ a =>
  obtain ⟨U, hKU, hU, -⟩ := a.2
  obtain ⟨ρ', hρ', hsub⟩ := exists_openCover_subset hs hU.isOpen hU.isCone hKU
  have hL := laurent_tuple (by linarith) hs (isHomOn_openCover_of_subset hU hsub) j
  exact ⟨hL.1.1 α h, hL.2.1 α h⟩

/-- Two sections over `K` which agree on an open cone around `K` have the same class. -/
theorem sectionMk_eq_of_eqOn {F : Subquotient (ConeSpace N) (puncture (ConeSpace N))} {n : ℤ}
    {K : Set (ConeSpace N)} {hK : K ⊆ puncture (ConeSpace N)} (x y : secM F n K hK)
    {W : Set (ConeSpace N)} (hKW : K ⊆ W) (hW : IsOpen W) (hWc : IsCone W)
    (h : ∀ w ∈ W, ∀ j, x.1 j w = y.1 j w) : sectionMk F x = sectionMk F y := by
  rw [sectionMk_eq_iff]
  obtain ⟨U, hKU, hU, -⟩ := x.2
  obtain ⟨V, hKV, hV, -⟩ := y.2
  exact isHomSection_of_eqOn F.coherent_N (U := U ∩ V) (fun z hz => ⟨hKU hz, hKV hz⟩)
    ((hU.inter hV.isOpen hV.isCone).sub (hV.inter_left hU.isOpen hU.isCone))
    (isHomSection_zero F.coherent_N n hK) hKW hW hWc fun z hz j => by
      simp [h z hz j]

/-! ### The contracting homotopy -/

/-- `k` is the least index with `α_k ≥ 0`. -/
def IsFirstNonneg (k : Fin (N + 1)) (α : Fin (N + 1) → ℤ) : Prop :=
  (∀ i, i < k → α i < 0) ∧ 0 ≤ α k

instance (k : Fin (N + 1)) (α : Fin (N + 1) → ℤ) : Decidable (IsFirstNonneg k α) := by
  unfold IsFirstNonneg
  infer_instance

theorem IsFirstNonneg.unique {k k' : Fin (N + 1)} {α : Fin (N + 1) → ℤ}
    (hk : IsFirstNonneg k α) (hk' : IsFirstNonneg k' α) : k = k' := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · exact absurd hk.2 (not_le.2 (hk'.1 k h))
  · exact absurd hk'.2 (not_le.2 (hk.1 k' h))

theorem exists_isFirstNonneg {α : Fin (N + 1) → ℤ} (h : ∃ i, 0 ≤ α i) :
    ∃ k, IsFirstNonneg k α := by
  classical
  obtain ⟨i, hi⟩ := h
  set S := Finset.univ.filter fun i => 0 ≤ α i with hSdef
  have hS : S.Nonempty := ⟨i, by simp [hSdef, hi]⟩
  refine ⟨S.min' hS, fun i' hi' => ?_, (Finset.mem_filter.1 (S.min'_mem hS)).2⟩
  by_contra h'
  push Not at h'
  exact absurd (S.min'_le i' (by simp [hSdef, h'])) (not_le.2 hi')

/-- The coefficients of the homotopy: `b_s = ∑_{k ∉ s} ε(k, s ∪ k) · (c_{s ∪ k})_{k(α) = k}`. -/
def homotopyCoeff (c : Finset (Fin (N + 1)) → (Fin (N + 1) → ℤ) → ℂ) (s : Finset (Fin (N + 1)))
    (α : Fin (N + 1) → ℤ) : ℂ :=
  ∑ k ∈ Finset.univ \ s, (cechSign (insert k s) k : ℂ) *
    (if IsFirstNonneg k α then c (insert k s) α else 0)

theorem homotopyCoeff_of_isFirstNonneg (c : Finset (Fin (N + 1)) → (Fin (N + 1) → ℤ) → ℂ)
    {k₀ : Fin (N + 1)} {α : Fin (N + 1) → ℤ} (hk₀ : IsFirstNonneg k₀ α)
    (s : Finset (Fin (N + 1))) :
    homotopyCoeff c s α =
      if k₀ ∈ s then 0 else (cechSign (insert k₀ s) k₀ : ℂ) * c (insert k₀ s) α := by
  unfold homotopyCoeff
  split_ifs with hs
  · refine Finset.sum_eq_zero fun k hk => ?_
    have hks : k ≠ k₀ := fun h => (Finset.mem_sdiff.1 hk).2 (h ▸ hs)
    rw [if_neg fun hP => hks (hP.unique hk₀), mul_zero]
  · rw [Finset.sum_eq_single_of_mem k₀ (Finset.mem_sdiff.2 ⟨Finset.mem_univ _, hs⟩)
      fun k _ hk => by rw [if_neg fun hP => hk (hP.unique hk₀), mul_zero], if_pos hk₀]

theorem homotopyCoeff_of_neg (c : Finset (Fin (N + 1)) → (Fin (N + 1) → ℤ) → ℂ)
    {α : Fin (N + 1) → ℤ} (hα : ∀ k, ¬IsFirstNonneg k α) (s : Finset (Fin (N + 1))) :
    homotopyCoeff c s α = 0 :=
  Finset.sum_eq_zero fun k _ => by rw [if_neg (hα k), mul_zero]

/-- **`d b = c` coefficientwise**, for a cocycle family `c` vanishing at the multi-indices with
all entries negative. -/
theorem sum_cechSign_homotopyCoeff (c : Finset (Fin (N + 1)) → (Fin (N + 1) → ℤ) → ℂ)
    (hcoc : ∀ u α, ∑ l ∈ u, (cechSign u l : ℂ) * c (u.erase l) α = 0)
    (htop : ∀ t α, (∀ i, α i < 0) → c t α = 0) (t : Finset (Fin (N + 1)))
    (α : Fin (N + 1) → ℤ) :
    ∑ j ∈ t, (cechSign t j : ℂ) * homotopyCoeff c (t.erase j) α = c t α := by
  classical
  by_cases hP : ∃ k, IsFirstNonneg k α
  · obtain ⟨k₀, hk₀⟩ := hP
    simp only [homotopyCoeff_of_isFirstNonneg c hk₀]
    by_cases hk₀t : k₀ ∈ t
    · rw [Finset.sum_eq_single_of_mem k₀ hk₀t fun j hj hjk => by
        rw [if_pos (Finset.mem_erase.2 ⟨fun h => hjk h.symm, hk₀t⟩), mul_zero]]
      rw [if_neg (Finset.notMem_erase k₀ t), Finset.insert_erase hk₀t, ← mul_assoc]
      have := cechSign_mul_self t k₀
      rw [show (cechSign t k₀ : ℂ) * cechSign t k₀ = 1 by exact_mod_cast this, one_mul]
    · set u := insert k₀ t with hudef
      have hut : u.erase k₀ = t := Finset.erase_insert hk₀t
      have hcu := hcoc u α
      rw [Finset.sum_insert hk₀t, hut] at hcu
      have hterm : ∀ j ∈ t, (cechSign t j : ℂ) * (if k₀ ∈ t.erase j then 0 else
          (cechSign (insert k₀ (t.erase j)) k₀ : ℂ) * c (insert k₀ (t.erase j)) α) =
          -(cechSign u k₀ : ℂ) * ((cechSign u j : ℂ) * c (u.erase j) α) := by
        intro j hj
        have hjk : j ≠ k₀ := fun h => hk₀t (h ▸ hj)
        rw [if_neg fun h => hk₀t (Finset.mem_of_mem_erase h)]
        have he : insert k₀ (t.erase j) = u.erase j := by
          rw [hudef, Finset.erase_insert_of_ne (Ne.symm hjk)]
        rw [he]
        have hs := cechSign_homotopy (u := u) (Finset.mem_insert_of_mem hj)
          (Finset.mem_insert_self k₀ t) hjk
        rw [hut] at hs
        have hs' : (cechSign t j : ℂ) * cechSign (u.erase j) k₀ =
            -((cechSign u k₀ : ℂ) * cechSign u j) := by exact_mod_cast hs
        linear_combination c (u.erase j) α * hs'
      rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
      have hsum : ∑ j ∈ t, (cechSign u j : ℂ) * c (u.erase j) α =
          -((cechSign u k₀ : ℂ) * c t α) := by linear_combination hcu
      rw [hsum]
      have := cechSign_mul_self u k₀
      have h1 : (cechSign u k₀ : ℂ) * cechSign u k₀ = 1 := by exact_mod_cast this
      linear_combination c t α * h1
  · push Not at hP
    have hα : ∀ i, α i < 0 := by
      by_contra h
      push Not at h
      obtain ⟨k, hk⟩ := exists_isFirstNonneg h
      exact hP k hk
    rw [htop t α hα]
    exact Finset.sum_eq_zero fun j _ => by rw [homotopyCoeff_of_neg c hP, mul_zero]

/-- **The contracting homotopy.** Let `ρ ≥ 1`. A `(q+1)`-cocycle of the Čech complex of
`𝒪^ι(n)` for the cover `(K_i)` whose Laurent coefficients at the multi-indices with all entries
negative vanish is a coboundary. -/
theorem exists_cechD_eq_free {ρ : ℝ} (hρ : 1 ≤ ρ) (n : ℤ) (q : ℕ)
    (z : cechCochain (coverSystem (freeSubquotient (ConeSpace N) ι) n ρ) (q + 1))
    (hz : cechDq _ (q + 1) z = 0)
    (htop : ∀ t α j, (∀ i, α i < 0) → secCoeff hρ n t α j (z.1 t) = 0) :
    ∃ b : cechCochain (coverSystem (freeSubquotient (ConeSpace N) ι) n ρ) q,
      cechDq _ q b = z := by
  classical
  -- representatives
  have hrep : ∀ t,
      ∃ a : secM (freeSubquotient (ConeSpace N) ι) n (coverSet ρ t) (coverSet_subset ρ t),
      sectionMk (freeSubquotient (ConeSpace N) ι) a = z.1 t :=
    fun t => Submodule.Quotient.mk_surjective _ (z.1 t)
  choose a ha using hrep
  set c : ι → Finset (Fin (N + 1)) → (Fin (N + 1) → ℤ) → ℂ :=
    fun j t α => lcoeff ((a t).1 j) α with hcdef
  have hc : ∀ j t α, c j t α = secCoeff hρ n t α j (z.1 t) := fun j t α => by
    rw [← ha t]
    rfl
  -- a common radius `ρ' > ρ`
  have hρt : ∀ t : Finset (Fin (N + 1)), ∃ ρt > ρ,
      t.Nonempty → IsHomOn (openCover ρt t) n (a t).1 := by
    intro t
    by_cases ht : t.Nonempty
    · obtain ⟨U, hKU, hU, -⟩ := (a t).2
      obtain ⟨ρt, hρt, hsub⟩ := exists_openCover_subset ht hU.isOpen hU.isCone hKU
      exact ⟨ρt, hρt, fun _ => isHomOn_openCover_of_subset hU hsub⟩
    · exact ⟨ρ + 1, by linarith, fun h => (ht h).elim⟩
  choose ρt hρtρ hρtU using hρt
  set δ : ℝ := Finset.univ.inf' Finset.univ_nonempty fun t => ρt t - ρ with hδdef
  have hδ : 0 < δ := (Finset.lt_inf'_iff _).2 fun t _ => by linarith [hρtρ t]
  set ρ' : ℝ := ρ + δ with hρ'def
  have hρ'1 : 1 < ρ' := by linarith
  have hhom : ∀ t, t.Nonempty → IsHomOn (openCover ρ' t) n (a t).1 := by
    intro t ht
    have hle : ρ' ≤ ρt t := by
      have := Finset.inf'_le (fun t => ρt t - ρ) (Finset.mem_univ t)
      linarith
    exact isHomOn_openCover_of_subset (hρtU t ht) (openCover_anti hle subset_rfl)
  have hlaur : ∀ t, t.Nonempty → ∀ j, IsLaurent ρ' t (c j t) ∧
      (∀ α, c j t α ≠ 0 → ∑ k, α k = n) ∧
      ∀ w ∈ openCover ρ' t, (∀ k, w k ≠ 0) →
        HasSum (fun α => c j t α * mono α w) ((a t).1 j w) :=
    fun t ht j => laurent_tuple hρ'1 ht (hhom t ht) j
  -- the cocycle identity for the coefficients
  have hcoc : ∀ j u α, ∑ l ∈ u, (cechSign u l : ℂ) * c j (u.erase l) α = 0 := by
    intro j u α
    have h : cechD (coverSystem (freeSubquotient (ConeSpace N) ι) n ρ) z.1 u = 0 := by
      have := congrFun (congrArg Subtype.val hz) u
      rw [cechDq_coe] at this
      exact this
    have h2 := congrArg (secCoeff hρ n u α j) h
    rw [cechD_apply, map_sum, map_zero] at h2
    rw [← h2]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_zsmul, secCoeff_res, hc, zsmul_eq_mul]
  have htop' : ∀ j t α, (∀ i, α i < 0) → c j t α = 0 := fun j t α hα => by
    rw [hc]
    exact htop t α j hα
  -- the coefficients of the homotopy and their sums
  set ρ'' : ℝ := ρ + δ / 2 with hρ''def
  have hρ''1 : 1 < ρ'' := by linarith
  set bc : ι → Finset (Fin (N + 1)) → (Fin (N + 1) → ℤ) → ℂ :=
    fun j s => homotopyCoeff (c j) s with hbcdef
  have hbc : ∀ s, s.Nonempty → ∀ j, IsLaurent ρ'' s (bc j s) ∧
      ∀ α, bc j s α ≠ 0 → ∑ k, α k = n := by
    intro s hs j
    refine ⟨IsLaurent.sum _ fun k hk => ?_, fun α hα => ?_⟩
    · have hks : k ∉ s := (Finset.mem_sdiff.1 hk).2
      have hL := (hlaur (insert k s) (Finset.insert_nonempty k s) j).1
      have hL' : IsLaurent ρ' (insert k s)
          (fun α => if IsFirstNonneg k α then c j (insert k s) α else 0) :=
        hL.of_subfamily fun α hα => by
          split_ifs at hα ⊢ with h
          · rfl
          · exact (hα rfl).elim
      exact (hL'.extend hks hs hρ''1 (by linarith) fun α hα => by
        split_ifs at hα with h
        · exact h.2
        · exact (hα rfl).elim).const_mul _
    · obtain ⟨k, hk, hk0⟩ := Finset.exists_ne_zero_of_sum_ne_zero hα
      have h1 := right_ne_zero_of_mul hk0
      split_ifs at h1 with h
      · exact (hlaur (insert k s) (Finset.insert_nonempty k s) j).2.1 α h1
      · exact (h1 rfl).elim
  set g : Finset (Fin (N + 1)) → (freeSubquotient (ConeSpace N) ι).ι → ConeSpace N → ℂ :=
    fun s j => lser (bc j s) with hgdef
  have hg : ∀ s, s.Nonempty → IsHomOn (openCover ρ'' s) n (g s) := fun s hs =>
    ⟨isOpen_openCover ρ'' s, isCone_openCover ρ'' s, openCover_subset_ne ρ'' s,
      fun j => (hbc s hs j).1.differentiableOn (by linarith),
      fun w _ a ha j => lser_smul (hbc s hs j).2 ha w⟩
  have hgsec : ∀ s, s.Nonempty →
      IsHomSection (freeSubquotient (ConeSpace N) ι).M n (coverSet ρ s) (g s) := fun s hs =>
    ⟨openCover ρ'' s, coverSet_subset_openCover (by linarith) s, hg s hs,
      fun y hy j => holAt_of_differentiableOn (isOpen_openCover ρ'' s) ((hg s hs).diff j) hy⟩
  -- the cochain `b`
  have hcard : ∀ s : Finset (Fin (N + 1)), s.card = q + 1 → s.Nonempty := fun s hs =>
    Finset.card_pos.1 (by omega)
  let bfam : ∀ s, (coverSystem (freeSubquotient (ConeSpace N) ι) n ρ).obj s := fun s =>
    if h : s.card = q + 1 then
      sectionMk (freeSubquotient (ConeSpace N) ι) ⟨g s, hgsec s (hcard s h)⟩
    else 0
  have hbmem : bfam ∈ cechCochain (coverSystem (freeSubquotient (ConeSpace N) ι) n ρ) q :=
    fun s hs => dif_neg hs
  have hbfam : ∀ s (h : s.card = q + 1),
      bfam s = sectionMk (freeSubquotient (ConeSpace N) ι) ⟨g s, hgsec s (hcard s h)⟩ :=
    fun s h => dif_pos h
  refine ⟨⟨bfam, hbmem⟩, Subtype.ext (funext fun t => ?_)⟩
  rw [cechDq_coe]
  by_cases ht : t.card = q + 1 + 1
  swap
  · rw [cechD_mem (coverSystem (freeSubquotient (ConeSpace N) ι) n ρ) hbmem t ht, z.2 t ht]
  have hne : ∀ j, (t.erase j).Nonempty := fun j => by
    by_cases hj : j ∈ t
    · exact Finset.card_pos.1 (by rw [Finset.card_erase_of_mem hj]; omega)
    · rw [Finset.erase_eq_of_notMem hj]
      exact Finset.card_pos.1 (by omega)
  have hgsecT : ∀ j,
      IsHomSection (freeSubquotient (ConeSpace N) ι).M n (coverSet ρ t) (g (t.erase j)) :=
    fun j =>
    (hgsec _ (hne j)).mono (coverSet_anti ρ (Finset.erase_subset j t))
  set G : secM (freeSubquotient (ConeSpace N) ι) n (coverSet ρ t) (coverSet_subset ρ t) :=
    ∑ j ∈ t, cechSign t j •
      (⟨g (t.erase j), hgsecT j⟩ : secM (freeSubquotient (ConeSpace N) ι) n (coverSet ρ t) _)
    with hGdef
  have hcj : ∀ j ∈ t, (t.erase j).card = q + 1 := fun j hj => by
    rw [Finset.card_erase_of_mem hj]
    omega
  have hD : cechD (coverSystem (freeSubquotient (ConeSpace N) ι) n ρ) bfam t =
      sectionMk (freeSubquotient (ConeSpace N) ι) G := by
    rw [cechD_apply]
    have hterm : ∀ j ∈ t, cechSign t j •
        (coverSystem (freeSubquotient (ConeSpace N) ι) n ρ).res (Finset.erase_subset j t)
          (bfam (t.erase j)) =
        Submodule.mkQ _ (cechSign t j • (⟨g (t.erase j), hgsecT j⟩ :
          secM (freeSubquotient (ConeSpace N) ι) n (coverSet ρ t) (coverSet_subset ρ t))) := by
      intro j hj
      rw [map_zsmul, hbfam _ (hcj j hj)]
      rfl
    rw [Finset.sum_congr rfl hterm]
    exact (map_sum _ _ _).symm
  rw [hD, ← ha t]
  have hnt : t.Nonempty := Finset.card_pos.1 (by omega)
  have hW : openCover ρ'' t ⊆ openCover ρ' t := openCover_anti (by linarith) subset_rfl
  refine sectionMk_eq_of_eqOn G (a t) (coverSet_subset_openCover (by linarith) t)
    (isOpen_openCover ρ'' t) (isCone_openCover ρ'' t) fun w hw jj => ?_
  -- compare the two holomorphic functions on `V_t(ρ'')`
  have hGval : ∀ w, G.1 jj w = ∑ j ∈ t, (cechSign t j : ℂ) * g (t.erase j) jj w := by
    intro w
    simp only [hGdef, Submodule.coe_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    show cechSign t j • g (t.erase j) jj w = _
    rw [zsmul_eq_mul]
  have hWj : ∀ j, openCover ρ'' t ⊆ openCover ρ'' (t.erase j) := fun j =>
    openCover_anti le_rfl (Finset.erase_subset j t)
  refine eqOn_of_eqOn_coord_ne_zero (f := fun w => G.1 jj w) (g := fun w => (a t).1 jj w)
    (isOpen_openCover ρ'' t) ?_ ?_ (fun w hw hw0 => ?_) hw
  · have : ContinuousOn (fun w => ∑ j ∈ t, (cechSign t j : ℂ) * g (t.erase j) jj w)
        (openCover ρ'' t) :=
      continuousOn_finsetSum _ fun j _ => continuousOn_const.mul
        (((hg _ (hne j)).diff jj).continuousOn.mono (hWj j))
    exact this.congr fun w _ => hGval w
  · exact ((hhom t hnt).diff jj).continuousOn.mono hW
  · rw [hGval]
    have h1 : HasSum (fun α => ∑ j ∈ t, (cechSign t j : ℂ) * (bc jj (t.erase j) α * mono α w))
        (∑ j ∈ t, (cechSign t j : ℂ) * g (t.erase j) jj w) :=
      hasSum_sum fun j _ => ((hbc _ (hne j) jj).1.hasSum_lser (by linarith)
        (hWj j hw)).mul_left _
    have h2 := (hlaur t hnt jj).2.2 w (hW hw) hw0
    refine h1.unique (h2.congr_fun fun α => ?_)
    rw [← sum_cechSign_homotopyCoeff (c jj) (hcoc jj) (htop' jj) t α, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [hbcdef]
    ring

/-! ### Vanishing and finiteness -/

/-- **`Ȟ^q(ℙᴺ, 𝒪(n)^ι) = 0` for `0 < q < N`, and for `q = N` if `n ≥ -N`** (Čech cohomology of
the closed cover `(K_i)`, `ρ ≥ 1`). With `coverSystem_cechH_subsingleton` (`q ≥ N + 1`): all
higher cohomology of `𝒪(n)^ι` vanishes for `n ≥ -N`. -/
theorem cechH_free_subsingleton {ρ : ℝ} (hρ : 1 ≤ ρ) (n : ℤ) {q : ℕ} (hq : 1 ≤ q)
    (h : q ≠ N ∨ -(N : ℤ) ≤ n) :
    Subsingleton (cechH (coverSystem (freeSubquotient (ConeSpace N) ι) n ρ) q) := by
  classical
  by_cases hqN : N + 1 ≤ q
  · exact coverSystem_cechH_subsingleton n ρ hqN
  obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
  refine cechH_subsingleton_of_exact _ q' fun z hz => exists_cechD_eq_free hρ n q' z hz ?_
  intro t α j hα
  by_contra hne
  have hzt : z.1 t ≠ 0 := fun h0 => hne (by rw [h0, map_zero])
  have htc : t.card = q' + 1 + 1 := by
    by_contra hc
    exact hzt (z.2 t hc)
  have hnt : t.Nonempty := Finset.card_pos.1 (by omega)
  obtain ⟨hsupp, hsum⟩ := secCoeff_ne_zero hρ hnt (z.1 t) hne
  have hall : t = Finset.univ := Finset.eq_univ_of_forall fun k => by
    by_contra hk
    exact absurd (hsupp k hk) (not_le.2 (hα k))
  have hqN' : q' + 1 = N := by
    have := congrArg Finset.card hall
    rw [Finset.card_univ, Fintype.card_fin] at this
    omega
  have hle : ∑ k, α k ≤ -((N : ℤ) + 1) := by
    calc ∑ k, α k ≤ ∑ _k : Fin (N + 1), (-1 : ℤ) :=
          Finset.sum_le_sum fun k _ => by linarith [hα k]
      _ = -((N : ℤ) + 1) := by simp
  rcases h with h | h
  · exact h hqN'
  · linarith

/-- The case of the structure sheaf: `Ȟ^q(ℙᴺ, 𝒪(n)) = 0` for `0 < q < N`, and for `q ≥ 1` if
`n ≥ -N`. -/
theorem cechH_structureSheaf_subsingleton {ρ : ℝ} (hρ : 1 ≤ ρ) (n : ℤ) {q : ℕ} (hq : 1 ≤ q)
    (h : q ≠ N ∨ -(N : ℤ) ≤ n) :
    Subsingleton (cechH (coverSystem (structureSheaf N) n ρ) q) :=
  cechH_free_subsingleton hρ n hq h

/-- **`Ȟ^q(ℙᴺ, 𝒪(n)^ι)` is finite-dimensional for every `q ≥ 1` and every `n`.** For `q ≠ N`
it vanishes; `Ȟ^N` is detected by the finitely many Laurent coefficients `κ_{α,j}(z_{0…N})`
with all `α_k ≤ -1` and `∑ α = n`. -/
theorem finiteDimensional_cechH_free {ρ : ℝ} (hρ : 1 ≤ ρ) (n : ℤ) {q : ℕ} (hq : 1 ≤ q) :
    FiniteDimensional ℂ (cechH (coverSystem (freeSubquotient (ConeSpace N) ι) n ρ) q) := by
  classical
  by_cases hqN : q ≠ N
  · have := cechH_free_subsingleton (ι := ι) hρ n hq (Or.inl hqN)
    exact Module.Finite.of_finite
  push Not at hqN
  obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
  set Γ := coverSystem (freeSubquotient (ConeSpace N) ι) n ρ with hΓdef
  set A : Finset (Fin (N + 1) → ℤ) := Fintype.piFinset fun _ => Finset.Icc n 0 with hAdef
  -- the coefficients at the multi-indices of `A` of the component on `{0, …, N}`
  let φ : LinearMap.ker (cechDq Γ (q' + 1)) →ₗ[ℂ] (↥A × ι → ℂ) :=
    LinearMap.pi fun p => (secCoeff hρ n Finset.univ p.1.1 p.2).comp
      ((LinearMap.proj Finset.univ).comp ((cechCochain Γ (q' + 1)).subtype.comp
        (LinearMap.ker (cechDq Γ (q' + 1))).subtype))
  have hφ : ∀ z, φ z = 0 → cechClass Γ (q' + 1) z = 0 := by
    intro z hz
    rw [cechClass_eq_zero_iff Γ q']
    refine exists_cechD_eq_free hρ n q' z.1 z.2 fun t α j hα => ?_
    by_contra hne
    have hzt : z.1.1 t ≠ 0 := fun h0 => hne (by rw [h0, map_zero])
    have hnt : t.Nonempty := by
      by_contra ht
      rw [Finset.not_nonempty_iff_eq_empty] at ht
      exact hzt (z.1.2 t (by rw [ht]; simp))
    obtain ⟨hsupp, hsum⟩ := secCoeff_ne_zero hρ hnt (z.1.1 t) hne
    have hall : t = Finset.univ := Finset.eq_univ_of_forall fun k => by
      by_contra hk
      exact absurd (hsupp k hk) (not_le.2 (hα k))
    subst hall
    have hαA : α ∈ A := by
      rw [hAdef, Fintype.mem_piFinset]
      intro k
      rw [Finset.mem_Icc]
      refine ⟨?_, (hα k).le⟩
      have h1 : ∑ i ∈ Finset.univ.erase k, α i ≤ 0 :=
        Finset.sum_nonpos fun i _ => (hα i).le
      have h2 := Finset.add_sum_erase Finset.univ α (Finset.mem_univ k)
      linarith
    have := congrFun hz (⟨α, hαA⟩, j)
    exact hne this
  -- `Ȟ^{q'+1}` is the image of `range φ` under `cechClass ∘ (a right inverse of φ)`
  obtain ⟨gφ, hgφ⟩ := φ.rangeRestrict.exists_rightInverse_of_surjective
    (LinearMap.range_rangeRestrict φ)
  let ψ : LinearMap.range φ →ₗ[ℂ] cechH Γ (q' + 1) :=
    (cechClass Γ (q' + 1)).comp gφ
  have hψ : Function.Surjective ψ := by
    intro x
    obtain ⟨z, rfl⟩ := cechClass_surjective Γ (q' + 1) x
    refine ⟨φ.rangeRestrict z, ?_⟩
    have h1 : φ (gφ (φ.rangeRestrict z)) = φ z := by
      have := congrArg Subtype.val (LinearMap.congr_fun hgφ (φ.rangeRestrict z))
      simpa using this
    have h2 := hφ (z + (-1 : ℂ) • gφ (φ.rangeRestrict z))
      (by rw [map_add, map_smul, h1, neg_one_smul, add_neg_cancel])
    rw [map_add, map_smul, neg_one_smul, add_neg_eq_zero] at h2
    exact h2.symm
  exact Module.Finite.of_surjective ψ hψ

end SGPT.GAGA.PN
