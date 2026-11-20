import SGPT.Toric.Toric5Multiplier

/-!
# The `T_c`-weight decomposition of `H⁰(X, L ⊗ 𝓘(φ))`

Source `chapter_toric_ample.tex`, proof of `thm:Yao`: "`H⁰(X, L ⊗ 𝓘(φ))` is a `T_c`-invariant
subspace of `H⁰(X, L)`.  Since the `T_c`-weight spaces in `H⁰(X, L)` are the lines `ℂ χ^m`, it is
the direct sum of suitable `ℂ χ^m`'s."

* `translate_mem_toricMultiplierSections`: for a `T_c`-invariant quasi-psh `φ` and `t ∈ T_c`,
  `g ∈ H⁰(X, O(D) ⊗ 𝓘(cφ)) ⇒ g(t · ) ∈ H⁰(X, O(D) ⊗ 𝓘(cφ))` (in a vertex chart, `t` acts by a
  linear biholomorphism preserving `φ`, and local weighted integrability is invariant under
  biholomorphisms, `Pending.ChartWeightedL2.multiplierIntegrableAt_comp`);
* `latticeCharacter_mem_of_sum_mem`: in a `T_c`-invariant space of functions, every character
  occurring with a nonzero coefficient in an element lies in the space (separation of the
  weights by suitable elements of `T_c`);
* `toricMultiplierSections_eq_span`, `finrank_toricMultiplierSections`:
  `H⁰(X, O(D) ⊗ 𝓘(cφ)) = ⊕_{χ^m ∈ H⁰(X, O(D) ⊗ 𝓘(cφ))} ℂ χ^m`, so
  `h⁰(X, O(D) ⊗ 𝓘(cφ)) = #{m ∈ M : χ^m ∈ H⁰(X, O(D) ⊗ 𝓘(cφ))}`.
-/

set_option autoImplicit false
noncomputable section
namespace SGPT.Toric
open Set Filter MeasureTheory SGPT.PSH SGPT.PSH.VariableComplexAtlas SGPT.Convex
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open scoped Topology ContDiff BigOperators Manifold ENNReal

variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin n → ℤ} {hs : latticePolytopeEdgeSmooth γ}

/-! ### The torus action in vertex coordinates -/

theorem modelActionLinear_apply (v : latticePolytopeVertices γ) (t : Fin n → ℂˣ)
    (z : ComplexModel n) (j : Fin n) :
    originalPolytopeNativeModelActionLinear γ hs v t z j =
      (latticeCharacter (originalPolytopeNativeBasis γ hs v j) t : ℂ) * z j := rfl

theorem modelActionLinear_mul (v : latticePolytopeVertices γ) (s t : Fin n → ℂˣ)
    (z : ComplexModel n) :
    originalPolytopeNativeModelActionLinear γ hs v s
        (originalPolytopeNativeModelActionLinear γ hs v t z) =
      originalPolytopeNativeModelActionLinear γ hs v (s * t) z := by
  ext j
  simp only [modelActionLinear_apply, map_mul, Units.val_mul]
  ring

theorem modelActionLinear_one (v : latticePolytopeVertices γ) (z : ComplexModel n) :
    originalPolytopeNativeModelActionLinear γ hs v 1 z = z := by
  ext j
  simp [modelActionLinear_apply]

/-- The vertex coordinates of `t · a`. -/
theorem vertexChart_embedding_mul (v : latticePolytopeVertices γ) (t a : Fin n → ℂˣ) :
    originalPolytopeNativeModelChart γ hs v (polytopeToricEmbedding γ hs (t * a)) =
      originalPolytopeNativeModelActionLinear γ hs v t
        (originalPolytopeNativeModelChart γ hs v (polytopeToricEmbedding γ hs a)) := by
  rw [← polytopeToricAction_embedding]
  exact originalPolytopeNativeModelChart_action γ hs v t _ (embedding_mem_vertexChart_source v a)

/-- A `T_c`-invariant function has `T_c`-invariant vertex chart functions. -/
theorem chartFunction_modelActionLinear {φ : PolytopeToricVariety γ hs → EReal}
    (hinv : PolytopeToricInvariant γ hs φ) (v : latticePolytopeVertices γ)
    {t : Fin n → ℂˣ} (ht : IsCompactTorusElement t) (z : ComplexModel n) :
    chartFunction φ (polytopeToricVertexChart γ hs v)
        (originalPolytopeNativeModelActionLinear γ hs v t z) =
      chartFunction φ (polytopeToricVertexChart γ hs v) z := by
  change φ ((originalPolytopeNativeModelChart γ hs v).symm
    (originalPolytopeNativeModelActionLinear γ hs v t z)) =
      φ ((originalPolytopeNativeModelChart γ hs v).symm z)
  have hsrc : originalPolytopeNativeAction γ t ((originalPolytopeNativeModelChart γ hs v).symm z) ∈
      (originalPolytopeNativeModelChart γ hs v).source := by
    rw [originalPolytopeNativeModelChart_source]
    apply (originalPolytopeNativeAction_mem_chart_source_iff γ hs v t _).mpr
    rw [← originalPolytopeNativeModelChart_source]
    exact vertexChart_symm_mem_source v z
  rw [← originalPolytopeNativeModelChart_action_symm γ hs v t z,
    (originalPolytopeNativeModelChart γ hs v).left_inv hsrc]
  exact hinv t ht _

/-! ### `T_c`-invariance of `H⁰(X, O(D) ⊗ 𝓘(cφ))` -/

variable {D : ToricDivisor γ hs}

/-- Translation by `t ∈ T(ℂ)` preserves `H⁰(X, O(D))`. -/
theorem translate_mem_toricSections {g : (Fin n → ℂˣ) → ℂ} (hg : g ∈ toricSections D)
    (t : Fin n → ℂˣ) : (fun a => g (t * a)) ∈ toricSections D := by
  intro v
  obtain ⟨f, hf, hgf⟩ := hg v
  refine ⟨fun z => (latticeCharacter (toricCartierDatum D v) t : ℂ) *
      f (originalPolytopeNativeModelActionLinear γ hs v t z),
    (differentiable_const _).mul (hf.comp (originalPolytopeNativeModelActionLinear γ hs v t).differentiable),
    fun a => ?_⟩
  show g (t * a) = _
  dsimp only
  rw [hgf (t * a), vertexChart_embedding_mul, map_mul, Units.val_mul]
  ring

/-- Source proof of `thm:Yao`: `H⁰(X, O(D) ⊗ 𝓘(cφ))` is `T_c`-invariant for `T_c`-invariant `φ`. -/
theorem translate_mem_toricMultiplierSections {c : ℝ} (hc : 0 < c)
    {φ : PolytopeToricVariety γ hs → EReal}
    (hφ : (ofFixedModel n (PolytopeToricVariety γ hs)).IsQPSH φ)
    (hinv : PolytopeToricInvariant γ hs φ) {g : (Fin n → ℂˣ) → ℂ}
    (hg : g ∈ toricMultiplierSections D hc hφ) {t : Fin n → ℂˣ} (ht : IsCompactTorusElement t) :
    (fun a => g (t * a)) ∈ toricMultiplierSections D hc hφ := by
  rw [mem_toricMultiplierSections_iff] at hg ⊢
  refine ⟨translate_mem_toricSections hg.1 t, ?_⟩
  intro v f' hf' hgf' z
  obtain ⟨f, hf, hgf⟩ := hg.1 v
  set L := originalPolytopeNativeModelActionLinear γ hs v t
  set α : ℂ := (latticeCharacter (toricCartierDatum D v) t : ℂ)
  have hcoeff : f' = fun z => α * f (L z) := by
    apply toricSectionCoeff_unique (D := D) (f' := fun z => α * f (L z)) v hf'
      (continuous_const.mul (hf.continuous.comp L.continuous)) hgf'
    intro a
    show g (t * a) = _
    rw [hgf (t * a), vertexChart_embedding_mul, map_mul, Units.val_mul]
    beta_reduce
    ring
  rw [hcoeff]
  have hint : MultiplierIntegrableAt (chartFunction φ (polytopeToricVertexChart γ hs v)) c f
      (L z) volume := hg.2 v f hf.continuous hgf (L z)
  have hqpsh := IsQPSH.chartFunction hφ (polytopeToricVertexChart γ hs v)
  rw [vertexChart_val, vertexChart_target] at hqpsh
  have hcomp : MultiplierIntegrableAt (chartFunction φ (polytopeToricVertexChart γ hs v)) c
      (fun w => f (L w)) z volume := by
    have hinvt : IsCompactTorusElement t⁻¹ := isCompactTorusElement_inv ht
    refine Pending.ChartWeightedL2.multiplierIntegrableAt_comp (τ := L)
      (σ := originalPolytopeNativeModelActionLinear γ hs v t⁻¹) isOpen_univ isOpen_univ
      L.differentiable.differentiableOn
      ((originalPolytopeNativeModelActionLinear γ hs v t⁻¹).restrictScalars ℝ).contDiff.contDiffOn
      (mapsTo_univ _ _) (mapsTo_univ _ _) (fun w _ => ?_) (fun w _ => ?_)
      (fun w _ => chartFunction_modelActionLinear hinv v ht w)
      hqpsh.upperSemicontinuousOn hc.ne' (mem_univ z) hint
    · rw [modelActionLinear_mul, inv_mul_cancel, modelActionLinear_one]
    · rw [modelActionLinear_mul, mul_inv_cancel, modelActionLinear_one]
  exact Pending.multiplierIntegrableAt_holomorphic_mul (hqpsh z (mem_univ z)) hcomp analyticAt_const

/-! ### Separation of weights -/

/-- An element of the compact torus separating two distinct characters. -/
theorem exists_compactTorus_separating {m m' : Fin n → ℤ} (hmm : m ≠ m') :
    ∃ t : Fin n → ℂˣ, IsCompactTorusElement t ∧
      (latticeCharacter m t : ℂ) ≠ latticeCharacter m' t := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, m i ≠ m' i := by
    by_contra hall
    push Not at hall
    exact hmm (funext hall)
  set d : ℤ := m i - m' i
  have hd : (d : ℂ) ≠ 0 := by exact_mod_cast sub_ne_zero.mpr hi
  set s : ℂˣ := Units.mk0 (Complex.exp (Real.pi * Complex.I / d)) (Complex.exp_ne_zero _)
  set t : Fin n → ℂˣ := Pi.mulSingle i s
  refine ⟨t, fun j => ?_, ?_⟩
  · by_cases hj : j = i
    · subst hj
      simp only [t, Pi.mulSingle_eq_same, s, Units.val_mk0]
      rw [Complex.norm_exp]
      have : (Real.pi * Complex.I / d).re = 0 := by
        have hre : ((d : ℂ)).im = 0 := by simp
        simp [Complex.div_re, Complex.mul_re]
      rw [this, Real.exp_zero]
    · simp [t, Pi.mulSingle_eq_of_ne hj]
  · have hchar : ∀ μ : Fin n → ℤ, (latticeCharacter μ t : ℂ) = (s : ℂ) ^ μ i := by
      intro μ
      simp only [latticeCharacter, MonoidHom.coe_mk, OneHom.coe_mk, t, Units.coe_prod,
        Units.val_zpow_eq_zpow_val]
      rw [Finset.prod_eq_single i]
      · simp
      · intro j _ hj; simp [Pi.mulSingle_eq_of_ne hj]
      · intro h; exact absurd (Finset.mem_univ i) h
    rw [hchar, hchar]
    intro heq
    have hs0 : (s : ℂ) ≠ 0 := Units.ne_zero s
    have h1 : (s : ℂ) ^ d = 1 := by
      simp only [d]
      rw [zpow_sub₀ hs0, heq, div_self (zpow_ne_zero _ hs0)]
    have h2 : (s : ℂ) ^ d = -1 := by
      simp only [s, Units.val_mk0]
      rw [← Complex.exp_int_mul, mul_div_cancel₀ _ hd, Complex.exp_pi_mul_I]
    rw [h1] at h2
    norm_num at h2

/-- Source proof of `thm:Yao`: in a `T_c`-invariant space `W` of functions on `T(ℂ)`, every
character occurring with a nonzero coefficient in an element of `W` lies in `W`. -/
theorem latticeCharacter_mem_of_sum_mem (W : Submodule ℂ ((Fin n → ℂˣ) → ℂ))
    (hW : ∀ t : Fin n → ℂˣ, IsCompactTorusElement t → ∀ g ∈ W, (fun a => g (t * a)) ∈ W) :
    ∀ (s : Finset (Fin n → ℤ)) (c : (Fin n → ℤ) → ℂ),
      (fun a => ∑ m ∈ s, c m * (latticeCharacter m a : ℂ)) ∈ W →
      ∀ m ∈ s, c m ≠ 0 → (fun a => (latticeCharacter m a : ℂ)) ∈ W := by
  classical
  intro s
  induction s using Finset.strongInduction with
  | H s ih =>
  intro c hg m hm hcm
  by_cases hother : ∃ m' ∈ s, m' ≠ m ∧ c m' ≠ 0
  · obtain ⟨m', hm', hne, hcm'⟩ := hother
    obtain ⟨t, ht, hsep⟩ := exists_compactTorus_separating hne.symm
    set c' : (Fin n → ℤ) → ℂ := fun μ =>
      c μ * ((latticeCharacter μ t : ℂ) - latticeCharacter m' t)
    have hsum : (fun a => ∑ μ ∈ s.erase m', c' μ * (latticeCharacter μ a : ℂ)) =
        (fun a => ∑ μ ∈ s, c μ * (latticeCharacter μ (t * a) : ℂ)) -
          (latticeCharacter m' t : ℂ) • fun a => ∑ μ ∈ s, c μ * (latticeCharacter μ a : ℂ) := by
      funext a
      have h1 : ∑ μ ∈ s, c' μ * (latticeCharacter μ a : ℂ) =
          ∑ μ ∈ s.erase m', c' μ * (latticeCharacter μ a : ℂ) := by
        rw [← Finset.sum_erase_add s _ hm']
        simp [c']
      rw [← h1]
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun μ _ => ?_
      simp only [c', map_mul, Units.val_mul]
      ring
    have hg' : (fun a => ∑ μ ∈ s.erase m', c' μ * (latticeCharacter μ a : ℂ)) ∈ W := by
      rw [hsum]
      exact W.sub_mem (hW t ht _ hg) (W.smul_mem _ hg)
    refine ih (s.erase m') (Finset.erase_ssubset hm') c' hg' m
      (Finset.mem_erase.mpr ⟨hne.symm, hm⟩) ?_
    exact mul_ne_zero hcm (sub_ne_zero.mpr hsep)
  · push Not at hother
    have hsingle : (fun a => ∑ μ ∈ s, c μ * (latticeCharacter μ a : ℂ)) =
        c m • fun a => (latticeCharacter m a : ℂ) := by
      funext a
      rw [Finset.sum_eq_single m]
      · rfl
      · intro μ hμ hμm
        rw [hother μ hμ hμm, zero_mul]
      · intro h; exact absurd hm h
    rw [hsingle] at hg
    have := W.smul_mem (c m)⁻¹ hg
    rwa [smul_smul, inv_mul_cancel₀ hcm, one_smul] at this

/-! ### The decomposition -/

/-- Source proof of `thm:Yao`: `H⁰(X, O(D) ⊗ 𝓘(cφ))` is spanned by the characters it contains. -/
theorem toricMultiplierSections_eq_span {c : ℝ} (hc : 0 < c)
    {φ : PolytopeToricVariety γ hs → EReal}
    (hφ : (ofFixedModel n (PolytopeToricVariety γ hs)).IsQPSH φ)
    (hinv : PolytopeToricInvariant γ hs φ) :
    toricMultiplierSections D hc hφ = Submodule.span ℂ
      ((fun m : Fin n → ℤ => fun a : Fin n → ℂˣ => (latticeCharacter m a : ℂ)) ''
        {m | (fun a => (latticeCharacter m a : ℂ)) ∈ toricMultiplierSections D hc hφ}) := by
  classical
  apply le_antisymm
  · intro g hg
    have hrep := eq_sum_of_mem_toricSections hg.1
    set S := (finite_toricLatticePoints D).toFinset
    set coef := fun m => UnitAddTorus.mFourierCoeff (fun t => g (compactTorusPoint t)) m
    have hgeq : g = fun a => ∑ m ∈ S, coef m * (latticeCharacter m a : ℂ) := funext hrep
    have hmem : ∀ m ∈ S, coef m ≠ 0 →
        (fun a => (latticeCharacter m a : ℂ)) ∈ toricMultiplierSections D hc hφ := by
      intro m hm hcm
      apply latticeCharacter_mem_of_sum_mem _ (fun t ht g' hg' =>
        translate_mem_toricMultiplierSections hc hφ hinv hg' ht) S coef _ m hm hcm
      rw [← hgeq]; exact hg
    rw [hgeq]
    have hsum : (fun a => ∑ m ∈ S, coef m * (latticeCharacter m a : ℂ)) =
        ∑ m ∈ S, coef m • fun a => (latticeCharacter m a : ℂ) := by
      funext a; simp [Finset.sum_apply]
    rw [hsum]
    refine Submodule.sum_mem _ fun m hm => ?_
    by_cases hcm : coef m = 0
    · rw [hcm, zero_smul]; exact Submodule.zero_mem _
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨m, hmem m hm hcm, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨m, hm, rfl⟩
    exact hm

/-- The characters in `H⁰(X, O(D) ⊗ 𝓘(cφ))` are lattice points of `P_D`. -/
theorem setOf_latticeCharacter_mem_subset {c : ℝ} (hc : 0 < c)
    {φ : PolytopeToricVariety γ hs → EReal}
    (hφ : (ofFixedModel n (PolytopeToricVariety γ hs)).IsQPSH φ) :
    {m | (fun a => (latticeCharacter m a : ℂ)) ∈ toricMultiplierSections D hc hφ} ⊆
      toricLatticePoints D := fun _ hm => mem_toricLatticePoints_of_latticeCharacter_mem hm.1

/-- `h⁰(X, O(D) ⊗ 𝓘(cφ)) = #{m ∈ M : χ^m ∈ H⁰(X, O(D) ⊗ 𝓘(cφ))}`. -/
theorem finrank_toricMultiplierSections {c : ℝ} (hc : 0 < c)
    {φ : PolytopeToricVariety γ hs → EReal}
    (hφ : (ofFixedModel n (PolytopeToricVariety γ hs)).IsQPSH φ)
    (hinv : PolytopeToricInvariant γ hs φ) :
    Module.finrank ℂ (toricMultiplierSections D hc hφ) =
      {m | (fun a => (latticeCharacter m a : ℂ)) ∈ toricMultiplierSections D hc hφ}.ncard := by
  set T := {m | (fun a => (latticeCharacter m a : ℂ)) ∈ toricMultiplierSections D hc hφ}
  have hfin : T.Finite := (finite_toricLatticePoints D).subset (setOf_latticeCharacter_mem_subset hc hφ)
  let _ := hfin.fintype
  have h := finrank_span_eq_card
    ((linearIndependent_latticeCharacter).comp (Subtype.val : T → Fin n → ℤ) Subtype.val_injective)
  simp only [Function.comp_def] at h
  have hrange : (Set.range fun m : T => fun a : Fin n → ℂˣ => (latticeCharacter m.val a : ℂ)) =
      (fun m : Fin n → ℤ => fun a : Fin n → ℂˣ => (latticeCharacter m a : ℂ)) '' T := by
    ext g; simp
  rw [toricMultiplierSections_eq_span hc hφ hinv, ← hrange, h, Set.ncard_eq_toFinset_card',
    Set.toFinset_card]

end SGPT.Toric
