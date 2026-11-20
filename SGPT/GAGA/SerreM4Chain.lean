import SGPT.GAGA.SerreM3Nakayama

/-!
# Serre's theorems on `ℙᴺ`, part 13: the saturation chain in the hyperplane step

Towards source `lma:GAGA` (`chapter_NApotential.tex`, lines 1143--1145), milestone M4.2.

For `1 ≤ d ≤ N`, a subsheaf `M/I_{L_d}` of `𝒪_{L_d}^ι` and the coordinate `z_d`, let
`G_k = (M : z_d^k)/I_{L_d}` and `Q_k = (M : z_d^k + I_{L_{d-1}})/I_{L_{d-1}}`. The hyperplane
sequences `0 → G_{k+1}(-1) → G_k → Q_k → 0` (`chain_shortExact`) and the stabilization
`G_{k₀+1} = G_{k₀}` give, assuming `Ȟ¹(Q_k(m)) = 0` for `m ≫ 0` (Theorem B one dimension lower),
that multiplication by `z_d`, `Ȟ¹(G_{k+1}(n)) → Ȟ¹(G_k(n+1))`, is **injective** for `n ≫ 0` and
every `k ≤ k₀` (`chain_injective`): the dimensions of `Ȟ¹(G_{k₀}(n))` are finite
(`finiteDimensional_cechH_one_Sd'`) and non-increasing, hence eventually constant, so `z_d` is
bijective at `k₀`; for `k < k₀` the composite of `z_d` with the inclusion `G_k → G_{k₀}` is the
composite of the inclusion of `G_{k+1}` with `z_d` on `G_{k₀}` (`chain_square_left`,
`chain_square_right`, `chain_square_top`). Consequently `Ȟ⁰(G_k(n+1)) → Ȟ⁰(Q_k(n+1))` is onto
(`chain_H0_surjective`).

Blueprint: `claude-serre-m34.tex`, node `claude-serre-m34:chain`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Set Filter Topology
open SGPT.Foundations.Analysis.Pending.OkaRelationSheaf
open SGPT.GAGA.Core
open Module

noncomputable section

namespace SGPT.GAGA.PN

/-! ### Linear algebra -/

theorem finrank_le_of_surjective' {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] [FiniteDimensional ℂ V] (f : V →ₗ[ℂ] W) (hf : Function.Surjective f) :
    finrank ℂ W ≤ finrank ℂ V := by
  have h := LinearMap.finrank_range_le f
  rwa [LinearMap.range_eq_top.2 hf, finrank_top] at h

theorem finrank_eq_of_bijective' {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] (f : V →ₗ[ℂ] W) (hf : Function.Bijective f) : finrank ℂ V = finrank ℂ W :=
  (LinearEquiv.ofBijective f hf).finrank_eq

/-- A sequence of naturals, non-increasing from `n₀` on, is eventually constant. -/
theorem eventually_const_of_antitone (f : ℤ → ℕ) (n₀ : ℤ)
    (hf : ∀ n ≥ n₀, f (n + 1) ≤ f n) : ∃ n₁ ≥ n₀, ∀ n ≥ n₁, f (n + 1) = f n := by
  classical
  set S : Set ℕ := f '' Set.Ici n₀ with hSdef
  have hne : S.Nonempty := ⟨f n₀, n₀, Set.mem_Ici.2 le_rfl, rfl⟩
  obtain ⟨n₁, hn₁, hv⟩ := Nat.sInf_mem hne
  have hmin : ∀ n ≥ n₀, f n₁ ≤ f n := fun n hn => by
    rw [hv]
    exact Nat.sInf_le ⟨n, hn, rfl⟩
  have hdec : ∀ n ≥ n₁, f n ≤ f n₁ := by
    intro n hn
    induction n, hn using Int.leInduction with
    | base => exact le_rfl
    | succ n hn ih => exact (hf n (le_trans hn₁ hn)).trans ih
  refine ⟨n₁, hn₁, fun n hn => ?_⟩
  have h1 := hdec (n + 1) (by omega)
  have h2 := hmin (n + 1) (by have : n₀ ≤ n₁ := hn₁; omega)
  have h3 := hdec n hn
  have h4 := hmin n (le_trans hn₁ hn)
  omega

variable {N : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ### Members of `𝒮_d` and the saturation chain -/

/-- `M` is an invariant coherent subsheaf of `𝒪^ι` containing `I_{L_d} 𝒪^ι`, i.e. `M/I_{L_d}` is an
invariant subsheaf of `𝒪_{L_d}^ι`. -/
structure InS (d : ℕ) (M : GermModule (ConeSpace N) ι) : Prop where
  coh : M.IsCoherentOn (puncture (ConeSpace N))
  inv : IsConeInvariant M
  le : (Idm d ι).LeOn M (puncture (ConeSpace N))

theorem satChain_le_succ_iter {M : GermModule (ConeSpace N) ι} (e : Fin (N + 1))
    (hM : M.IsCoherentOn (puncture (ConeSpace N))) {k k' : ℕ} (h : k ≤ k') :
    (satChain M e k).LeOn (satChain M e k') (puncture (ConeSpace N)) := by
  induction k', h using Nat.le_induction with
  | base => exact GermModule.LeOn.refl _ _
  | succ k' _ ih => exact ih.trans (satChain_mono e hM k')

theorem InS.satChain {d : ℕ} {M : GermModule (ConeSpace N) ι} (hS : InS d M) (e : Fin (N + 1))
    (k : ℕ) : InS d (satChain M e k) :=
  ⟨satChain_coherent e hS.coh k, satChain_invariant e hS.coh hS.inv k,
    hS.le.trans (satChain_le_succ_iter e hS.coh (Nat.zero_le k))⟩

theorem InS.sup_pred {d : ℕ} {M : GermModule (ConeSpace N) ι} (hS : InS d M) :
    InS (d - 1) (M.sup (Idm (d - 1) ι)) :=
  ⟨hS.coh.sup (Idm_isCoherentOn_puncture _), hS.inv.sup (isConeInvariant_Idm _),
    GermModule.le_sup_right hS.coh⟩

/-- The subquotient `M/I_{L_d}` of a member of `𝒮_d`. -/
def sqOf {d : ℕ} {M : GermModule (ConeSpace N) ι} (hS : InS d M) :
    Subquotient (ConeSpace N) (puncture (ConeSpace N)) :=
  Sd d M hS.coh hS.le

theorem sqOf_isInvariant {d : ℕ} {M : GermModule (ConeSpace N) ι} (hS : InS d M) :
    IsInvariantSubquotient (sqOf hS) :=
  ⟨hS.inv, isConeInvariant_Idm d⟩

/-- `Ȟ¹((M/I_{L_d})(n))` is finite-dimensional, `d ≤ N`. -/
theorem finiteDimensional_cechH_one_Sd' {d : ℕ} (hd : d ≤ N) {M : GermModule (ConeSpace N) ι}
    (hS : InS d M) (n : ℤ) : FiniteDimensional ℂ (cechH (coverSystem (sqOf hS) n 1) 1) := by
  rcases lt_or_eq_of_le hd with hd | hdN
  · exact finiteDimensional_cechH_one_Sd hd hS.coh hS.inv hS.le le_rfl n
  · subst hdN
    have hb := cechHMap_bijective_of_eqOn (M := M) (I := GermModule.bot _ ι) (M' := M)
      (I' := Idm d ι) (hM := hS.coh) (hI := GermModule.bot_isCoherentOn _)
      (hle := GermModule.bot_le hS.coh) (hM' := hS.coh) (hI' := Idm_isCoherentOn_puncture d)
      (hle' := hS.le) (fun _ _ _ => Iff.rfl) Idm_N_eqOn_bot n 1 1
    have : FiniteDimensional ℂ (cechH (coverSystem (mkSq M (GermModule.bot _ ι) hS.coh
        (GermModule.bot_isCoherentOn _) (GermModule.bot_le hS.coh)) n 1) 1) :=
      finiteDimensional_cechH_one_subSq hS.coh hS.inv (ρ := 1) le_rfl n
    exact Module.Finite.of_surjective _ hb.2

/-! ### The chain `G_k = (M : z_d^k)/I_{L_d}` -/

section Chain

variable {d : ℕ} (hd : d < N + 1) {M : GermModule (ConeSpace N) ι} (hS : InS d M)

/-- `G_k = (M : z_d^k)/I_{L_d}`. -/
def chainG (k : ℕ) : Subquotient (ConeSpace N) (puncture (ConeSpace N)) :=
  sqOf (hS.satChain ⟨d, hd⟩ k)

/-- `Q_k = (M : z_d^k + I_{L_{d-1}})/I_{L_{d-1}}`. -/
def chainQ (k : ℕ) : Subquotient (ConeSpace N) (puncture (ConeSpace N)) :=
  sqOf (hS.satChain ⟨d, hd⟩ k).sup_pred

/-- Multiplication by `z_d`, `G_{k+1}(-1) → G_k`. -/
def chainPhi (k : ℕ) : Subquotient.Hom (chainG hd hS (k + 1)) (chainG hd hS k) where
  A := scalMat ι ⟨d, hd⟩
  holAt x hx i j := (isHomMatrix_scalMat (ι := ι) ⟨d, hd⟩).holAt x hx i j
  map_M _ _ _ ha := ha.2
  map_N _ _ _ ha := Idm_mem_scal _ ha

/-- The projection `G_k → Q_k`. -/
def chainPsi (k : ℕ) : Subquotient.Hom (chainG hd hS k) (chainQ hd hS k) where
  A := idMatrix ι
  holAt x _ := holAt_idMatrix x
  map_M y hy _ ha := mem_matApply_idMatrix.2
    (GermModule.le_sup_left (Idm_isCoherentOn_puncture _) y hy _ ha)
  map_N y hy _ ha := mem_matApply_idMatrix.2 (Idm_le_Idm (Nat.sub_le d 1) _ y hy _ ha)

theorem chainPhi_isHom (k : ℕ) : IsHomMatrix (chainPhi hd hS k).A 1 :=
  isHomMatrix_scalMat _

theorem chainPsi_isHom (k : ℕ) : IsHomMatrix (chainPsi hd hS k).A 0 :=
  isHomMatrix_idMatrix

/-- The hyperplane sequences of the chain. -/
theorem chain_shortExact (hd1 : 1 ≤ d) (k : ℕ) :
    Subquotient.ShortExact (chainPhi hd hS k) (chainPsi hd hS k) := by
  have hk := hS.satChain ⟨d, hd⟩ k
  have hk1 := hS.satChain ⟨d, hd⟩ (k + 1)
  obtain ⟨φ, ψ, hφA, hψA, hex⟩ : ∃ (φ : Subquotient.Hom (chainG hd hS (k + 1)) (chainG hd hS k))
      (ψ : Subquotient.Hom (chainG hd hS k) (chainQ hd hS k)),
      φ.A = scalMat ι ⟨d, hd⟩ ∧ ψ.A = idMatrix ι ∧ Subquotient.ShortExact φ ψ :=
    shortExact_hyperplane (M := satChain M ⟨d, hd⟩ k) (M' := satChain M ⟨d, hd⟩ (k + 1))
      (M'' := (satChain M ⟨d, hd⟩ k).sup (Idm (d - 1) ι)) (I := Idm d ι) (I' := Idm (d - 1) ι)
      hd hd1 hk.coh hk1.coh hk.sup_pred.coh (Idm_isCoherentOn_puncture d)
      (Idm_isCoherentOn_puncture _) (fun _ _ _ => Iff.rfl) (fun _ _ _ => Iff.rfl) hk.le
      (fun _ _ _ => Iff.rfl) (fun _ _ _ => Iff.rfl) hk1.le hk.le hk.sup_pred.le
  have e1 : φ = chainPhi hd hS k := by
    cases φ
    cases hφA
    rfl
  have e2 : ψ = chainPsi hd hS k := by
    cases ψ
    cases hψA
    rfl
  rw [← e1, ← e2]
  exact hex

/-- The inclusion `G_k → G_{k'}` (`k ≤ k'`). -/
def chainIncl {k k' : ℕ} (h : k ≤ k') : Subquotient.Hom (chainG hd hS k) (chainG hd hS k') :=
  idHomSq (satChain_le_succ_iter _ hS.coh h) (GermModule.LeOn.refl _ _)

/-- Multiplication by `z_d`, `G_{k+1}(-1) → G_{k'}` (`k ≤ k'`). -/
def chainScal {k k' : ℕ} (h : k ≤ k') :
    Subquotient.Hom (chainG hd hS (k + 1)) (chainG hd hS k') where
  A := scalMat ι ⟨d, hd⟩
  holAt x hx i j := (isHomMatrix_scalMat (ι := ι) ⟨d, hd⟩).holAt x hx i j
  map_M y hy _ ha := satChain_le_succ_iter _ hS.coh h y hy _ ha.2
  map_N _ _ _ ha := Idm_mem_scal _ ha

/-- Multiplication by `z_d` on `G_k`, `G_k(-1) → G_k`. -/
def chainZ (k : ℕ) : Subquotient.Hom (chainG hd hS k) (chainG hd hS k) where
  A := scalMat ι ⟨d, hd⟩
  holAt x hx i j := (isHomMatrix_scalMat (ι := ι) ⟨d, hd⟩).holAt x hx i j
  map_M y hy _ ha := (satChain_mono ⟨d, hd⟩ hS.coh k y hy _ ha).2
  map_N _ _ _ ha := Idm_mem_scal _ ha

theorem chainZ_isHom (k : ℕ) : IsHomMatrix (chainZ hd hS k).A 1 :=
  isHomMatrix_scalMat _

theorem chainScal_isHom {k k' : ℕ} (h : k ≤ k') : IsHomMatrix (chainScal hd hS h).A 1 :=
  isHomMatrix_scalMat _

/-- The Čech map induced by multiplication by `z_d` on `G_k`. -/
abbrev chainZH (k : ℕ) (n : ℤ) :=
  (cechHMap (coverHom' (chainZ hd hS k) (chainZ_isHom hd hS k) (rfl : n + 1 = n + 1) 1) 1).hom

/-- The Čech map induced by multiplication by `z_d`, `G_{k+1}(-1) → G_{k'}`. -/
abbrev chainScalH {k k' : ℕ} (h : k ≤ k') (n : ℤ) :=
  (cechHMap (coverHom' (chainScal hd hS h) (chainScal_isHom hd hS h) (rfl : n + 1 = n + 1) 1)
    1).hom

/-- The degree-one Čech map induced by multiplication by `z_d`, `Ȟ¹(G_{k+1}(n)) → Ȟ¹(G_k(n+1))`. -/
abbrev chainPhiH (k : ℕ) (n : ℤ) :=
  (cechHMap (coverHom (chainPhi hd hS k) (chainPhi_isHom hd hS k) n 1) 1).hom

/-- The Čech map induced by the inclusion `G_k → G_{k'}`. -/
abbrev chainInclH {k k' : ℕ} (h : k ≤ k') (n : ℤ) (q : ℕ) :=
  (cechHMap (coverHom' (chainIncl hd hS h) isHomMatrix_idMatrix (add_zero n) 1) q).hom

theorem chainInclH_bijective_self (k : ℕ) (n : ℤ) (q : ℕ) :
    Function.Bijective (chainInclH hd hS (le_refl k) n q) :=
  cechHMap_bijective_of_eqOn (M := satChain M ⟨d, hd⟩ k) (I := Idm d ι)
    (M' := satChain M ⟨d, hd⟩ k) (I' := Idm d ι) (fun _ _ _ => Iff.rfl) (fun _ _ _ => Iff.rfl)
    n 1 q

/-- `Φ_k` is onto in the degrees where `Ȟ¹(Q_k(n+1)) = 0`. -/
theorem chainPhiH_surjective (hd1 : 1 ≤ d) (k : ℕ) (n : ℤ)
    (hQ : Subsingleton (cechH (coverSystem (chainQ hd hS k) (n + 1 + 0) 1) 1)) :
    Function.Surjective (chainPhiH hd hS k n) := by
  intro y
  have hles := coverSystem_les (Laurent.sectionsDecompose_coverSet_all 1)
    (sqOf_isInvariant (hS.satChain ⟨d, hd⟩ (k + 1))) (sqOf_isInvariant (hS.satChain ⟨d, hd⟩ k))
    (sqOf_isInvariant (hS.satChain ⟨d, hd⟩ k).sup_pred) (chainPhi_isHom hd hS k)
    (chainPsi_isHom hd hS k) (chain_shortExact hd hS hd1 k) n 1
  exact (hles.2.1 y).1 (@Subsingleton.elim _ hQ _ _)

/-- `ι_k ∘ Φ_k = χ_k` with `χ_k` multiplication by `z_d`, `G_{k+1}(-1) → G_{k'}`. -/
theorem chain_square_left {k k' : ℕ} (h : k ≤ k') (n : ℤ)
    (x : cechH (coverSystem (chainG hd hS (k + 1)) n 1) 1) :
    chainScalH hd hS h n x = chainInclH hd hS h (n + 1) 1 (chainPhiH hd hS k n x) :=
  cechHMap_coverHom'_comp (chainPhi hd hS k) (chainIncl hd hS h) (chainScal hd hS h)
    (chainPhi_isHom hd hS k) isHomMatrix_idMatrix (chainScal_isHom hd hS h) rfl (add_zero _) rfl
    (fun _ => (matApply_idMatrix _).symm) 1 x

/-- `Z_{k'} ∘ ι_{k+1} = χ_k`. -/
theorem chain_square_right {k k' : ℕ} (h : k ≤ k') (h' : k + 1 ≤ k') (n : ℤ)
    (x : cechH (coverSystem (chainG hd hS (k + 1)) n 1) 1) :
    chainScalH hd hS h n x = chainZH hd hS k' n (chainInclH hd hS h' n 1 x) :=
  cechHMap_coverHom'_comp (chainIncl hd hS h') (chainZ hd hS k') (chainScal hd hS h)
    isHomMatrix_idMatrix (chainZ_isHom hd hS k') (chainScal_isHom hd hS h) (add_zero _) rfl rfl
    (fun a => congrArg (matApply (scalMat ι ⟨d, hd⟩)) (matApply_idMatrix a).symm) 1 x

/-- `Z_{k₀} = Φ_{k₀} ∘ ι` with `ι : G_{k₀} → G_{k₀+1}`. -/
theorem chain_square_top (k : ℕ) (n : ℤ) (x : cechH (coverSystem (chainG hd hS k) n 1) 1) :
    chainZH hd hS k n x = chainPhiH hd hS k n (chainInclH hd hS (Nat.le_succ k) n 1 x) :=
  cechHMap_coverHom'_comp (chainIncl hd hS (Nat.le_succ k)) (chainPhi hd hS k) (chainZ hd hS k)
    isHomMatrix_idMatrix (chainPhi_isHom hd hS k) (chainZ_isHom hd hS k) (add_zero _) rfl rfl
    (fun a => congrArg (matApply (scalMat ι ⟨d, hd⟩)) (matApply_idMatrix a).symm) 1 x

/-- **Injectivity along the chain.** Assume `Ȟ¹(Q_k(m)) = 0` for `m ≫ 0` and every `k`, and let
`G_{k₀+1} = G_{k₀}` stalkwise. Then there is `n₂` such that multiplication by `z_d`,
`Ȟ¹(G_{k+1}(n)) → Ȟ¹(G_k(n+1))`, is injective (indeed bijective) for all `k ≤ k₀` and
`n ≥ n₂`. -/
theorem chain_injective (hd1 : 1 ≤ d) (hdN : d ≤ N) {k₀ : ℕ}
    (hstab : (satChain M ⟨d, hd⟩ (k₀ + 1)).EqOn (satChain M ⟨d, hd⟩ k₀) (puncture (ConeSpace N)))
    (hB : ∀ k, ∃ m₀ : ℤ, ∀ m ≥ m₀,
      Subsingleton (cechH (coverSystem (chainQ hd hS k) m 1) 1)) :
    ∃ n₂ : ℤ, ∀ k ≤ k₀, ∀ n ≥ n₂, Function.Injective (chainPhiH hd hS k n) := by
  classical
  choose mB hmB using hB
  have hfin : ∀ k n, FiniteDimensional ℂ (cechH (coverSystem (chainG hd hS k) n 1) 1) :=
    fun k n => finiteDimensional_cechH_one_Sd' hdN (hS.satChain ⟨d, hd⟩ k) n
  have hsurj : ∀ k (n : ℤ), mB k ≤ n + 1 → Function.Surjective (chainPhiH hd hS k n) :=
    fun k n hn => chainPhiH_surjective hd hS hd1 k n (hmB k _ (by simpa using hn))
  -- the inclusion `G_{k₀} → G_{k₀+1}` is bijective
  have hι₀ : ∀ t, Function.Bijective (chainInclH hd hS (Nat.le_succ k₀) t 1) := fun t =>
    cechHMap_bijective_of_eqOn (M := satChain M ⟨d, hd⟩ k₀) (I := Idm d ι)
      (M' := satChain M ⟨d, hd⟩ (k₀ + 1)) (I' := Idm d ι) hstab.symm (fun _ _ _ => Iff.rfl) t 1 1
  -- the dimensions of `Ȟ¹(G_{k₀}(n))` are eventually constant
  let a : ℤ → ℕ := fun n => finrank ℂ (cechH (coverSystem (chainG hd hS k₀) n 1) 1)
  have ha : ∀ n, finrank ℂ (cechH (coverSystem (chainG hd hS (k₀ + 1)) n 1) 1) = a n :=
    fun n => (finrank_eq_of_bijective' _ (hι₀ n)).symm
  have hanti : ∀ n ≥ mB k₀ - 1, a (n + 1) ≤ a n := fun n hn => by
    have := finrank_le_of_surjective' _ (hsurj k₀ n (by omega))
    rwa [ha n] at this
  obtain ⟨n₁, hn₁0, hn₁⟩ := eventually_const_of_antitone a _ hanti
  have hbij₀ : ∀ n ≥ n₁, Function.Bijective (chainPhiH hd hS k₀ n) := fun n hn => by
    have hs := hsurj k₀ n (by omega)
    have := hfin (k₀ + 1) n
    have := hfin k₀ (n + 1)
    exact ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      ((ha n).trans (hn₁ n hn).symm)).2 hs, hs⟩
  have hZ : ∀ n ≥ n₁, Function.Bijective (chainZH hd hS k₀ n) := fun n hn => by
    have h := (hbij₀ n hn).comp (hι₀ n)
    have e : chainZH hd hS k₀ n = chainPhiH hd hS k₀ n ∘ chainInclH hd hS (Nat.le_succ k₀) n 1 :=
      funext fun x => chain_square_top hd hS k₀ n x
    rw [e]
    exact h
  -- one step down the chain
  have hstep : ∀ k (hk : k + 1 ≤ k₀) (n' : ℤ),
      (∀ n ≥ n', Function.Bijective (chainInclH hd hS hk n 1)) →
      ∀ m ≥ max n' n₁, mB k ≤ m + 1 → Function.Injective (chainPhiH hd hS k m) ∧
        Function.Bijective (chainInclH hd hS (Nat.le_of_succ_le hk) (m + 1) 1) := by
    intro k hk n' hι m hm hmB
    have hcomp : Function.Bijective (chainInclH hd hS (Nat.le_of_succ_le hk) (m + 1) 1 ∘
        chainPhiH hd hS k m) := by
      have e : chainInclH hd hS (Nat.le_of_succ_le hk) (m + 1) 1 ∘ chainPhiH hd hS k m =
          chainZH hd hS k₀ m ∘ chainInclH hd hS hk m 1 := funext fun x =>
        (chain_square_left hd hS (Nat.le_of_succ_le hk) m x).symm.trans
          (chain_square_right hd hS (Nat.le_of_succ_le hk) hk m x)
      rw [e]
      exact (hZ m (le_trans (le_max_right _ _) hm)).comp (hι m (le_trans (le_max_left _ _) hm))
    have hs := hsurj k m hmB
    refine ⟨hcomp.1.of_comp, ?_, ?_⟩
    · intro u v huv
      obtain ⟨u', rfl⟩ := hs u
      obtain ⟨v', rfl⟩ := hs v
      exact congrArg _ (hcomp.1 huv)
    · exact hcomp.2.of_comp
  have hdesc : ∀ j : ℕ, ∃ n' : ℤ, ∀ k (hk : k ≤ k₀), k₀ - j ≤ k → ∀ n ≥ n',
      Function.Bijective (chainInclH hd hS hk n 1) ∧ Function.Injective (chainPhiH hd hS k n) := by
    intro j
    induction j with
    | zero =>
      refine ⟨n₁, fun k hk hkj n hn => ?_⟩
      obtain rfl : k = k₀ := by omega
      exact ⟨chainInclH_bijective_self hd hS k n 1, (hbij₀ n hn).1⟩
    | succ j ih =>
      obtain ⟨n', hn'⟩ := ih
      refine ⟨max (max n' n₁) (mB (k₀ - (j + 1)) - 1) + 1, fun k hk hkj n hn => ?_⟩
      by_cases hkj' : k₀ - j ≤ k
      · exact hn' k hk hkj' n (by omega)
      · have hk1 : k + 1 ≤ k₀ := by omega
        have hkeq : k = k₀ - (j + 1) := by omega
        have hι : ∀ n ≥ n', Function.Bijective (chainInclH hd hS hk1 n 1) := fun n hn =>
          (hn' (k + 1) hk1 (by omega) n hn).1
        have hmB : ∀ m ≥ n - 1, mB k ≤ m + 1 := fun m hm => by
          subst hkeq
          omega
        refine ⟨?_, (hstep k hk1 n' hι n (by omega) (hmB n (by omega))).1⟩
        obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
        exact (hstep k hk1 n' hι m (by omega) (hmB m (by omega))).2
  obtain ⟨n', hn'⟩ := hdesc k₀
  exact ⟨n', fun k hk n hn => (hn' k hk (by omega) n hn).2⟩

/-- **Surjectivity on `Ȟ⁰`**: if multiplication by `z_d`, `Ȟ¹(G_{k+1}(n)) → Ȟ¹(G_k(n+1))`, is
injective, then `Ȟ⁰(G_k(n+1)) → Ȟ⁰(Q_k(n+1))` is onto. -/
theorem chain_H0_surjective (hd1 : 1 ≤ d) (k : ℕ) (n : ℤ)
    (hinj : Function.Injective (chainPhiH hd hS k n)) :
    Function.Surjective
      (cechHMap (coverHom (chainPsi hd hS k) (chainPsi_isHom hd hS k) (n + 1) 1) 0).hom := by
  intro y
  obtain ⟨-, -, h3, h4⟩ := coverSystem_les (Laurent.sectionsDecompose_coverSet_all 1)
    (sqOf_isInvariant (hS.satChain ⟨d, hd⟩ (k + 1))) (sqOf_isInvariant (hS.satChain ⟨d, hd⟩ k))
    (sqOf_isInvariant (hS.satChain ⟨d, hd⟩ k).sup_pred) (chainPhi_isHom hd hS k)
    (chainPsi_isHom hd hS k) (chain_shortExact hd hS hd1 k) n 0
  exact (h3 y).1 (hinj (((h4 _).2 ⟨y, rfl⟩).trans (map_zero _).symm))

end Chain

end SGPT.GAGA.PN
