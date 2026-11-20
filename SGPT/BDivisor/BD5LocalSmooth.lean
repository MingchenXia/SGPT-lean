import SGPT.Projective.PrincipalCotangentRank

/-!
# quotients by relations with independent differentials (Jacobian criterion)

Source: `rmk:bdiv:L749` (algebraization of the book's blow-up models; Jacobian criterion).

Let `A` be a formally smooth `k`-algebra with finite free differentials, `B = A / (g₁, …, g_c)`
a local quotient and `K` a field receiving `B` (the residue field of a point).  If there are
`k`-derivations `D₁, …, D_c : A → K` with `Dᵢ(g_j) = δᵢⱼ` (the differentials of the relations at
the point are linearly independent), then

* `formallySmooth_of_relations_derivations_bd5`: `B` is formally smooth over `k`;
* `cotangent_finrank_of_relations_derivations_bd5`: `dim_K K ⊗_B Ω_{B/k} = rank Ω_{A/k} - c`.

This generalizes the one-relation case `PrincipalCotangentSmooth` / `PrincipalCotangentRank` to
`c` relations (the local form of the Jacobian criterion used for the algebraization of
projective submanifolds, `BD5Algebraization`).
-/

set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace SGPT.BDivisor.BD5

open TensorProduct KaehlerDifferential IsLocalRing Module
open scoped TensorProduct

section Span

variable {A K : Type} [CommRing A] [Field K] [Algebra A K]

/-- The generators of an ideal given by a finite family. -/
def relationGenerator {c : ℕ} (I : Ideal A) (g : Fin c → A) (hI : I = Ideal.span (Set.range g))
    (j : Fin c) : I :=
  ⟨g j, by rw [hI]; exact Ideal.subset_span ⟨j, rfl⟩⟩

/-- Every vector of `K ⊗_A I` is a `K`-combination of the `1 ⊗ g_j`. -/
theorem tensor_ideal_span_bd5 {c : ℕ} (I : Ideal A) (g : Fin c → A)
    (hI : I = Ideal.span (Set.range g)) (x : K ⊗[A] I) :
    ∃ a : Fin c → K, x = ∑ j, a j • ((1 : K) ⊗ₜ[A] relationGenerator I g hI j) := by
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul a b =>
      have hbI : b.val ∈ Ideal.span (Set.range g) := hI ▸ b.property
      obtain ⟨d, hd⟩ := (Ideal.mem_span_range_iff_exists_fun).mp hbI
      have hb : b = ∑ j, d j • relationGenerator I g hI j := by
        apply Subtype.ext
        rw [← hd]
        simp [relationGenerator, smul_eq_mul]
      refine ⟨fun j => d j • a, ?_⟩
      rw [hb, TensorProduct.tmul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [TensorProduct.tmul_smul]
      simp only [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  | add x y hx hy =>
      obtain ⟨a, rfl⟩ := hx
      obtain ⟨b, rfl⟩ := hy
      exact ⟨a + b, by simp [add_smul, Finset.sum_add_distrib]⟩

end Span

section LocalQuotient

variable {k A B K : Type} [CommRing k] [CommRing A] [CommRing B] [Field K]
  [Algebra k A] [Algebra A B] [Algebra k B] [IsScalarTower k A B]
  [Algebra B K] [Algebra A K] [Algebra k K]
  [IsScalarTower A B K] [IsScalarTower k A K]

/-- The evaluation of the derivations on base-changed differentials. -/
def derivationsEval {c : ℕ} (D : Fin c → Derivation k A K) :
    K ⊗[A] Ω[A⁄k] →ₗ[K] (Fin c → K) :=
  LinearMap.pi fun i => (D i).liftKaehlerDifferential.liftBaseChange K

omit [Algebra k B] [IsScalarTower k A B] in
theorem derivationsEval_cotangent {c : ℕ}
    (g : Fin c → A) (hI : RingHom.ker (algebraMap A B) = Ideal.span (Set.range g))
    (D : Fin c → Derivation k A K) (j : Fin c) :
    derivationsEval D (cotangentComplexBaseChange k B A K
      ((1 : K) ⊗ₜ[A] relationGenerator (RingHom.ker (algebraMap A B)) g hI j)) =
      fun i => D i (g j) := by
  funext i
  simp only [derivationsEval, LinearMap.pi_apply, cotangentComplexBaseChange_tmul, one_smul,
    kerToTensor_apply, LinearMap.liftBaseChange_tmul, Derivation.liftKaehlerDifferential_comp_D,
    relationGenerator]

omit [Algebra k B] [IsScalarTower k A B] in
/-- With derivations dual to the relations, the base-changed conormal map is injective. -/
theorem cotangentComplexBaseChange_injective_bd5 {c : ℕ}
    (g : Fin c → A) (hI : RingHom.ker (algebraMap A B) = Ideal.span (Set.range g))
    (D : Fin c → Derivation k A K) (hD : ∀ i j, D i (g j) = if i = j then 1 else 0) :
    Function.Injective (cotangentComplexBaseChange k B A K) := by
  have hz : ∀ x, cotangentComplexBaseChange k B A K x = 0 → x = 0 := by
    intro x hx
    obtain ⟨a, rfl⟩ := tensor_ideal_span_bd5 (RingHom.ker (algebraMap A B)) g hI x
    have h := congrArg (derivationsEval D) hx
    rw [map_sum, map_sum, map_zero] at h
    have ha : a = 0 := by
      funext i
      have hi := congrFun h i
      simp only [map_smul, derivationsEval_cotangent g hI D, Finset.sum_apply,
        Pi.smul_apply, hD, smul_eq_mul, mul_ite, mul_one, mul_zero, Pi.zero_apply,
        Finset.sum_ite_eq, Finset.mem_univ, if_true] at hi
      simpa using hi
    simp [ha]
  intro x y hxy
  apply sub_eq_zero.mp
  apply hz
  rw [map_sub, hxy, sub_self]

omit [Algebra k B] [IsScalarTower k A B] in
/-- The base-changed generators form a basis-like family: `dim_K (K ⊗_A I) = c`. -/
theorem finrank_tensor_ker_bd5 {c : ℕ}
    (g : Fin c → A) (hI : RingHom.ker (algebraMap A B) = Ideal.span (Set.range g))
    (D : Fin c → Derivation k A K) (hD : ∀ i j, D i (g j) = if i = j then 1 else 0) :
    finrank K (K ⊗[A] RingHom.ker (algebraMap A B)) = c := by
  let v : Fin c → K ⊗[A] RingHom.ker (algebraMap A B) :=
    fun j => (1 : K) ⊗ₜ[A] relationGenerator (RingHom.ker (algebraMap A B)) g hI j
  have hli : LinearIndependent K v := by
    rw [Fintype.linearIndependent_iff]
    intro a ha i
    have h := congrArg (fun x => derivationsEval D (cotangentComplexBaseChange k B A K x)) ha
    simp only [map_sum, map_smul, map_zero, v, derivationsEval_cotangent g hI D] at h
    have hi := congrFun h i
    simp only [Finset.sum_apply, Pi.smul_apply, hD, smul_eq_mul, mul_ite, mul_one, mul_zero,
      Pi.zero_apply, Finset.sum_ite_eq, Finset.mem_univ, if_true] at hi
    simpa using hi
  have hsp : Submodule.span K (Set.range v) = ⊤ := by
    apply eq_top_iff.mpr
    intro x _
    obtain ⟨a, rfl⟩ := tensor_ideal_span_bd5 (RingHom.ker (algebraMap A B)) g hI x
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  rw [finrank_eq_card_basis (Basis.mk hli (hsp ▸ le_rfl)), Fintype.card_fin]

variable [Module.Free A Ω[A⁄k]] [Module.Finite A Ω[A⁄k]]

/-- **Jacobian criterion (formal smoothness).**  A local quotient of a formally smooth algebra by
relations whose differentials at the point are independent is formally smooth. -/
theorem formallySmooth_of_relations_derivations_bd5 [Algebra.FormallySmooth k A] [IsLocalRing B]
    {c : ℕ}
    (hAB : Function.Surjective (algebraMap A B))
    (g : Fin c → A) (hI : RingHom.ker (algebraMap A B) = Ideal.span (Set.range g))
    (D : Fin c → Derivation k A K) (hD : ∀ i j, D i (g j) = if i = j then 1 else 0)
    (hBK : maximalIdeal B ≤ RingHom.ker (algebraMap B K)) : Algebra.FormallySmooth k B := by
  have hfg : (RingHom.ker (algebraMap A B)).FG := by
    rw [hI]
    exact Submodule.fg_span (Set.finite_range g)
  exact (Algebra.FormallySmooth.iff_injective_cotangentComplexBaseChange A K hAB hfg hBK).mpr
    (cotangentComplexBaseChange_injective_bd5 g hI D hD)

/-- **Jacobian criterion (dimension).**  `dim_K K ⊗_B Ω_{B/k} = rank Ω_{A/k} - c`. -/
theorem cotangent_finrank_of_relations_derivations_bd5 {c : ℕ}
    (hAB : Function.Surjective (algebraMap A B))
    (g : Fin c → A) (hI : RingHom.ker (algebraMap A B) = Ideal.span (Set.range g))
    (D : Fin c → Derivation k A K) (hD : ∀ i j, D i (g j) = if i = j then 1 else 0) :
    finrank K (K ⊗[B] Ω[B⁄k]) = finrank A Ω[A⁄k] - c := by
  let : Nontrivial A := (algebraMap A K).domain_nontrivial
  let I := RingHom.ker (algebraMap A B)
  let J := cotangentComplexBaseChange k B A K
  have hJ : Function.Injective J := cotangentComplexBaseChange_injective_bd5 g hI D hD
  have hdimI : finrank K (K ⊗[A] I) = c := finrank_tensor_ker_bd5 g hI D hD
  let P : Algebra.Extension k B := { Ring := A, σ := _, algebraMap_σ := Function.surjInv_eq hAB }
  let eV := AlgebraTensorModule.cancelBaseChange A B K K Ω[A⁄k]
  let eI := (AlgebraTensorModule.cancelBaseChange A B K K P.ker).symm ≪≫ₗ
    P.cotangentEquiv.baseChange (A := K)
  let F := P.cotangentComplex.baseChange K
  let G := P.toKaehler.baseChange K
  have hF : Function.Injective F := by
    dsimp only [F]
    rw [P.lTensor_cotangentComplex_eq_cotangentComplexBaseChange K]
    exact eV.symm.injective.comp (hJ.comp eI.symm.injective)
  have hdimC : finrank K (K ⊗[B] P.Cotangent) = c :=
    eI.finrank_eq.symm.trans hdimI
  have hexact : Function.Exact F G := by
    change Function.Exact (P.cotangentComplex.lTensor K) (P.toKaehler.lTensor K)
    exact lTensor_exact K P.exact_cotangentComplex_toKaehler P.toKaehler_surjective
  have hG : Function.Surjective G := LinearMap.lTensor_surjective K P.toKaehler_surjective
  let : Module.Finite K (K ⊗[B] P.CotangentSpace) :=
    Module.Finite.of_surjective eV.symm.toLinearMap eV.symm.surjective
  have hdimV : finrank K (K ⊗[B] P.CotangentSpace) = finrank A Ω[A⁄k] :=
    eV.finrank_eq.trans Module.finrank_baseChange
  have hker : finrank K G.ker = c := by
    rw [hexact.linearMap_ker_eq, LinearMap.finrank_range_of_inj hF, hdimC]
  have hdim := G.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hG, finrank_top, hker, hdimV] at hdim
  omega

end LocalQuotient

end SGPT.BDivisor.BD5
