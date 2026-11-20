import SGPT.GAGA.SerreM5Step

/-!
# Serre's theorems on `ℙᴺ`: Theorem B from Theorem A

Towards source `lma:GAGA` (`chapter_NApotential.tex`, lines 1143--1145), milestone M4.2.

Let `d ≤ N` and assume Theorem A for the class `𝒮_d` (`SerreA N d`). For `M ∈ 𝒮_d`, global
sections `σ_k` of `M(m₁)` generating `M` modulo `I_{L_d}` give a presentation
`0 → K/I_{L_d} → 𝒪_{L_d}^μ(-m₁) → M/I_{L_d} → 0` (`presHom`, `presHom_surjective`) whose kernel
is again in `𝒮_d` (Oka's theorem: kernels of morphisms of coherent sheaves are coherent). Since
`Ȟ^q(𝒪_{L_d}(n)^μ) = 0` for `q ≥ 1`, `n ≥ -d` (`cechH_OL_subsingleton'`), the long exact sequence
gives `Ȟ^q(M/I_{L_d}(n + m₁)) ↪ Ȟ^{q+1}(K/I_{L_d}(n))`, and descending induction on `q` (the cover
has `N + 1` sets) gives Theorem B for `𝒮_d` (`serreB_of_serreA`).

Blueprint: `claude-serre-m5.tex`, node `claude-serre-m5:theorem-B`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Set Filter Topology
open SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.OkaRelationSheaf
open SGPT.GAGA.Core

noncomputable section

namespace SGPT.GAGA.PN

variable {N : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]

section Presentation

variable {d : ℕ} {M : GermModule (ConeSpace N) ι} (hS : InS d M) {μ : Type} [Fintype μ]
  [DecidableEq μ] {m₁ : ℤ} {σ : μ → ι → ConeSpace N → ℂ} (hσ : GlobSec M m₁ σ)

include hσ in
theorem isHomMatrix_colMatrix : IsHomMatrix (colMatrix σ) m₁ :=
  ⟨fun _ hx i j => holAt_of_differentiableOn isOpen_ne ((hσ.1 j).diff i) hx,
    fun z hz c hc i j => (hσ.1 j).hom z hz c hc i⟩

/-- The presentation `𝒪_{L_d}^μ(-m₁) → M/I_{L_d}`, `c ↦ ∑ c_k σ_k`. -/
def presHom : Subquotient.Hom (OL (N := N) d μ) (sqOf hS) where
  A := colMatrix σ
  holAt x hx i j := (isHomMatrix_colMatrix hσ).holAt x hx i j
  map_M y hy a ha := by
    have hM := hS.coh y hy
    exact hM.congr_mem (hM.finset_sum_mem Finset.univ fun k _ => hM.smul_mem (ha k) (hσ.2 k y hy))
      fun j => Eventually.of_forall fun z => (matApply_colMatrix σ a j z).symm
  map_N y hy a ha := by
    have ha' := mem_Idm_iff.1 (show (Idm d μ).mem y a from ha)
    show (Idm d ι).mem y (matApply (colMatrix σ) a)
    refine mem_Idm_iff.2 ⟨HolTupleAt.matApply (fun i j => (isHomMatrix_colMatrix hσ).holAt y hy i j)
      ha'.1, ?_⟩
    filter_upwards [ha'.2] with z hz hzL i
    exact (matApply_colMatrix σ a i z).trans
      (Finset.sum_eq_zero fun k _ => by rw [hz hzL k, zero_mul])

/-- The presentation is onto when the `σ_k` generate `M` modulo `I_{L_d}`. -/
theorem presHom_surjective (hgen : ∀ y : ConeSpace N, y ≠ 0 → GenAt M (Idm d ι) σ y) :
    Subquotient.Surjective (presHom hS hσ) := by
  refine GermModule.LeOn.antisymm (GermModule.sup_le hS.coh hS.le
    (GermModule.map_le hS.coh (presHom hS hσ).map_M)) fun y hy a ha => ?_
  obtain ⟨c, hc, hca⟩ := hgen y hy a ha
  refine ⟨fun j z => a j z - ∑ k, c k z * σ k j z, fun j z => ∑ k, c k z * σ k j z, hca,
    ⟨c, hc, fun j => Eventually.of_forall fun z => (matApply_colMatrix σ c j z).symm⟩,
    fun j => Eventually.of_forall fun z => ?_⟩
  show a j z = (a j z - ∑ k, c k z * σ k j z) + ∑ k, c k z * σ k j z
  ring

end Presentation

/-- **Theorem B from Theorem A** for the class `𝒮_d`. -/
theorem serreB_of_serreA {d : ℕ} (hdN : d ≤ N) (hA : SerreA N d) : SerreB N d := by
  have hX : OkaProperty (ConeSpace N) := okaProperty_of_finiteDimensional _
  suffices H : ∀ i q : ℕ, N + 1 ≤ q + i → 1 ≤ q → ∀ (ι : Type) [Fintype ι] [DecidableEq ι]
      (M : GermModule (ConeSpace N) ι) (hS : InS d M), ∃ m₀ : ℤ, ∀ m ≥ m₀,
        Subsingleton (cechH (coverSystem (sqOf hS) m 1) q) from
    fun q hq => H (N + 1) q (by omega) hq
  intro i
  induction i with
  | zero =>
    intro q hq _ ι _ _ M hS
    exact ⟨0, fun m _ => coverSystem_cechH_subsingleton (F := sqOf hS) m 1 (by omega)⟩
  | succ i ih =>
    intro q hqi hq ι _ _ M hS
    classical
    obtain ⟨m₁, hm₁⟩ := hA ι M hS
    obtain ⟨μ, _, σ, hσ, hgen⟩ := hm₁ m₁ le_rfl
    have hψ : IsHomMatrix (presHom hS hσ).A m₁ := isHomMatrix_colMatrix hσ
    have hK : InS d (Subquotient.ker hX (presHom hS hσ)).M :=
      ⟨(Subquotient.ker hX (presHom hS hσ)).coherent_M,
        isConeInvariant_top.inf ((isConeInvariant_Idm d).comap (Idm_isCoherentOn_puncture d) hψ),
        (Subquotient.ker hX (presHom hS hσ)).le⟩
    obtain ⟨mK, hmK⟩ := ih (q + 1) (by omega) (by omega) μ _ hK
    refine ⟨m₁ + max (-(d : ℤ)) mK, fun m hm => ?_⟩
    have hmax1 := le_max_left (-(d : ℤ)) mK
    have hmax2 := le_max_right (-(d : ℤ)) mK
    have hses : Subquotient.ShortExact (Subquotient.kerι (hX := hX) (presHom hS hσ))
        (presHom hS hσ) :=
      ⟨Subquotient.injective_kerι _, Subquotient.exact_kerι _,
        presHom_surjective hS hσ fun y hy => hgen y hy⟩
    have hles := coverSystem_les (Laurent.sectionsDecompose_coverSet_all 1)
      (F := Subquotient.ker hX (presHom hS hσ)) ⟨hK.inv, isConeInvariant_Idm d⟩
      (OL_isInvariant d) (sqOf_isInvariant hS) isHomMatrix_idMatrix hψ hses (m - m₁) q
    have hOL : Subsingleton (cechH (coverSystem (OL (N := N) d μ) (m - m₁ + 0) 1) q) :=
      cechH_OL_subsingleton' le_rfl hdN hq (by omega)
    have hKs : Subsingleton (cechH (coverSystem (Subquotient.ker hX (presHom hS hσ)) (m - m₁) 1)
        (q + 1)) := hmK (m - m₁) (by omega)
    have hsub : Subsingleton (cechH (coverSystem (sqOf hS) (m - m₁ + 0 + m₁) 1) q) := by
      refine subsingleton_of_forall_eq 0 fun y => ?_
      obtain ⟨x', hx'⟩ := (hles.2.2.1 y).1 (Subsingleton.elim _ _)
      rw [← hx', Subsingleton.elim x' 0, map_zero]
    have e : m - m₁ + 0 + m₁ = m := by ring
    rw [e] at hsub
    exact hsub

end SGPT.GAGA.PN
