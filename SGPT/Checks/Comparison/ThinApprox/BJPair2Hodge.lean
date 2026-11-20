import SGPT.Checks.Comparison.ThinApprox.BJPair2Const
import SGPT.Checks.Comparison.BJHodgeInequality

namespace SGPT.NAPotential.BJ
end SGPT.NAPotential.BJ
namespace SGPT.NAPotential.BJ.AppSeq
end SGPT.NAPotential.BJ.AppSeq
namespace SGPT.NAPotential.BJ.FixedRay
end SGPT.NAPotential.BJ.FixedRay
namespace SGPT.NAPotential.BJ.MaxClosure
end SGPT.NAPotential.BJ.MaxClosure
namespace SGPT.NAPotential.BJ.Pair3ClassStability
end SGPT.NAPotential.BJ.Pair3ClassStability
namespace SGPT.NAPotential.BJ.Pair3Div
end SGPT.NAPotential.BJ.Pair3Div
namespace SGPT.NAPotential.BJ.Printed
end SGPT.NAPotential.BJ.Printed
namespace SGPT.NAPotential.BJ.RationalPromotion
end SGPT.NAPotential.BJ.RationalPromotion
namespace SGPT.NAPotential.BJ.SourceDXZPositive
end SGPT.NAPotential.BJ.SourceDXZPositive
namespace SGPT.NAPotential.BJ.SourceDivUnique
end SGPT.NAPotential.BJ.SourceDivUnique
namespace SGPT.NAPotential.BJ.SourceNet
end SGPT.NAPotential.BJ.SourceNet
namespace SGPT.NAPotential.BJ.SourceRationalPromotion
end SGPT.NAPotential.BJ.SourceRationalPromotion
namespace SGPT.NAPotential.BJCycle
end SGPT.NAPotential.BJCycle
namespace SGPT.NAPotential.BJModel
end SGPT.NAPotential.BJModel
namespace SGPT.NAPotential.ThinApprox.BJ
end SGPT.NAPotential.ThinApprox.BJ
namespace SGPT.NAPotential.ThinApprox.BJ.AppSeq
end SGPT.NAPotential.ThinApprox.BJ.AppSeq
namespace SGPT.NAPotential.ThinApprox.BJ.FixedRay
end SGPT.NAPotential.ThinApprox.BJ.FixedRay
namespace SGPT.NAPotential.ThinApprox.BJ.MaxClosure
end SGPT.NAPotential.ThinApprox.BJ.MaxClosure
namespace SGPT.NAPotential.ThinApprox.BJ.Pair3ClassStability
end SGPT.NAPotential.ThinApprox.BJ.Pair3ClassStability
namespace SGPT.NAPotential.ThinApprox.BJ.Pair3Div
end SGPT.NAPotential.ThinApprox.BJ.Pair3Div
namespace SGPT.NAPotential.ThinApprox.BJ.Printed
end SGPT.NAPotential.ThinApprox.BJ.Printed
namespace SGPT.NAPotential.ThinApprox.BJ.SourceDXZPositive
end SGPT.NAPotential.ThinApprox.BJ.SourceDXZPositive
namespace SGPT.NAPotential.ThinApprox.BJ.SourceDivUnique
end SGPT.NAPotential.ThinApprox.BJ.SourceDivUnique
namespace SGPT.NAPotential.ThinApprox.BJ.SourceNet
end SGPT.NAPotential.ThinApprox.BJ.SourceNet
namespace SGPT.NAPotential.ThinApprox.BJCycle
end SGPT.NAPotential.ThinApprox.BJCycle
namespace SGPT.NAPotential.ThinApprox.BJModel
end SGPT.NAPotential.ThinApprox.BJModel


/-!
# The Hodge inequality without the fibre at infinity (lane BJ-PAIR, R5)

Source: [BJ22] (`references/bj22-trivval`), Lemma `lem:Hodge`. Towards
`thm:BJappseq` of `chapter_NApotential.tex`. Blueprint: `claude-bj-pair.tex`.

Lanes BJ-INTERSECT (`interFormQ_sq_nonpos_of_components`) and BJ-HODGE
(`interFormQ_sq_nonpos_of_vertical`) prove the Hodge-type inequality `(D² ⋅ L₁ ⋯ L_{n-1}) ≤ 0` for
vertical `D` assuming a fibre class `P` with two sections with disjoint zero loci (the central fibre
and the fibre at infinity); the second section is only used to see that the components `E_j` of the
central fibre (on a de Jong alteration) are orthogonal to the fibre: `(E_j ⋅ P ⋅ ⋯) = 0`. The copies
below (same proofs, adapted) take the orthogonality as a hypothesis
(`interFormQ_sq_nonpos_of_components_ortho`, `interFormQ_sq_nonpos_of_components_smul_ortho`), and
in `interFormQ_sq_nonpos_of_vertical_ortho` obtain it by cutting along `E_j` (`interFormQ_cut`),
on which `P` is trivial: the hypothesis is that `P` becomes trivial on every scheme mapping into the
zero locus of `s₀`. On a blow-up model `P = 𝒪(𝒳₀)` satisfies it (lane BJ-PAIR's
`picPullbackQ_cartierCentral_eq_zero`, file `BJPair2HodgePair`).
-/

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Scheme.Modules TopologicalSpace
open scoped TensorProduct

universe u

namespace SGPT.NAPotential.ThinApprox.BJ
open SGPT.NAPotential.BJ

open SGPT.Foundations.Envelope SGPT.Foundations.Envelope.SeshadriAmplenessCriterion SGPT.NAPotential.BJIntersect
open SGPT.NAPotential.BJProj SGPT.NAPotential.BJHodge SGPT.Support.Alterations

attribute [local instance] Scheme.Modules.monoidalCategory Scheme.Modules.symmetricCategory

section ortho

variable {k : Type u} [Field k]

/-- **Zariski's lemma for the components of a fibre** (BJ-INTERSECT's
`interFormQ_sq_nonpos_of_components`, with the orthogonality `(E_j ⋅ P ⋅ ⋯) = 0` as hypothesis
instead of a section of `P` at infinity). -/
theorem interFormQ_sq_nonpos_of_components_ortho (m : ℕ) {X : Scheme.{u}} [IsIntegral X]
    [CompactSpace X] [X.IsSeparated] (p : X ⟶ Spec (.of k)) [IsProjective p]
    (hdim : topologicalKrullDim X ≤ (m + 2 : ℕ))
    (P : X.Modules) (hP : IsInvertible P)
    {ι : Type*} [Fintype ι] (E : ι → {E : X.Modules // IsInvertible E})
    (σ : ∀ j, unitObj X ⟶ (E j).1) (hσ : ∀ j, σ j ≠ 0)
    (hint : ∀ j, IsIntegral (LineSectionZeroIdeal.zeroIdeal (E j).1 (E j).2 (σ j)).subscheme)
    (hres : ∀ i j, i ≠ j → restrictSection
      (LineSectionZeroIdeal.zeroIdeal (E i).1 (E i).2 (σ i)).subschemeι (σ j) ≠ 0)
    (b : ι → ℕ) (hb : ∀ j, 0 < b j) (hfib : ∑ j, b j • lineCls (E j) = lineCls ⟨P, hP⟩)
    (hortho : ∀ j (t : Multiset (PicQ X)),
      interFormQ p (m + 2) hdim (unitObj X) (picQ (E j) ::ₘ picQ ⟨P, hP⟩ ::ₘ t) = 0)
    (W : Set X) (hW : ∀ j, ((LineSectionZeroIdeal.zeroIdeal (E j).1 (E j).2 (σ j)).support :
      Set X) ⊆ W)
    (Ns : List {N : X.Modules // IsInvertible N}) (hNs : Ns.length = m)
    (hnef : ∀ N ∈ Ns, IsNefOn p N.1 W) (x : ι → ℚ) :
    interFormQ p (m + 2) hdim (unitObj X)
      ((∑ j, x j • picQ (E j)) ::ₘ (∑ j, x j • picQ (E j)) ::ₘ
        ((Ns.map picQ : List (PicQ X)) : Multiset (PicQ X))) ≤ 0 := by
  classical
  set Φ := interFormQ p (m + 2) hdim (unitObj X) with hΦ
  set t : Multiset (PicQ X) := ((Ns.map picQ : List (PicQ X)) : Multiset (PicQ X)) with ht
  -- the intersection numbers `(E_i · E_j · N)` and `(E_i · P · N)`
  have hval : ∀ A B : {E : X.Modules // IsInvertible E},
      Φ (picQ A ::ₘ picQ B ::ₘ t) =
        mixedEulerDifference p (A.1 :: B.1 :: Ns.map Subtype.val) (unitObj X) := by
    intro A B
    have := interFormQ_picQ p (m + 2) hdim (unitObj X) (A :: B :: Ns) (by simp [hNs])
    simpa [ht] using this
  have hP' : picQ ⟨P, hP⟩ = ∑ j, ((b j : ℚ)) • picQ (E j) := by
    unfold picQ
    rw [← hfib, TensorProduct.tmul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [TensorProduct.tmul_smul, ← Nat.cast_smul_eq_nsmul ℚ]
  refine Φ.sq_nonpos_of_offDiag_nonneg (fun j => picQ (E j)) t (fun j => (b j : ℚ))
    (fun j => by exact_mod_cast hb j) (fun i j hij => ?_) (fun i => ?_) x
  · rw [hval]
    have := mixedEulerDifference_components_nonneg m p hdim (E i).1 (E i).2 (σ i) (hσ i)
      (hint i) (E j).1 (E j).2 (σ j) (hres i j hij) W (hW i) Ns hNs hnef
    exact_mod_cast this
  · rw [← hP']
    exact hortho i t

/-- The same against nonnegative rational multiples of nef line bundles (BJ-INTERSECT's
`interFormQ_sq_nonpos_of_components_smul`, with the orthogonality as hypothesis). -/
theorem interFormQ_sq_nonpos_of_components_smul_ortho (m : ℕ) {X : Scheme.{u}} [IsIntegral X]
    [CompactSpace X] [X.IsSeparated] (p : X ⟶ Spec (.of k)) [IsProjective p]
    (hdim : topologicalKrullDim X ≤ (m + 2 : ℕ))
    (P : X.Modules) (hP : IsInvertible P)
    {ι : Type*} [Fintype ι] (E : ι → {E : X.Modules // IsInvertible E})
    (σ : ∀ j, unitObj X ⟶ (E j).1) (hσ : ∀ j, σ j ≠ 0)
    (hint : ∀ j, IsIntegral (LineSectionZeroIdeal.zeroIdeal (E j).1 (E j).2 (σ j)).subscheme)
    (hres : ∀ i j, i ≠ j → restrictSection
      (LineSectionZeroIdeal.zeroIdeal (E i).1 (E i).2 (σ i)).subschemeι (σ j) ≠ 0)
    (b : ι → ℕ) (hb : ∀ j, 0 < b j) (hfib : ∑ j, b j • lineCls (E j) = lineCls ⟨P, hP⟩)
    (hortho : ∀ j (t : Multiset (PicQ X)),
      interFormQ p (m + 2) hdim (unitObj X) (picQ (E j) ::ₘ picQ ⟨P, hP⟩ ::ₘ t) = 0)
    (W : Set X) (hW : ∀ j, ((LineSectionZeroIdeal.zeroIdeal (E j).1 (E j).2 (σ j)).support :
      Set X) ⊆ W)
    (Ns : List ({N : X.Modules // IsInvertible N} × ℚ)) (hNs : Ns.length = m)
    (hnef : ∀ N ∈ Ns, IsNefOn p N.1.1 W) (hc : ∀ N ∈ Ns, 0 ≤ N.2) (x : ι → ℚ) :
    interFormQ p (m + 2) hdim (unitObj X)
      ((∑ j, x j • picQ (E j)) ::ₘ (∑ j, x j • picQ (E j)) ::ₘ
        ((Ns.map fun N => N.2 • picQ N.1 : List (PicQ X)) : Multiset (PicQ X))) ≤ 0 := by
  have h := (interFormQ p (m + 2) hdim (unitObj X)).map_smul_list Prod.snd (fun N => picQ N.1) Ns
    {∑ j, x j • picQ (E j), ∑ j, x j • picQ (E j)}
  simp only [Multiset.insert_eq_cons, Multiset.cons_add, Multiset.singleton_add] at h
  rw [h]
  refine mul_nonpos_of_nonneg_of_nonpos (List.prod_nonneg fun c hc' => ?_) ?_
  · obtain ⟨N, hN, rfl⟩ := List.mem_map.mp hc'
    exact hc N hN
  · have := interFormQ_sq_nonpos_of_components_ortho m p hdim P hP E σ hσ hint hres b hb
      hfib hortho W hW (Ns.map Prod.fst) (by simpa using hNs)
      (by
        intro N hN
        obtain ⟨M, hM, rfl⟩ := List.mem_map.mp hN
        exact hnef M hM) x
    simpa [List.map_map, Function.comp_def] using this

/-- **The Hodge inequality for vertical divisors** (BJ-HODGE's `interFormQ_sq_nonpos_of_vertical`,
without the fibre at infinity): if `P` has a nonzero section `s₀` and becomes trivial on every
scheme mapping into the zero locus `Z₀` of `s₀`, then `(D² ⋅ N₁ ⋯ N_m) ≤ 0` for every combination
`D` of invertible sheaves with sections vanishing only on `Z₀` and line bundles `Nᵢ` nef on a
set `W ⊇ Z₀`. -/
theorem interFormQ_sq_nonpos_of_vertical_ortho (m : ℕ) {X : Scheme.{u}} [IsIntegral X]
    [CompactSpace X] [X.IsSeparated] (p : X ⟶ Spec (.of k)) [IsProjective p]
    (hdim : topologicalKrullDim X ≤ (m + 2 : ℕ))
    (P : X.Modules) (hP : IsInvertible P) (s₀ : unitObj X ⟶ P) (hs₀ : s₀ ≠ 0)
    (htrivP : ∀ {T : Scheme.{u}} (h : T ⟶ X),
      Set.range h ⊆ (LineSectionZeroIdeal.zeroIdeal P hP s₀).support →
        picPullbackQ h (picQ ⟨P, hP⟩) = 0)
    {κ : Type*} [Fintype κ] (M : κ → {M : X.Modules // IsInvertible M})
    (t : ∀ i, unitObj X ⟶ (M i).1) (ht : ∀ i, t i ≠ 0)
    (hvert : ∀ i, ((LineSectionZeroIdeal.zeroIdeal (M i).1 (M i).2 (t i)).support : Set X) ⊆
      (LineSectionZeroIdeal.zeroIdeal P hP s₀).support)
    (W : Set X) (hW : ((LineSectionZeroIdeal.zeroIdeal P hP s₀).support : Set X) ⊆ W)
    (Ns : List ({N : X.Modules // IsInvertible N} × ℚ)) (hNs : Ns.length = m)
    (hnef : ∀ N ∈ Ns, IsNefOn p N.1.1 W) (hc : ∀ N ∈ Ns, 0 ≤ N.2) (x : κ → ℚ) :
    interFormQ p (m + 2) hdim (unitObj X)
      ((∑ i, x i • picQ (M i)) ::ₘ (∑ i, x i • picQ (M i)) ::ₘ
        ((Ns.map fun N => N.2 • picQ N.1 : List (PicQ X)) : Multiset (PicQ X))) ≤ 0 := by
  classical
  set Z₀ := LineSectionZeroIdeal.zeroIdeal P hP s₀ with hZ₀
  -- (a) the regular model
  have hZne : Z₀.support ≠ ⊤ := by
    obtain ⟨x₀, hx₀⟩ := exists_not_mem_support_zeroIdeal P hP s₀ hs₀
    intro htop
    exact hx₀ (htop ▸ trivial)
  obtain ⟨Y, f, hYint, hYproj, -, hfsurj, hYdim, B, hB, hBsupp⟩ :=
    exists_regular_snc_model p Z₀.support hZne
  have : IsProjective (f ≫ p) := hYproj
  have hpF := ProjectiveFactorizationRingIso.of_isProjective (f ≫ p)
  have : IsProper (f ≫ p) := hpF.isProper
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (f ≫ p)
  have : Y.IsSeparated := ⟨by
    rw [← terminal.comp_from (f ≫ p)]
    infer_instance⟩
  have : IsLocallyNoetherian Y := SGPT.NAPotential.BJ.isLocallyNoetherian_of_isProjective (f ≫ p)
  have : IsNoetherian Y := {}
  have hYdim' : topologicalKrullDim Y ≤ (m + 2 : ℕ) := hYdim ▸ hdim
  -- (b) the components of the boundary
  let ι := DivisorComponent B
  let : Fintype ι := Fintype.ofFinite ι
  let C : ι → Closeds Y := fun j => j.val
  have hirr : ∀ j, IsIrreducible (C j : Set Y) := snc_component_isIrreducible B
  have hcart : ∀ j, (Scheme.IdealSheafData.vanishingIdeal (C j)).IsInvertible :=
    snc_component_isInvertible B hB
  have hinc : ∀ i j, C i ≤ C j → i = j := snc_component_eq_of_le B
  let I : ι → Y.IdealSheafData := fun j => Scheme.IdealSheafData.vanishingIdeal (C j)
  have hCB : ∀ j, (C j : Set Y) ⊆ f ⁻¹' Z₀.support := fun j =>
    hBsupp ▸ snc_component_le_support B j
  have hcover : f ⁻¹' (Z₀.support : Set X) ⊆ ⋃ j, (C j : Set Y) := by
    rw [← hBsupp, snc_support_eq_iUnion B]
  -- the central fibre upstairs
  let P' := (Scheme.Modules.pullback f).obj P
  have hP' : IsInvertible P' := hP.pullback f
  let s₀' := SchemeLineSectionEvaluation.pullbackSectionHom f s₀
  have hs₀' : s₀' ≠ 0 := pullbackSectionHom_ne_zero f hfsurj P hP s₀ hs₀
  set J₀ := LineSectionZeroIdeal.zeroIdeal P' hP' s₀' with hJ₀
  have hJ₀inv : J₀.IsInvertible :=
    LineSectionZeroIdeal.zeroIdeal_isInvertible_of_ne_zero P' hP' s₀' hs₀'
  have hJ₀supp : (J₀.support : Set Y) = f ⁻¹' Z₀.support := support_zeroIdeal_pullback f P hP s₀
  have hJ₀cov : (J₀.support : Set Y) ⊆ ⋃ j, (C j : Set Y) := hJ₀supp ▸ hcover
  let b : ι → ℕ := ord C hirr hcart hinc J₀ hJ₀inv hJ₀cov
  have hb : ∀ j, 0 < b j := fun j =>
    ord_pos C hirr hcart hinc J₀ hJ₀inv hJ₀cov j (hJ₀supp ▸ hCB j)
  have hJ₀eq : J₀ = ∏ j, I j ^ b j := eq_prod_pow_ord C hirr hcart hinc J₀ hJ₀inv hJ₀cov
  -- the vertical divisors upstairs
  let M' : κ → X.Modules := fun i => (M i).1
  let t' := fun i => SchemeLineSectionEvaluation.pullbackSectionHom f (t i)
  have ht' : ∀ i, t' i ≠ 0 := fun i => pullbackSectionHom_ne_zero f hfsurj _ (M i).2 (t i) (ht i)
  have hJinv : ∀ i, (LineSectionZeroIdeal.zeroIdeal _ ((M i).2.pullback f) (t' i)).IsInvertible :=
    fun i => LineSectionZeroIdeal.zeroIdeal_isInvertible_of_ne_zero _ _ _ (ht' i)
  have hJcov : ∀ i, ((LineSectionZeroIdeal.zeroIdeal _ ((M i).2.pullback f) (t' i)).support :
      Set Y) ⊆ ⋃ j, (C j : Set Y) := by
    intro i
    rw [support_zeroIdeal_pullback f (M i).1 (M i).2 (t i)]
    exact (Set.preimage_mono (hvert i)).trans hcover
  let d : κ → ι → ℕ := fun i => ord C hirr hcart hinc _ (hJinv i) (hJcov i)
  have hJeq : ∀ i, LineSectionZeroIdeal.zeroIdeal _ ((M i).2.pullback f) (t' i) =
      ∏ j, I j ^ d i j := fun i => eq_prod_pow_ord C hirr hcart hinc _ (hJinv i) (hJcov i)
  -- the components as line bundles with sections
  let E : ι → {E : Y.Modules // IsInvertible E} := fun j =>
    ⟨cartierLine (I j), cartierLine_isInvertible (hcart j)⟩
  let σ : ∀ j, unitObj Y ⟶ (E j).1 := fun j => cartierSection (I j) (hcart j)
  have hσzero : ∀ j, LineSectionZeroIdeal.zeroIdeal (E j).1 (E j).2 (σ j) = I j := fun j =>
    zeroIdeal_cartierSection (I j) (hcart j)
  have hσsupp : ∀ j, ((LineSectionZeroIdeal.zeroIdeal (E j).1 (E j).2 (σ j)).support : Set Y) =
      C j := by
    intro j
    rw [hσzero j]
    exact Scheme.IdealSheafData.coe_support_vanishingIdeal (C j)
  have hσ : ∀ j, σ j ≠ 0 := by
    intro j
    obtain ⟨x₀, hx₀⟩ := exists_not_mem_support_zeroIdeal P hP s₀ hs₀
    obtain ⟨y, rfl⟩ := hfsurj x₀
    refine ne_zero_of_not_mem_support (E j).1 (E j).2 (σ j) y ?_
    intro hy
    have hy' : y ∈ (C j : Set Y) := by
      rw [← hσsupp j]
      exact hy
    exact hx₀ (hCB j hy')
  have hint : ∀ j, IsIntegral (LineSectionZeroIdeal.zeroIdeal (E j).1 (E j).2 (σ j)).subscheme := by
    intro j
    rw [hσzero j]
    exact FcSchemeCurveDimensions.isIntegral_vanishingIdeal_subscheme (C j) (hirr j)
  have hres : ∀ i j, i ≠ j → restrictSection
      (LineSectionZeroIdeal.zeroIdeal (E i).1 (E i).2 (σ i)).subschemeι (σ j) ≠ 0 := by
    intro i j hij
    have hη : genPt C hirr i ∈ Set.range
        (LineSectionZeroIdeal.zeroIdeal (E i).1 (E i).2 (σ i)).subschemeι := by
      rw [Scheme.IdealSheafData.range_subschemeι, hσsupp i]
      exact (isGenericPoint_genPt C hirr i).mem
    obtain ⟨z, hz⟩ := hη
    refine SchemeGlobalPullbackCartierRatio.pullbackSection_ne_zero _ (E j).1 (E j).2 (σ j) z ?_
    rw [hz]
    intro hmem
    have hmem' : genPt C hirr i ∈ (C j : Set Y) := by
      rw [← hσsupp j]
      exact hmem
    apply hij
    refine hinc i j fun y hy => ?_
    exact ((isGenericPoint_genPt C hirr i).specializes hy).mem_closed (C j).isClosed hmem'
  have hfib : ∑ j, b j • lineCls (E j) = lineCls ⟨P', hP'⟩ :=
    (lineCls_eq_sum_cartierLine Finset.univ I hcart b P' hP' s₀' hs₀' hJ₀eq).symm
  have hortho : ∀ j (t : Multiset (PicQ Y)),
      interFormQ (f ≫ p) (m + 2) hYdim' (unitObj Y) (picQ (E j) ::ₘ picQ ⟨P', hP'⟩ ::ₘ t) = 0 := by
    intro j t
    have : IsProjective ((LineSectionZeroIdeal.zeroIdeal (E j).1 (E j).2 (σ j)).subschemeι ≫
        (f ≫ p)) := isProjective_closed_comp _ _
    rw [interFormQ_cut (m + 1) (f ≫ p) hYdim' (E j).1 (E j).2 (σ j) (hσ j), Multiset.map_cons]
    have h0 : picPullbackQ (LineSectionZeroIdeal.zeroIdeal (E j).1 (E j).2 (σ j)).subschemeι
        (picQ ⟨P', hP'⟩) = 0 := by
      rw [show (⟨P', hP'⟩ : {L : Y.Modules // IsInvertible L}) =
          ⟨(Scheme.Modules.pullback f).obj P, hP.pullback f⟩ from rfl,
        ← SGPT.NAPotential.BJ.picPullbackQ_picQ f ⟨P, hP⟩, ← picPullbackQ_comp]
      apply htrivP
      rintro _ ⟨z, rfl⟩
      have hz : (LineSectionZeroIdeal.zeroIdeal (E j).1 (E j).2 (σ j)).subschemeι z ∈ (C j : Set Y) := by
        rw [← hσsupp j, ← Scheme.IdealSheafData.range_subschemeι]
        exact ⟨z, rfl⟩
      exact hCB j hz
    rw [h0, MultisetForm.map_zero_cons]
  -- (c) relatively nef classes upstairs
  let W' : Set Y := f ⁻¹' W
  have hW' : ∀ j, ((LineSectionZeroIdeal.zeroIdeal (E j).1 (E j).2 (σ j)).support : Set Y) ⊆ W' := by
    intro j
    rw [hσsupp j]
    exact (hCB j).trans (Set.preimage_mono hW)
  let pb : {N : X.Modules // IsInvertible N} × ℚ → {N : Y.Modules // IsInvertible N} × ℚ :=
    fun N => (⟨(Scheme.Modules.pullback f).obj N.1.1, N.1.2.pullback f⟩, N.2)
  let Ns' := Ns.map pb
  have hNs' : Ns'.length = m := by simp [Ns', hNs]
  have hnef' : ∀ N ∈ Ns', IsNefOn (f ≫ p) N.1.1 W' := by
    intro N hN
    obtain ⟨N₀, hN₀, rfl⟩ := List.mem_map.mp hN
    exact IsNefOn.pullback_morphism f N₀.1.2 (hnef N₀ hN₀)
  have hc' : ∀ N ∈ Ns', 0 ≤ N.2 := by
    intro N hN
    obtain ⟨N₀, hN₀, rfl⟩ := List.mem_map.mp hN
    exact hc N₀ hN₀
  let x' : ι → ℚ := fun j => ∑ i, x i * (d i j : ℚ)
  have hY := interFormQ_sq_nonpos_of_components_smul_ortho m (f ≫ p) hYdim' P' hP' E σ hσ
    hint hres b hb hfib hortho W' hW' Ns' hNs' hnef' hc' x'
  -- the pulled-back classes
  have hD : picPullbackQ f (∑ i, x i • picQ (M i)) = ∑ j, x' j • picQ (E j) := by
    rw [map_sum]
    simp only [_root_.map_smul]
    have hMi : ∀ i, picPullbackQ f (picQ (M i)) = ∑ j, (d i j : ℚ) • picQ (E j) := by
      intro i
      rw [show M i = ⟨(M i).1, (M i).2⟩ from rfl, SGPT.NAPotential.BJ.picPullbackQ_picQ]
      exact picQ_eq_sum_cartierLine Finset.univ I hcart (d i) _ ((M i).2.pullback f) (t' i)
        (ht' i) (hJeq i)
    simp only [hMi, Finset.smul_sum, smul_smul, x', Finset.sum_smul]
    exact Finset.sum_comm
  have hN : ∀ N : {N : X.Modules // IsInvertible N} × ℚ,
      picPullbackQ f (N.2 • picQ N.1) = (pb N).2 • picQ (pb N).1 := by
    intro N
    rw [_root_.map_smul, show N.1 = ⟨N.1.1, N.1.2⟩ from rfl, SGPT.NAPotential.BJ.picPullbackQ_picQ]
  refine interFormQ_nonpos_of_pullback_nonpos p f (m + 2) hdim hYdim' hfsurj _ ?_
  convert hY using 2
  rw [Multiset.map_cons, Multiset.map_cons, Multiset.map_coe, hD, List.map_map]
  congr 3
  simp only [Ns', List.map_map]
  exact List.map_congr_left fun N _ => hN N

end ortho

end SGPT.NAPotential.ThinApprox.BJ
