import SGPT.Checks.Comparison.BJHodgeDivisor
import SGPT.Checks.Comparison.BJHodgeLine
import SGPT.Checks.Comparison.BJHodgeAlteration
import SGPT.Checks.Comparison.BJIntersectHodge
import SGPT.Checks.Comparison.BJProjFormula
import SGPT.Checks.Comparison.BJProjNef
import SGPT.Foundations.Envelope.AlgGeom.SchemeCurveDimensions

/-!
# The Hodge-type inequality for vertical divisors

[BHJ17, Lemma 6.14] = [BJ22, `lem:Hodge`]: on a test configuration `𝒳̄` of an `n`-dimensional
variety, a `ℚ`-Cartier divisor `D` supported on the central fibre satisfies
`(D² · L₁ ⋯ L_{n-1}) ≤ 0` for relatively nef `Lᵢ`.

`interFormQ_sq_nonpos_of_vertical` proves it for any integral projective scheme `X` over a field
(`dim X ≤ m + 2`, `n = m + 1`) with a "fibre class": an invertible `P` with nonzero sections `s₀`
(cutting out the central fibre `𝒳₀`) and `s_∞` (cutting out the fibre at infinity) whose zero
loci are disjoint (for a test configuration, `P = π^*𝒪_{ℙ¹}(1)` and `s₀, s_∞` the pulled-back
coordinates). The vertical divisor is any `ℚ`-combination `D = ∑ xᵢ [Mᵢ]` of invertible sheaves
`Mᵢ` with nonzero sections `tᵢ` whose zero loci lie in `𝒳₀` (effective Cartier divisors supported on
the central fibre; every Cartier divisor supported on `𝒳₀` is a difference of two such), and the
`Lᵢ = cᵢ Nᵢ` are nonnegative rational multiples of invertible sheaves nef on a set containing `𝒳₀`.
Unlike `BJIntersect.interFormQ_sq_nonpos_of_components`, no assumption is made on the components
of the central fibre (which need not be `ℚ`-Cartier).

Proof ([BHJ17, proof of Lemma 6.14]): de Jong's alteration theorem gives a surjection
`f : Y ⟶ X` from a regular integral projective `Y` of the same dimension and a strict normal
crossings divisor on `Y` with support `f⁻¹ 𝒳₀` (`exists_regular_snc_model`). Its components `E_j`
are prime Cartier divisors, so the vertical Cartier divisors `f^*𝒳₀` and `f^*Mᵢ` decompose as
`∑ b_j E_j` (`b_j > 0`) and `∑ d_{ij} E_j` (`eq_prod_pow_ord`, `ord_pos`,
`lineCls_eq_sum_cartierLine`). The `f^*Nᵢ` are nef on `f⁻¹ W` (`IsNefOn.pullback_morphism`), and the
`E_j` are trivial on the zero scheme of `f^* s_∞` (`nonempty_pullback_iso_unit`). Hence
`(f^*D)² · f^*L₁ ⋯ ≤ 0` on `Y` by `interFormQ_sq_nonpos_of_components_smul`, and the sign descends to
`X` by the projection formula (`interFormQ_nonpos_of_pullback_nonpos`).

Blueprint: `claude-bj-hodge.tex` (`claude-bj-hodge:hodge`).
-/

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Scheme.Modules TopologicalSpace
open scoped TensorProduct

universe u

namespace SGPT.NAPotential.BJHodge

open SGPT.Foundations.Envelope SGPT.NAPotential.BJIntersect SGPT.NAPotential.BJProj SGPT.Support.Alterations

attribute [local instance] Scheme.Modules.monoidalCategory Scheme.Modules.symmetricCategory

variable {k : Type u} [Field k]

/-- The pull-back of a nonzero section along a surjection from an integral scheme is nonzero. -/
theorem pullbackSectionHom_ne_zero {X Y : Scheme.{u}} [IsIntegral X] (f : Y ⟶ X)
    (hf : Function.Surjective f) (L : X.Modules) (hL : IsInvertible L) (s : unitObj X ⟶ L)
    (hs : s ≠ 0) : SchemeLineSectionEvaluation.pullbackSectionHom f s ≠ 0 := by
  obtain ⟨x, hx⟩ := exists_not_mem_support_zeroIdeal L hL s hs
  obtain ⟨y, rfl⟩ := hf x
  exact SchemeGlobalPullbackCartierRatio.pullbackSection_ne_zero f L hL s y hx

/-- The support of the zero ideal of a pulled-back section is the preimage of the support. -/
theorem support_zeroIdeal_pullback {X Y : Scheme.{u}} (f : Y ⟶ X) (L : X.Modules)
    (hL : IsInvertible L) (s : unitObj X ⟶ L) :
    ((LineSectionZeroIdeal.zeroIdeal ((Scheme.Modules.pullback f).obj L) (hL.pullback f)
      (SchemeLineSectionEvaluation.pullbackSectionHom f s)).support : Set Y) =
      f ⁻¹' (LineSectionZeroIdeal.zeroIdeal L hL s).support := by
  rw [← Vanishing.NadelBertiniFibreIdeals.zeroIdeal_comap f L hL s,
    Scheme.IdealSheafData.support_comap]
  rfl

/-- A section of an invertible sheaf which does not vanish at some point is nonzero. -/
theorem ne_zero_of_not_mem_support {Y : Scheme.{u}} (L : Y.Modules) (hL : IsInvertible L)
    (s : unitObj Y ⟶ L) (y : Y) (hy : y ∉ (LineSectionZeroIdeal.zeroIdeal L hL s).support) :
    s ≠ 0 := by
  intro h0
  apply SchemeGlobalPullbackCartierRatio.pullbackSection_ne_zero (𝟙 Y) L hL s y hy
  rw [h0, SchemeLineSectionEvaluation.pullbackSectionHom, Functor.map_zero, comp_zero]

/-- **The Hodge-type inequality for vertical divisors** ([BHJ17, Lemma 6.14], [BJ22, `lem:Hodge`]).
Let `X` be an integral projective `k`-scheme of dimension `≤ m + 2`, `P` invertible with nonzero
sections `s₀, s_∞` with disjoint zero loci (the central fibre `𝒳₀ = {s₀ = 0}` and the fibre at
infinity), `Mᵢ` invertible with nonzero sections `tᵢ` vanishing only on `𝒳₀`, and `Nₖ` invertible
and nef on a set `W ⊇ 𝒳₀`, with rational weights `cₖ ≥ 0`. Then for `D = ∑ xᵢ [Mᵢ]`,
`(D · D · c₁N₁ ⋯ c_mN_m)_X ≤ 0`. -/
theorem interFormQ_sq_nonpos_of_vertical (m : ℕ) {X : Scheme.{u}} [IsIntegral X]
    [CompactSpace X] [X.IsSeparated] (p : X ⟶ Spec (.of k)) [IsProjective p]
    (hdim : topologicalKrullDim X ≤ (m + 2 : ℕ))
    (P : X.Modules) (hP : IsInvertible P) (s₀ sInf : unitObj X ⟶ P) (hs₀ : s₀ ≠ 0)
    (hsInf : sInf ≠ 0)
    (hdisj : Disjoint ((LineSectionZeroIdeal.zeroIdeal P hP s₀).support : Set X)
      (LineSectionZeroIdeal.zeroIdeal P hP sInf).support)
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
  have : IsLocallyNoetherian Y := isLocallyNoetherian_of_isProjective (f ≫ p)
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
  let sInf' := SchemeLineSectionEvaluation.pullbackSectionHom f sInf
  have hs₀' : s₀' ≠ 0 := pullbackSectionHom_ne_zero f hfsurj P hP s₀ hs₀
  have hsInf' : sInf' ≠ 0 := pullbackSectionHom_ne_zero f hfsurj P hP sInf hsInf
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
  have htriv : ∀ j, Nonempty ((Scheme.Modules.pullback
      (LineSectionZeroIdeal.zeroIdeal P' hP' sInf').subschemeι).obj (E j).1 ≅
        unitObj (LineSectionZeroIdeal.zeroIdeal P' hP' sInf').subscheme) := by
    intro j
    refine nonempty_pullback_iso_unit (E j).1 (E j).2 (σ j) (hσ j) _ fun z hz => ?_
    have hz1 : (LineSectionZeroIdeal.zeroIdeal P' hP' sInf').subschemeι z ∈
        ((LineSectionZeroIdeal.zeroIdeal P' hP' sInf').support : Set Y) := by
      rw [← Scheme.IdealSheafData.range_subschemeι]
      exact ⟨z, rfl⟩
    rw [support_zeroIdeal_pullback f P hP sInf] at hz1
    have hz2 : (LineSectionZeroIdeal.zeroIdeal P' hP' sInf').subschemeι z ∈ (C j : Set Y) := by
      rw [← hσsupp j]
      exact hz
    exact Set.disjoint_left.mp hdisj (hCB j hz2) hz1
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
  have hY := interFormQ_sq_nonpos_of_components_smul m (f ≫ p) hYdim' P' hP' sInf' hsInf' E σ hσ
    hint hres b hb hfib htriv W' hW' Ns' hNs' hnef' hc' x'
  -- the pulled-back classes
  have hD : picPullbackQ f (∑ i, x i • picQ (M i)) = ∑ j, x' j • picQ (E j) := by
    rw [map_sum]
    simp only [_root_.map_smul]
    have hMi : ∀ i, picPullbackQ f (picQ (M i)) = ∑ j, (d i j : ℚ) • picQ (E j) := by
      intro i
      rw [show M i = ⟨(M i).1, (M i).2⟩ from rfl, picPullbackQ_picQ]
      exact picQ_eq_sum_cartierLine Finset.univ I hcart (d i) _ ((M i).2.pullback f) (t' i)
        (ht' i) (hJeq i)
    simp only [hMi, Finset.smul_sum, smul_smul, x', Finset.sum_smul]
    exact Finset.sum_comm
  have hN : ∀ N : {N : X.Modules // IsInvertible N} × ℚ,
      picPullbackQ f (N.2 • picQ N.1) = (pb N).2 • picQ (pb N).1 := by
    intro N
    rw [_root_.map_smul, show N.1 = ⟨N.1.1, N.1.2⟩ from rfl, picPullbackQ_picQ]
  refine interFormQ_nonpos_of_pullback_nonpos p f (m + 2) hdim hYdim' hfsurj _ ?_
  convert hY using 2
  rw [Multiset.map_cons, Multiset.map_cons, Multiset.map_coe, hD, List.map_map]
  congr 3
  simp only [Ns', List.map_map]
  exact List.map_congr_left fun N _ => hN N

end SGPT.NAPotential.BJHodge
