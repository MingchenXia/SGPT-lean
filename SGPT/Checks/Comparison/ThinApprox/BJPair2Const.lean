import SGPT.Checks.Comparison.ThinApprox.BJPair2Energy

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
# Vertical divisors are orthogonal to the central fibre; `prop:intpairing` (i) (lane BJ-PAIR, R5)

Source: [BJ22] (`references/bj22-trivval`), Proposition `prop:intpairing` (i):
`(0, 1) ⋅ (s₁ ω, φ₁) ⋯ (s_n ω, φ_n) = (∏ sᵢ) (ω^n)`. Towards `thm:BJappseq` of
`chapter_NApotential.tex`. Blueprint: `claude-bj-pair.tex`.

[BJ22] move the central fibre `𝒳₀` to the fibre at infinity. We avoid the second chart of `ℙ¹`:

* `nonempty_pullback_comap_zeroIdeal_iso_unit`: the ideal sheaf of `0 ∈ ℙ¹`, pulled back along any
  morphism whose image lies in the chart `D₊(x₀) = Spec ℂ[t]`, is trivial (there it is `(t)`);
* `interFormQ_line_central_eq_zero` (**vertical divisors are orthogonal to the central fibre**): on
  a good model, `(E ⋅ 𝒳₀ ⋅ θ₂ ⋯ θ_n) = 0` for every vertical Cartier divisor `E` — cut along `E`,
  whose image lies in the central fibre, where `𝒪(𝒳₀)` is trivial;
* `MultisetForm.cons_map_eq_prod`: the multilinear expansion of `(c ⋅ ∏ (sᵢ ω + vᵢ))` when `c` is
  orthogonal to the `vᵢ`;
* `pairConst` (**[BJ22, `prop:intpairing` (i)]**): the axiom `PairConst` of lane BJ-PAIR (with
  `(𝒳₀ ⋅ (π^*ω)^n) = (ω^n)`, `interFormQ_central_omega`).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.NAPotential.ThinApprox.BJ
open SGPT.NAPotential.BJ

open AlgebraicGeometry CategoryTheory Topology
open SGPT.NAPotential.Berkovich SGPT.NAPotential.BJModel SGPT.NAPotential.ThinApprox.BJModel SGPT.NAPotential.BJIntersect
open SGPT.NAPotential.BJHodge
open SGPT.Support.Alterations SGPT.Support.Alterations.Geometry

/-! ### Multilinear expansion -/

theorem MultisetForm.cons_map_eq_prod {V : Type*} [AddCommGroup V] [Module ℚ V]
    (Φ : MultisetForm ℚ V) (c ω : V) (S : Submodule ℚ V)
    (hS : ∀ v ∈ S, ∀ t : Multiset V, Φ (c ::ₘ v ::ₘ t) = 0) :
    ∀ (s : Multiset (ℚ × V)) (t : Multiset V), (∀ x ∈ s, x.2 ∈ S) →
      Φ (c ::ₘ (t + s.map fun x => x.1 • ω + x.2)) =
        (s.map Prod.fst).prod * Φ (c ::ₘ (t + Multiset.replicate (Multiset.card s) ω)) := by
  intro s
  induction s using Multiset.induction_on with
  | empty => intro t _; simp
  | cons x s ih =>
    intro t hs
    have hx := hs x (Multiset.mem_cons_self x s)
    have hs' : ∀ y ∈ s, y.2 ∈ S := fun y hy => hs y (Multiset.mem_cons_of_mem hy)
    have e1 : t + (x.1 • ω + x.2) ::ₘ s.map (fun x => x.1 • ω + x.2) =
        (x.1 • ω + x.2) ::ₘ (t + s.map fun x => x.1 • ω + x.2) := Multiset.add_cons _ _ _
    rw [Multiset.map_cons, e1, Φ.map_add_snd, hS _ hx, add_zero]
    have e2 : Φ (c ::ₘ (x.1 • ω) ::ₘ (t + s.map fun x => x.1 • ω + x.2)) =
        x.1 * Φ (c ::ₘ ω ::ₘ (t + s.map fun x => x.1 • ω + x.2)) := by
      rw [Multiset.cons_swap, Φ.map_smul, Multiset.cons_swap]
    rw [e2, ← Multiset.cons_add, ih _ hs', Multiset.map_cons, Multiset.prod_cons,
      Multiset.card_cons, Multiset.replicate_succ, Multiset.add_cons, Multiset.cons_add]
    ring

variable {X : Scheme.{0}} {p : X ⟶ Spec (.of ℂ)} [IsProjective p] [IsIntegral X]

local instance : IsProper p :=
  (SGPT.Foundations.Envelope.ProjectiveFactorizationRingIso.of_isProjective p).isProper

/-! ### The ideal of `0 ∈ ℙ¹` on the chart `D₊(x₀)` -/

section chart

theorem lineChart_isDominant : IsDominant (lineChart ℂ) := by
  let := projectiveSpace_isIntegral ℂ 1
  constructor
  apply (lineChart ℂ).isOpenEmbedding.isOpen_range.dense
  obtain ⟨x⟩ : Nonempty (Spec (.of (ProjectiveIdeal.CoordinateRing ℂ (0 : Fin 2)))) :=
    inferInstance
  exact ⟨_, x, rfl⟩

/-- The pull-back of the trivial module sheaf is trivial. -/
theorem nonempty_pullback_iso_unit_of_iso {Y T : Scheme.{0}} (h : T ⟶ Y) {M : Y.Modules}
    (e : M ≅ Scheme.Modules.unitObj Y) :
    Nonempty ((Scheme.Modules.pullback h).obj M ≅ Scheme.Modules.unitObj T) :=
  ⟨(Scheme.Modules.pullback h).mapIso e ≪≫ Scheme.Modules.pullbackUnitIso h⟩

/-- **The ideal of `0 ∈ ℙ¹` is trivial over the chart `D₊(x₀)`**: its pull-back along a morphism
with image in the chart is trivial. -/
theorem nonempty_pullback_zeroIdeal_iso_unit {T : Scheme.{0}}
    (h : T ⟶ projectiveSpace ℂ 1) (hr : Set.range h ⊆ Set.range (lineChart ℂ)) :
    Nonempty ((Scheme.Modules.pullback h).obj (zeroIdeal ℂ).toModules ≅
      Scheme.Modules.unitObj T) := by
  let A := ProjectiveIdeal.CoordinateRing ℂ (0 : Fin 2)
  let := projectiveSpace_isIntegral ℂ 1
  have := lineChart_isDominant
  let h' := IsOpenImmersion.lift (lineChart ℂ) h hr
  have hfac : h' ≫ lineChart ℂ = h := IsOpenImmersion.lift_fac _ _ _
  rw [← hfac]
  let I0 := zeroIdeal ℂ
  have hI0 : I0.IsInvertible := zeroIdeal_isInvertible ℂ
  have hiso : IsIso (I0.toModulesComapPullbackMap (lineChart ℂ)) :=
    hI0.toModulesComapPullbackMap_isIso_of_dominant_integral (lineChart ℂ)
  let e1 := (Scheme.Modules.pullbackComp h' (lineChart ℂ)).app I0.toModules
  let e2 := (Scheme.Modules.pullback h').mapIso
    (asIso (I0.toModulesComapPullbackMap (lineChart ℂ)))
  suffices H : Nonempty ((Scheme.Modules.pullback h').obj (I0.comap (lineChart ℂ)).toModules ≅
      Scheme.Modules.unitObj T) by
    obtain ⟨e⟩ := H
    exact ⟨e1.symm ≪≫ e2 ≪≫ e⟩
  -- on `Spec ℂ[t]`, the ideal is `(t)`, generated by a nonzerodivisor
  rw [zeroIdeal_comap_lineChart]
  let g : Γ(Spec (.of A), ⊤) := (Scheme.ΓSpecIso (.of A)).inv (chartT ℂ)
  let J := Scheme.IdealSheafData.ofIdealTop (X := Spec (.of A)) (Ideal.span {g})
  let U : (Spec (.of A)).affineOpens := ⟨⊤, isAffineOpen_top _⟩
  have hg : g ∈ nonZeroDivisors Γ(Spec (.of A), U) := by
    apply mem_nonZeroDivisors_of_ne_zero
    intro h0
    have := congrArg (Scheme.ΓSpecIso (.of A)).hom.hom h0
    rw [ΓSpecIso_hom_inv_apply, map_zero] at this
    exact MvPolynomial.X_ne_zero _ this
  have hJ : J.ideal U = Ideal.span {g} := ofIdealTop_ideal_top _
  let eU := J.regularGeneratorPullbackModuleIso U g hg hJ
  let h'' := IsOpenImmersion.lift (U : (Spec (.of A)).Opens).ι h' (by
    rw [Scheme.Opens.range_ι]; exact Set.subset_univ _)
  have hfac' : h'' ≫ (U : (Spec (.of A)).Opens).ι = h' := IsOpenImmersion.lift_fac _ _ _
  rw [← hfac']
  obtain ⟨e3⟩ := nonempty_pullback_iso_unit_of_iso h'' eU
  exact ⟨((Scheme.Modules.pullbackComp h'' (U : (Spec (.of A)).Opens).ι).app J.toModules).symm ≪≫
    e3⟩

/-- The same along any dominant morphism from an integral scheme. -/
theorem nonempty_pullback_comap_zeroIdeal_iso_unit {Y T : Scheme.{0}} [IsIntegral Y]
    (q : Y ⟶ projectiveSpace ℂ 1) [IsDominant q] (h : T ⟶ Y)
    (hr : Set.range (h ≫ q) ⊆ Set.range (lineChart ℂ)) :
    Nonempty ((Scheme.Modules.pullback h).obj ((zeroIdeal ℂ).comap q).toModules ≅
      Scheme.Modules.unitObj T) := by
  let := projectiveSpace_isIntegral ℂ 1
  have hiso : IsIso ((zeroIdeal ℂ).toModulesComapPullbackMap q) :=
    (zeroIdeal_isInvertible ℂ).toModulesComapPullbackMap_isIso_of_dominant_integral q
  obtain ⟨e⟩ := nonempty_pullback_zeroIdeal_iso_unit (h ≫ q) hr
  exact ⟨(Scheme.Modules.pullback h).mapIso
      (asIso ((zeroIdeal ℂ).toModulesComapPullbackMap q)).symm ≪≫
    (Scheme.Modules.pullbackComp h q).app _ ≪≫ e⟩

end chart

/-! ### Vertical divisors are orthogonal to the central fibre -/

section ortho

variable (n : ℕ) (hX : topologicalKrullDim X ≤ n)

theorem flagModel_productSnd_isDominant (𝔠 : FlagIdeal X) (c : ℤ) :
    IsDominant (flagModelπ p 𝔠 c ≫ productSnd p) := by
  have := flagModelπ_isDominant p 𝔠 c
  have : IsDominant (productSnd p) := ⟨(productSnd_surjective p).denseRange⟩
  infer_instance

/-- **Vertical divisors are orthogonal to the central fibre**: `(E ⋅ 𝒳₀ ⋅ t) = 0` on a blow-up
model, for every vertical Cartier divisor `E` and all classes `t`. -/
theorem interFormQ_line_central_eq_zero {𝔠 : FlagIdeal X} {c : ℤ} (E : VertCartier p 𝔠 c)
    (t : Multiset (PicQ (flagModel p 𝔠 c))) :
    interFormQ (flagModelStructure p 𝔠 c) (n + 1) (topologicalKrullDim_flagModel_le p 𝔠 c n hX)
      (Scheme.Modules.unitObj _) (picQ E.line ::ₘ picQ (centralLine p 𝔠 c) ::ₘ t) = 0 := by
  have hJ := E.isInvertible
  have hL := cartierLine_isInvertible hJ
  have hcart : picQ E.line = -picQ ⟨cartierLine E.ideal, hL⟩ := by
    rw [picQ, picQ, lineCls_cartierLine hJ, TensorProduct.tmul_neg, neg_neg]
    rfl
  have hs : cartierSection E.ideal hJ ≠ 0 := by
    refine ne_zero_of_not_mem_support _ hL _ (genericPoint (flagModel p 𝔠 c)) ?_
    rw [zeroIdeal_cartierSection]
    intro hmem
    have h1 := E.support_subset hmem
    change flagModelπ p 𝔠 c (genericPoint (flagModel p 𝔠 c)) ∈ (centralIdeal p).support at h1
    rw [(flagModelπ_genericPoint p 𝔠 c).1] at h1
    exact genericPoint_productLine_not_mem h1
  have : IsProjective ((SGPT.Foundations.Envelope.LineSectionZeroIdeal.zeroIdeal (cartierLine E.ideal)
      hL (cartierSection E.ideal hJ)).subschemeι ≫ flagModelStructure p 𝔠 c) :=
    isProjective_closed_comp _ _
  rw [hcart, MultisetForm.map_neg, interFormQ_cut n (flagModelStructure p 𝔠 c) _ _ hL _ hs,
    Multiset.map_cons, neg_eq_zero]
  set Z := SGPT.Foundations.Envelope.LineSectionZeroIdeal.zeroIdeal (cartierLine E.ideal) hL
    (cartierSection E.ideal hJ)
  have hZ : Z = E.ideal := zeroIdeal_cartierSection _ hJ
  -- `𝒪(𝒳₀)` is trivial on `E`
  let q := flagModelπ p 𝔠 c ≫ productSnd p
  have := flagModel_productSnd_isDominant (p := p) 𝔠 c
  have hcomap : (centralIdeal p).comap (flagModelπ p 𝔠 c) = (zeroIdeal ℂ).comap q := by
    rw [Scheme.IdealSheafData.comap_comp]
    rfl
  have hrange : Set.range (Z.subschemeι ≫ q) ⊆ Set.range (lineChart ℂ) := by
    rintro _ ⟨x, rfl⟩
    have hx0 : Z.subschemeι x ∈ (Z.support : Set (flagModel p 𝔠 c)) := by
      rw [← Scheme.IdealSheafData.range_subschemeι]; exact ⟨x, rfl⟩
    have hsupp : (Z.support : Set (flagModel p 𝔠 c)) = E.ideal.support := by rw [hZ]
    rw [hsupp] at hx0
    have h1 := E.support_subset hx0
    change flagModelπ p 𝔠 c (Z.subschemeι x) ∈ ((centralIdeal p).support : Set _) at h1
    rw [support_centralIdeal] at h1
    obtain ⟨z, hz⟩ := h1
    refine ⟨Spec.map (CommRingCat.ofHom (evalZero ℂ)) z, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← zeroPoint, hz]
    rfl
  obtain ⟨e⟩ := nonempty_pullback_comap_zeroIdeal_iso_unit q Z.subschemeι hrange
  have hc0 : picPullbackQ Z.subschemeι (picQ (centralLine p 𝔠 c)) = 0 := by
    rw [SGPT.NAPotential.BJ.picPullbackQ_picQ]
    have h1 : picQ ⟨(Scheme.Modules.pullback Z.subschemeι).obj (centralLine p 𝔠 c).1,
        (centralLine p 𝔠 c).2.pullback _⟩ =
        picQ ⟨Scheme.Modules.unitObj Z.subscheme, Scheme.Modules.isInvertible_unit⟩ := by
      have hc : (centralLine p 𝔠 c).1 = ((zeroIdeal ℂ).comap q).toModules := by
        simp only [centralLine, hcomap]
      exact picQ_eq_of_iso _ _ ((Scheme.Modules.pullback Z.subschemeι).mapIso
        (eqToIso hc) ≪≫ e)
    rw [h1, picQ, lineCls_unit, TensorProduct.tmul_zero]
  rw [hc0, MultisetForm.map_zero_cons]

end ortho

/-! ### `prop:intpairing` (i) -/

section const

variable [CompactSpace X] [X.IsSeparated] (n : ℕ) (hX : topologicalKrullDim X ≤ n)
  (ω : PicQ X)

/-- The vertical classes `[𝒪(E)]` of a model. -/
def vertSpan (𝔠 : FlagIdeal X) (c : ℤ) : Submodule ℚ (PicQ (flagModel p 𝔠 c)) :=
  Submodule.span ℚ (Set.range fun E : VertCartier p 𝔠 c => picQ E.line)

omit [IsProjective p] [IsIntegral X] [CompactSpace X] [X.IsSeparated] in
theorem cls_mem_vertSpan {𝔠 : FlagIdeal X} {c : ℤ} (D : FDiv p 𝔠 c) :
    FDiv.cls D ∈ vertSpan 𝔠 c := by
  induction D using Finsupp.induction_linear with
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add D D' hD hD' => rw [map_add]; exact add_mem hD hD'
  | single e q =>
    rw [FDiv.cls_single]
    exact Submodule.smul_mem _ _ (Submodule.neg_mem _ (Submodule.subset_span ⟨e.vert, rfl⟩))

omit [CompactSpace X] [X.IsSeparated] in
theorem interFormQ_central_vert_eq_zero {𝔠 : FlagIdeal X} {c : ℤ} (v : PicQ (flagModel p 𝔠 c))
    (hv : v ∈ vertSpan 𝔠 c) (t : Multiset (PicQ (flagModel p 𝔠 c))) :
    interFormQ (flagModelStructure p 𝔠 c) (n + 1) (topologicalKrullDim_flagModel_le p 𝔠 c n hX)
      (Scheme.Modules.unitObj _) (-picQ (centralLine p 𝔠 c) ::ₘ v ::ₘ t) = 0 := by
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨E, rfl⟩ := hx
    rw [MultisetForm.map_neg, Multiset.cons_swap, interFormQ_line_central_eq_zero n hX E t,
      neg_zero]
  | zero => rw [Multiset.cons_swap, MultisetForm.map_zero_cons]
  | add x y _ _ hx hy => rw [MultisetForm.map_add_snd, hx, hy, add_zero]
  | smul a x _ hx =>
    rw [Multiset.cons_swap, MultisetForm.map_smul, Multiset.cons_swap, hx, mul_zero]

/-- **[BJ22, `prop:intpairing` (i)]**: `(0, 1) ⋅ (s₁ ω, φ₁) ⋯ (s_n ω, φ_n) = (∏ sᵢ) (ω^n)` for PL
functions `φᵢ`. This is the axiom `PairConst` of lane BJ-PAIR. -/
theorem pairConst : PairConst p n hX ω := by
  classical
  intro s hcard hs
  obtain ⟨𝔠, c, hgood, hrep⟩ := exists_goodModel_of_mem (p := p)
    (s := ((0 : ℚ), (1 : BerkovichPoint p → ℝ)) ::ₘ s) (by
      intro z hz
      rcases Multiset.mem_cons.mp hz with rfl | hz
      · have h1 : (1 : BerkovichPoint p → ℝ) = fun _ => ((1 : ℚ) : ℝ) := by
          funext v; simp
        rw [h1]
        exact const_mem_plSubmodule (f := p) (1 : ℚ)
      · exact hs z hz)
  let D1 : FDiv p 𝔠 c := Finsupp.single (centralDatum hgood) 1
  have hD1 : FDiv.fn D1 = 1 := by
    simp only [D1, FDiv.fn_single, fn_centralDatum, one_smul]
    rfl
  let R : (BerkovichPoint p → ℝ) → FDiv p 𝔠 c := fun φ => if φ = 1 then D1 else flagRep 𝔠 c φ
  have hR : ∀ x ∈ ((0 : ℚ), (1 : BerkovichPoint p → ℝ)) ::ₘ s, FDiv.fn (R x.2) = x.2 := by
    intro x hx
    by_cases h1 : x.2 = 1
    · rw [show R x.2 = D1 from if_pos h1, hD1, h1]
    · simp only [R, if_neg h1]
      exact fn_flagRep (hrep x hx)
  rw [flagPair_eq n hX ω hgood _ hrep, ← interFormQ_flag_eq_modelValue n hX ω hgood _ R hR,
    Multiset.map_cons]
  have hhead : ((0 : ℚ), (1 : BerkovichPoint p → ℝ)).1 • omegaPullback 𝔠 c ω +
      FDiv.cls (R ((0 : ℚ), (1 : BerkovichPoint p → ℝ)).2) = -picQ (centralLine p 𝔠 c) := by
    simp only [R, if_pos rfl, D1, FDiv.cls_single, picQ_centralDatum, zero_smul, zero_add,
      one_smul]
  rw [hhead]
  set s' : Multiset (ℚ × PicQ (flagModel p 𝔠 c)) := s.map fun x => (x.1, FDiv.cls (R x.2))
  have hmap : (s.map fun x => x.1 • omegaPullback 𝔠 c ω + FDiv.cls (R x.2)) =
      0 + s'.map fun y => y.1 • omegaPullback 𝔠 c ω + y.2 := by
    rw [zero_add, Multiset.map_map]
    rfl
  rw [hmap, MultisetForm.cons_map_eq_prod _ _ (omegaPullback 𝔠 c ω) (vertSpan 𝔠 c)
    (fun v hv t => interFormQ_central_vert_eq_zero n hX v hv t) s' 0 (fun y hy => by
      obtain ⟨x, -, rfl⟩ := Multiset.mem_map.mp hy
      exact cls_mem_vertSpan _),
    zero_add, Multiset.card_map, hcard, interFormQ_central_omega n hX ω, Multiset.map_map]
  rw [volQ, mul_comm]
  rfl

end const

end SGPT.NAPotential.ThinApprox.BJ
