import SGPT.Checks.Comparison.BJPairEnergy
import SGPT.Foundations.Envelope.AlgGeom.SeshadriAmplenessCriterionSectionIntersections
import SGPT.Foundations.Envelope.AlgGeom.SeshadriAmplenessCriterionDimensionDrop
import SGPT.Foundations.Envelope.Source.NumericalAmpleness
import SGPT.NAPotential.DivDictTrivial

/-!
# The volume, the central fibre and `equ:mixedMA0` for the energy pairing (lane BJ-PAIR, R5)

Source: [BJ22] (`references/bj22-trivval`), §3.2: `(ω^n) > 0` for an ample class,
`(𝒳₀ ⋅ (π^*ω)^n) = (ω^n)` and `equ:mixedMA0`, `(0, f) ⋅ (ω, 0)^n = (ω^n) f(v_triv)`. Towards
`thm:BJappseq` of `chapter_NApotential.tex`. Blueprint: `claude-bj-pair.tex`.

* `volQ_pos`: `(ω^n) > 0` when `dim X = n` and `ω` has ample numerical class (SGPT.Foundations.Envelope's
  `mixedEulerDifference_replicate_pos_of_isAmple` for an ample representative);
* `isIso_subscheme_productFst`: the subscheme `X × {0}` of `X × ℙ¹` maps isomorphically to `X`;
* `interFormQ_central_omega`: `(𝒳₀ ⋅ (π^*ω)^n)_𝒳 = (ω^n)_X` on every blow-up model (cut formula
  along `X × {0}` on `X × ℙ¹`, birational invariance);
* `interFormQ_flagVert_omega_eq_zero`: `(E ⋅ (π^*ω)^n) = 0` for the divisor `E = (t^{λ} 𝔞) · 𝒪`
  of a flag ideal with `𝔞_λ ≠ 0`: `E` maps into the proper closed subset `V(𝔞_λ)` of `X` (cut
  formula, BJ-INTERSECT's pull-back vanishing);
* `phi_trivial_eq`: `φ_𝔞(v_triv) = max {λ : 𝔞_λ ≠ 0}`;
* `pairTriv` (**[BJ22, `equ:mixedMA0`]**): the axiom `PairTriv` of lane BJ-PAIR holds when
  `dim X = n ≥ 1`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.NAPotential.BJ

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Topology
open SGPT.NAPotential.Berkovich SGPT.NAPotential.BJModel SGPT.NAPotential.BJIntersect
open SGPT.NAPotential.BJHodge SGPT.NAPotential.BJ.NativePicard
open SGPT.Support.Alterations SGPT.Support.Alterations.Geometry
open FlagIdealBound

/-! ### Scalars in multilinear forms -/

theorem MultisetForm.map_replicate_smul {V : Type*} [AddCommGroup V] [Module ℚ V]
    (Φ : MultisetForm ℚ V) (c : ℚ) (x : V) :
    ∀ (k : ℕ) (t : Multiset V),
      Φ (Multiset.replicate k (c • x) + t) = c ^ k * Φ (Multiset.replicate k x + t) := by
  intro k
  induction k with
  | zero => intro t; simp
  | succ k ih =>
    intro t
    rw [Multiset.replicate_succ, Multiset.replicate_succ, Multiset.cons_add, Multiset.cons_add,
      Φ.map_smul, ← Multiset.add_cons, ih, ← Multiset.add_cons, pow_succ]
    ring

variable {X : Scheme.{0}} {p : X ⟶ Spec (.of ℂ)} [IsProjective p] [IsIntegral X]

local instance : IsProper p :=
  (SGPT.Foundations.Envelope.ProjectiveFactorizationRingIso.of_isProjective p).isProper

/-! ### The volume -/

section vol

variable [CompactSpace X] [X.IsSeparated] (n : ℕ) (hX : topologicalKrullDim X ≤ n)

omit [IsIntegral X] [CompactSpace X] [X.IsSeparated] in
theorem picQ_atlas_presentation (ω : RationalPicardSpace X) :
    ∃ (L : X.Modules) (hL : Scheme.Modules.IsInvertible L) (m : ℕ), 0 < m ∧
      ω = (1 / (m : ℚ)) • picQ ⟨L, hL⟩ ∧
      NativePicard.numericalClass p ω =
        (1 / (m : ℚ)) • SGPT.Foundations.Envelope.NativeRealNumericalClasses.lineClass p L hL := by
  obtain ⟨L, a, m, hm, rfl⟩ := exists_actual_line_presentation ω
  refine ⟨L, isInvertible_of_atlas a, m, hm, by rw [rationalPicardClass_eq_picQ a], ?_⟩
  rw [numericalClass_rat_smul, numericalClass_line]

/-- **`(ω^n) > 0`** for a rational class with ample numerical class on an integral projective `X`
of dimension `n` (an ample representative of a multiple of `ω` and SGPT.Foundations.Envelope's positivity
of top self-intersections of ample bundles). -/
theorem volQ_pos (hXn : topologicalKrullDim X = n) (ω : RationalPicardSpace X)
    (hω : NativePicard.numericalClass p ω ∈
      SGPT.Foundations.Envelope.NativeRealNumericalClasses.ampleCone p) :
    0 < volQ p n hX ω := by
  obtain ⟨L, hL, m, hm, rfl, hnum⟩ := picQ_atlas_presentation (p := p) ω
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hclass : SGPT.Foundations.Envelope.NativeRealNumericalClasses.lineClass p L hL ∈
      SGPT.Foundations.Envelope.NativeRealNumericalClasses.ampleCone p := by
    have h2 := (SGPT.Foundations.Envelope.NativeRealNumericalClasses.ampleCone p).smul_mem hmR hω
    rw [hnum, ← Rat.cast_smul_eq_qsmul ℝ, smul_smul] at h2
    have h3 : (m : ℝ) * (((1 / (m : ℚ)) : ℚ) : ℝ) = 1 := by
      push_cast
      field_simp
    rwa [h3, one_smul] at h2
  have hample := SGPT.Foundations.Envelope.Variety.isAmple_of_lineClass_mem_ampleCone p L hL hclass
  have hpos := SGPT.Foundations.Envelope.SeshadriAmplenessCriterion.mixedEulerDifference_replicate_pos_of_isAmple
    p n hXn L hample
  have hval : interFormQ p n hX (Scheme.Modules.unitObj X)
      (Multiset.replicate n (picQ ⟨L, hL⟩)) =
      SGPT.Foundations.Envelope.SeshadriAmplenessCriterion.mixedEulerDifference p
        (List.replicate n L) (Scheme.Modules.unitObj X) := by
    have := interFormQ_picQ p n hX (Scheme.Modules.unitObj X) (List.replicate n ⟨L, hL⟩)
      (by simp)
    simpa [List.map_replicate, Multiset.coe_replicate] using this
  have hsc := MultisetForm.map_replicate_smul (interFormQ p n hX (Scheme.Modules.unitObj X))
    (1 / (m : ℚ)) (picQ ⟨L, hL⟩) n 0
  simp only [add_zero] at hsc
  rw [volQ, hsc, hval]
  have hmq : (0 : ℚ) < 1 / (m : ℚ) := by positivity
  exact mul_pos (pow_pos hmq n) (by exact_mod_cast hpos)

end vol

/-! ### The central fibre maps isomorphically to `X` -/

section central

omit [IsProjective p] [IsIntegral X] in
theorem isIso_zeroIdeal_structure :
    IsIso ((zeroIdeal ℂ).subschemeι ≫ projectiveSpaceStructure ℂ 1) := by
  have h1 : (zeroPoint ℂ).toImage ≫ (zeroIdeal ℂ).subschemeι = zeroPoint ℂ :=
    (zeroPoint ℂ).toImage_imageι
  have h2 : (zeroIdeal ℂ).subschemeι ≫ projectiveSpaceStructure ℂ 1 =
      inv (zeroPoint ℂ).toImage := by
    rw [← cancel_epi (zeroPoint ℂ).toImage, ← Category.assoc, h1, zeroPoint_structure,
      IsIso.hom_inv_id]
  rw [h2]
  infer_instance

omit [IsProjective p] [IsIntegral X] in
/-- **`X × {0} ≅ X`**: the subscheme of the ideal of the central fibre maps isomorphically to `X`
under the first projection. -/
theorem isIso_subscheme_productFst (I : (productLine p).IdealSheafData)
    (hI : I = centralIdeal p) : IsIso (I.subschemeι ≫ productFst p) := by
  subst hI
  have := isIso_zeroIdeal_structure
  have e1 : (centralIdeal p).subschemeι =
      ((zeroIdeal ℂ).comapIso (productSnd p)).hom ≫ pullback.fst _ _ :=
    (Scheme.IdealSheafData.comapIso_hom_fst _ _).symm
  rw [e1, Category.assoc]
  change IsIso (((zeroIdeal ℂ).comapIso (productSnd p)).hom ≫
    pullback.fst (pullback.snd p (projectiveSpaceStructure ℂ 1)) (zeroIdeal ℂ).subschemeι ≫
      pullback.fst p (projectiveSpaceStructure ℂ 1))
  rw [← pullbackLeftPullbackSndIso_hom_fst p (projectiveSpaceStructure ℂ 1)
    (zeroIdeal ℂ).subschemeι]
  infer_instance

end central

/-! ### `(𝒳₀ ⋅ (π^*ω)^n) = (ω^n)` -/

section centralNumber

variable [CompactSpace X] [X.IsSeparated] (n : ℕ) (hX : topologicalKrullDim X ≤ n)
  (ω : PicQ X)

omit [CompactSpace X] [X.IsSeparated] in
theorem genericPoint_productLine_not_mem :
    genericPoint (productLine p) ∉ (centralIdeal p).support := by
  let := productLine_isIntegral_of_isProjective p
  intro hmem
  apply support_centralIdeal_ne_top p
  rw [eq_top_iff]
  intro z _
  have hcl : z ∈ closure ({genericPoint (productLine p)} : Set (productLine p)) := by
    rw [(genericPoint_spec (productLine p)).def]; trivial
  exact (closure_minimal (Set.singleton_subset_iff.mpr hmem)
    (centralIdeal p).support.isClosed) hcl

/-- **`(X₀ ⋅ (pr₁^*ω)^n)_{X × ℙ¹} = (ω^n)_X`** (cut formula along `X × {0} ≅ X`). -/
theorem interFormQ_productLine_central
    (hdimP : topologicalKrullDim (productLine p) ≤ (n + 1 : ℕ)) :
    interFormQ (productStructure p) (n + 1) hdimP
        (Scheme.Modules.unitObj _)
        (picQ ⟨cartierLine (centralIdeal p), cartierLine_isInvertible (centralIdeal_isInvertible p)⟩
          ::ₘ Multiset.replicate n (picPullbackQ (productFst p) ω)) =
      interFormQ p n hX (Scheme.Modules.unitObj X) (Multiset.replicate n ω) := by
  let := productLine_isIntegral_of_isProjective p
  have hI := centralIdeal_isInvertible p
  have hL := cartierLine_isInvertible hI
  have hs : cartierSection (centralIdeal p) hI ≠ 0 := by
    refine ne_zero_of_not_mem_support _ hL _ (genericPoint (productLine p)) ?_
    rw [zeroIdeal_cartierSection]
    exact genericPoint_productLine_not_mem
  have : IsProjective ((SGPT.Foundations.Envelope.LineSectionZeroIdeal.zeroIdeal (cartierLine (centralIdeal p))
      hL (cartierSection (centralIdeal p) hI)).subschemeι ≫ productStructure p) :=
    isProjective_closed_comp _ _
  rw [interFormQ_cut n (productStructure p) _ (cartierLine (centralIdeal p)) hL _ hs]
  set Z := SGPT.Foundations.Envelope.LineSectionZeroIdeal.zeroIdeal (cartierLine (centralIdeal p)) hL
    (cartierSection (centralIdeal p) hI)
  have hZ : Z = centralIdeal p := zeroIdeal_cartierSection _ hI
  have hiso := isIso_subscheme_productFst Z hZ
  let j := Z.subschemeι ≫ productFst p
  have hmap : (Multiset.replicate n (picPullbackQ (productFst p) ω)).map
      (picPullbackQ Z.subschemeι) = (Multiset.replicate n ω).map (picPullbackQ j) := by
    rw [Multiset.map_replicate, Multiset.map_replicate, picPullbackQ_comp]
  rw [hmap]
  have hst : Z.subschemeι ≫ productStructure p = j ≫ p := by
    simp only [j, productStructure, Category.assoc]
  have : IsProjective (j ≫ p) := by
    rw [← hst]; exact isProjective_closed_comp _ _
  let : CompactSpace Z.subscheme := QuasiCompact.compactSpace_of_compactSpace Z.subschemeι
  let : Z.subscheme.IsSeparated := isSeparated_of_closed Z.subschemeι
  have : Nonempty (⊤ : X.Opens) := by
    obtain ⟨x⟩ : Nonempty X := inferInstance
    exact ⟨⟨x, trivial⟩⟩
  rw [interFormQ_congr hst]
  exact BJProj.interFormQ_pullback_eq_of_isIso_restrict p j n hX _ ⊤ _

omit [CompactSpace X] [X.IsSeparated] in
/-- On a blow-up model, `𝓘 · 𝒪` is the pull-back of `𝓘` and `[𝒪(𝒳₀)] = π^*[𝒪(X × {0})]`. -/
theorem neg_picQ_centralLine_eq (𝔠 : FlagIdeal X) (c : ℤ) :
    -picQ (centralLine p 𝔠 c) = picPullbackQ (flagModelπ p 𝔠 c)
      (picQ ⟨cartierLine (centralIdeal p), cartierLine_isInvertible (centralIdeal_isInvertible p)⟩) := by
  let := productLine_isIntegral_of_isProjective p
  have := flagModelπ_isDominant p 𝔠 c
  have hI := centralIdeal_isInvertible p
  have hiso : IsIso ((centralIdeal p).toModulesComapPullbackMap (flagModelπ p 𝔠 c)) :=
    hI.toModulesComapPullbackMap_isIso_of_dominant_integral (flagModelπ p 𝔠 c)
  have h1 : picQ (centralLine p 𝔠 c) =
      picPullbackQ (flagModelπ p 𝔠 c) (picQ ⟨(centralIdeal p).toModules,
        hI.isInvertibleModule_toModules⟩) := by
    rw [picPullbackQ_picQ]
    exact (picQ_eq_of_iso _ _
      (asIso ((centralIdeal p).toModulesComapPullbackMap (flagModelπ p 𝔠 c)))).symm
  have h2 : picQ ⟨cartierLine (centralIdeal p), cartierLine_isInvertible hI⟩ =
      -picQ ⟨(centralIdeal p).toModules, hI.isInvertibleModule_toModules⟩ := by
    rw [picQ, picQ, lineCls_cartierLine hI, TensorProduct.tmul_neg]
  rw [h1, h2, map_neg]

/-- **`(𝒳₀ ⋅ (π^*ω)^n)_𝒳 = (ω^n)_X`** on every blow-up model ([BJ22, §3.2]). -/
theorem interFormQ_central_omega (𝔠 : FlagIdeal X) (c : ℤ) :
    interFormQ (flagModelStructure p 𝔠 c) (n + 1) (topologicalKrullDim_flagModel_le p 𝔠 c n hX)
        (Scheme.Modules.unitObj _)
        (-picQ (centralLine p 𝔠 c) ::ₘ Multiset.replicate n (omegaPullback 𝔠 c ω)) =
      interFormQ p n hX (Scheme.Modules.unitObj X) (Multiset.replicate n ω) := by
  let := productLine_isIntegral_of_isProjective p
  let := isLocallyNoetherian_of_isProjective p
  rw [← interFormQ_productLine_central n hX ω (topologicalKrullDim_productLine_le p n hX)]
  have hmap : (-picQ (centralLine p 𝔠 c) ::ₘ Multiset.replicate n (omegaPullback 𝔠 c ω)) =
      (picQ ⟨cartierLine (centralIdeal p), cartierLine_isInvertible (centralIdeal_isInvertible p)⟩
        ::ₘ Multiset.replicate n (picPullbackQ (productFst p) ω)).map
        (picPullbackQ (flagModelπ p 𝔠 c)) := by
    rw [Multiset.map_cons, Multiset.map_replicate, neg_picQ_centralLine_eq,
      omegaPullback_eq_picPullbackQ, picPullbackQ_comp]
  rw [hmap]
  have : Nonempty ((flagSheaf p 𝔠 c).support.compl : (productLine p).Opens) := by
    obtain ⟨z, hz⟩ : ∃ z, z ∉ (flagSheaf p 𝔠 c).support := by
      by_contra h
      push Not at h
      exact support_flagSheaf_ne_top p 𝔠 c (eq_top_iff.mpr fun z _ => h z)
    exact ⟨⟨z, hz⟩⟩
  have : IsIso (flagModelπ p 𝔠 c ∣_ (flagSheaf p 𝔠 c).support.compl) :=
    flagModelπ_isIso_restrict p 𝔠 c
  exact BJProj.interFormQ_pullback_eq_of_isIso_restrict (productStructure p) (flagModelπ p 𝔠 c)
    (n + 1) _ _ (flagSheaf p 𝔠 c).support.compl _

/-! ### Divisors of flag ideals mapping into a proper closed subset -/

omit [CompactSpace X] [X.IsSeparated] in
/-- **`(E ⋅ (π^*ω)^n) = 0`** for the divisor `E = (t^λ 𝔞) · 𝒪` of a flag datum with `𝔞_λ ≠ 0`
(`dim X = n ≥ 1`): `E` maps into the proper closed subset `V(𝔞_λ)` of `X`. -/
theorem interFormQ_flagVert_omega_eq_zero (hXn : topologicalKrullDim X = n) (hn : 0 < n)
    {𝔠 : FlagIdeal X} {c : ℤ} (e : FlagDatum p 𝔠 c) (he : e.ideal.ideal e.bound ≠ ⊥) :
    interFormQ (flagModelStructure p 𝔠 c) (n + 1) (topologicalKrullDim_flagModel_le p 𝔠 c n hX)
        (Scheme.Modules.unitObj _)
        (-picQ e.vert.line ::ₘ Multiset.replicate n (omegaPullback 𝔠 c ω)) = 0 := by
  obtain ⟨d, rfl⟩ : ∃ d, n = d + 1 := ⟨n - 1, by omega⟩
  have hJ : e.vert.ideal.IsInvertible := e.isInvertible
  have hL := cartierLine_isInvertible hJ
  have hcart : -picQ e.vert.line = picQ ⟨cartierLine e.vert.ideal, hL⟩ := by
    rw [picQ, picQ, lineCls_cartierLine hJ, TensorProduct.tmul_neg]
    rfl
  -- the section is nonzero: the generic point is not in the central fibre
  have hs : cartierSection e.vert.ideal hJ ≠ 0 := by
    refine ne_zero_of_not_mem_support _ hL _ (genericPoint (flagModel p 𝔠 c)) ?_
    rw [zeroIdeal_cartierSection]
    intro hmem
    have h1 := e.vert.support_subset hmem
    change flagModelπ p 𝔠 c (genericPoint (flagModel p 𝔠 c)) ∈ (centralIdeal p).support at h1
    rw [(flagModelπ_genericPoint p 𝔠 c).1] at h1
    exact genericPoint_productLine_not_mem h1
  have : IsProjective ((SGPT.Foundations.Envelope.LineSectionZeroIdeal.zeroIdeal (cartierLine e.vert.ideal)
      hL (cartierSection e.vert.ideal hJ)).subschemeι ≫ flagModelStructure p 𝔠 c) :=
    isProjective_closed_comp _ _
  rw [hcart, interFormQ_cut (d + 1) (flagModelStructure p 𝔠 c) _ _ hL _ hs]
  set Z := SGPT.Foundations.Envelope.LineSectionZeroIdeal.zeroIdeal (cartierLine e.vert.ideal) hL
    (cartierSection e.vert.ideal hJ)
  have hZ : Z = e.vert.ideal := zeroIdeal_cartierSection _ hJ
  let g := Z.subschemeι ≫ flagModelπ p 𝔠 c ≫ productFst p
  have hmap : (Multiset.replicate (d + 1) (omegaPullback 𝔠 c ω)).map
      (picPullbackQ Z.subschemeι) = (Multiset.replicate (d + 1) ω).map (picPullbackQ g) := by
    rw [Multiset.map_replicate, Multiset.map_replicate, omegaPullback_eq_picPullbackQ,
      ← picPullbackQ_comp]
  rw [hmap]
  -- write `ω = m⁻¹ [L]`
  obtain ⟨L, hLX, m, hm, rfl, -⟩ := picQ_atlas_presentation (p := p) ω
  let : CompactSpace Z.subscheme := QuasiCompact.compactSpace_of_compactSpace Z.subschemeι
  let : Z.subscheme.IsSeparated := isSeparated_of_closed Z.subschemeι
  have hsc := MultisetForm.map_replicate_smul
    (interFormQ (Z.subschemeι ≫ flagModelStructure p 𝔠 c) (d + 1)
      (SGPT.Foundations.Envelope.SeshadriAmplenessCriterion.sectionZero_dimension_drop (d + 1) (topologicalKrullDim_flagModel_le p 𝔠 c (d + 1) hX)
        (cartierLine e.vert.ideal) hL _ hs) (Scheme.Modules.unitObj _))
    (1 / (m : ℚ)) (picPullbackQ g (picQ ⟨L, hLX⟩)) (d + 1) 0
  simp only [add_zero] at hsc
  rw [Multiset.map_replicate, map_smul, hsc, picPullbackQ_picQ]
  apply mul_eq_zero_of_right
  have hst : Z.subschemeι ≫ flagModelStructure p 𝔠 c = g ≫ p := by
    simp only [g, flagModelStructure, productStructure, Category.assoc]
  have : IsProjective (g ≫ p) := by
    rw [← hst]; exact isProjective_closed_comp _ _
  have hval := interFormQ_picQ (Z.subschemeι ≫ flagModelStructure p 𝔠 c) (d + 1)
    (SGPT.Foundations.Envelope.SeshadriAmplenessCriterion.sectionZero_dimension_drop (d + 1) (topologicalKrullDim_flagModel_le p 𝔠 c (d + 1) hX)
      (cartierLine e.vert.ideal) hL _ hs) (Scheme.Modules.unitObj _)
    (List.replicate (d + 1) ⟨(Scheme.Modules.pullback g).obj L, hLX.pullback g⟩) (by simp)
  simp only [List.map_replicate] at hval
  rw [← Multiset.coe_replicate, hval]
  have hlist : List.replicate (d + 1) ((Scheme.Modules.pullback g).obj L) =
      (List.replicate (d + 1) L).map (Scheme.Modules.pullback g).obj :=
    List.map_replicate.symm
  rw [hlist, hst]
  -- the image lies in `V(𝔞_λ)`, of dimension `≤ d`
  let C : TopologicalSpace.Closeds X := (e.ideal.ideal e.bound).support
  have hC : C ≠ ⊤ := by
    intro htop
    have hgen := stalkIdeal_genericPoint_eq_top he
    have hmem : genericPoint X ∈ C := by rw [htop]; trivial
    rw [Scheme.IdealSheafData.mem_support_iff_stalkIdeal_le_maximalIdeal] at hmem
    rw [berkovich_stalkIdeal_eq] at hgen
    rw [hgen] at hmem
    exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top (top_le_iff.mp hmem)
  have hdimC : topologicalKrullDim C ≤ d :=
    SGPT.Foundations.Envelope.SeshadriAmplenessCriterion.properClosed_dimension_drop C hC d (hXn ▸ le_refl _)
  have hrange : Set.range g ⊆ (C : Set X) := by
    rintro _ ⟨x, rfl⟩
    have hx0 : Z.subschemeι x ∈ (Z.support : Set (flagModel p 𝔠 c)) := by
      rw [← Scheme.IdealSheafData.range_subschemeι]; exact ⟨x, rfl⟩
    have hsupp : (Z.support : Set (flagModel p 𝔠 c)) = e.vert.ideal.support := by
      rw [hZ]
    have hx : Z.subschemeι x ∈
        (((flagSheaf p e.ideal e.bound).comap (flagModelπ p 𝔠 c)).support : Set _) := by
      have h' : (e.vert.ideal.support : Set (flagModel p 𝔠 c)) =
          (((flagSheaf p e.ideal e.bound).comap (flagModelπ p 𝔠 c)).support : Set _) := rfl
      rw [← h', ← hsupp]; exact hx0
    rw [Scheme.IdealSheafData.support_comap] at hx
    have hle : (e.ideal.ideal (e.bound - ((0 : ℕ) : ℤ))).comap (productFst p) *
        centralIdeal p ^ (0 : ℕ) ≤ flagSheaf p e.ideal e.bound := le_flagSheaf p e.ideal e.bound 0
    rw [pow_zero, Scheme.IdealSheafData.one_eq_top, Scheme.IdealSheafData.mul_top, Nat.cast_zero,
      sub_zero] at hle
    have hx2 := Scheme.IdealSheafData.support_antitone hle hx
    rw [Scheme.IdealSheafData.support_comap] at hx2
    exact hx2
  exact_mod_cast mixedEulerDifference_pullback_eq_zero p g (C : Set X) C.isClosed hrange
    (List.replicate (d + 1) L) (fun K hK => (List.eq_of_mem_replicate hK) ▸ hLX) (by simp)
    (by
      rw [List.length_replicate]
      exact lt_of_le_of_lt hdimC (by exact_mod_cast Nat.lt_succ_self d))
    (Scheme.Modules.unitObj _)

end centralNumber

/-! ### `φ_𝔞(v_triv)` -/

section triv

/-- **`φ_𝔞(v_triv) = λ₀`** for the largest weight `λ₀` with `𝔞_{λ₀} ≠ 0`. -/
theorem phi_trivial_eq (𝔞 : FlagIdeal X) {l₀ : ℤ} (hl₀ : 𝔞.ideal l₀ ≠ ⊥)
    (hmax : ∀ l, l₀ < l → 𝔞.ideal l = ⊥) : 𝔞.phi (BerkovichPoint.trivial p) = l₀ := by
  let := isLocallyNoetherian_of_isProjective p
  apply le_antisymm (𝔞.phi_le _ hmax)
  have h := 𝔞.ofReal_sub_phi_le (BerkovichPoint.trivial p) l₀
  rw [BerkovichPoint.trivial_idealVal_eq_zero hl₀, nonpos_iff_eq_zero,
    ENNReal.ofReal_eq_zero] at h
  linarith

/-- The largest weight `λ₀` with `𝔞_{λ₀} ≠ 0`. -/
theorem exists_max_weight (𝔞 : FlagIdeal X) :
    ∃ l₀ : ℤ, 𝔞.ideal l₀ ≠ ⊥ ∧ ∀ l, l₀ < l → 𝔞.ideal l = ⊥ := by
  classical
  obtain ⟨b, hb⟩ := FlagIdealBound.exists_isWeightBound 𝔞
  obtain ⟨a, ha⟩ := 𝔞.exists_eq_top
  have htop : (⊤ : X.IdealSheafData) ≠ ⊥ := by
    intro h
    obtain ⟨x⟩ : Nonempty X := inferInstance
    have h1 := Scheme.IdealSheafData.stalkIdeal_top x
    rw [h, Scheme.IdealSheafData.stalkIdeal_bot] at h1
    exact bot_ne_top h1
  obtain ⟨l₀, hl₀, hmax⟩ := Int.exists_greatest_of_bdd (P := fun l => 𝔞.ideal l ≠ ⊥)
    ⟨b, fun z hz => by
      by_contra h
      exact hz (hb z (lt_of_not_ge h))⟩ ⟨a, by rw [ha a le_rfl]; exact htop⟩
  exact ⟨l₀, hl₀, fun l hl => by
    by_contra h
    exact absurd (hmax l h) (not_le.mpr hl)⟩

end triv

/-! ### `equ:mixedMA0` -/

section pairTriv

variable [CompactSpace X] [X.IsSeparated] (n : ℕ) (hX : topologicalKrullDim X ≤ n)
  (ω : PicQ X)

theorem flagPair_triv_phi (hXn : topologicalKrullDim X = n) (hn : 0 < n) (𝔞 : FlagIdeal X) :
    (flagPair n hX ω (((0 : ℚ), 𝔞.phi) ::ₘ
        Multiset.replicate n ((1 : ℚ), (0 : BerkovichPoint p → ℝ))) : ℝ) =
      volQ p n hX ω * 𝔞.phi (BerkovichPoint.trivial p) := by
  classical
  obtain ⟨l₀, hl₀, hmax⟩ := exists_max_weight 𝔞
  have hb : IsWeightBound 𝔞 l₀ := hmax
  obtain ⟨hgood, hdom⟩ := isGoodModel_mul_monomial p hb
  set 𝔠 := 𝔞 * FlagIdeal.monomial X 0
  set c := l₀ + 1
  let e := FlagDatum.ofDominates hdom hb
  let D : FDiv p 𝔠 c := Finsupp.single (centralDatum hgood) (l₀ : ℚ) - Finsupp.single e 1
  have hD : FDiv.fn D = 𝔞.phi := by
    funext v
    simp only [D, map_sub, FDiv.fn_single, fn_centralDatum, Pi.sub_apply, Pi.smul_apply,
      FlagDatum.fn_vert, e, FlagDatum.ofDominates, Rat.smul_def, one_smul, Rat.cast_intCast,
      mul_one]
    ring
  let R : (BerkovichPoint p → ℝ) → FDiv p 𝔠 c := fun φ => if φ = 𝔞.phi then D else 0
  have hRphi : R 𝔞.phi = D := if_pos rfl
  have hR0 : FDiv.fn (R 0) = 0 := by
    by_cases h0 : (0 : BerkovichPoint p → ℝ) = 𝔞.phi
    · rw [show R 0 = D from if_pos h0, hD, h0]
    · rw [show R 0 = 0 from if_neg h0, map_zero]
  have hR : ∀ x ∈ (((0 : ℚ), 𝔞.phi) ::ₘ
      Multiset.replicate n ((1 : ℚ), (0 : BerkovichPoint p → ℝ))), FDiv.fn (R x.2) = x.2 := by
    intro x hx
    rcases Multiset.mem_cons.mp hx with rfl | hx
    · exact hRphi ▸ hD
    · rw [Multiset.eq_of_mem_replicate hx]
      exact hR0
  rw [flagPair_eq n hX ω hgood _ (fun x hx => ⟨R x.2, hR x hx⟩),
    ← interFormQ_flag_eq_modelValue n hX ω hgood _ R hR]
  simp only [Multiset.map_cons, Multiset.map_replicate]
  -- `R 0` only matters through `ν^*`, where it vanishes
  have hν : picPullbackQ (normModelν p 𝔠 c) ((1 : ℚ) • omegaPullback 𝔠 c ω + FDiv.cls (R 0)) =
      picPullbackQ (normModelν p 𝔠 c) (omegaPullback 𝔠 c ω) := by
    have h0 : picPullbackQ (normModelν p 𝔠 c) (FDiv.cls (R 0)) = 0 :=
      FDiv.ncls_eq_zero hgood.central_isInvertible (R 0) hR0
    rw [map_add, one_smul, h0, add_zero]
  have hzero : ∀ a : PicQ (flagModel p 𝔠 c),
      interFormQ (flagModelStructure p 𝔠 c) (n + 1) (topologicalKrullDim_flagModel_le p 𝔠 c n hX)
        (Scheme.Modules.unitObj _) (a ::ₘ Multiset.replicate n
          ((1 : ℚ) • omegaPullback 𝔠 c ω + FDiv.cls (R 0))) =
      interFormQ (flagModelStructure p 𝔠 c) (n + 1) (topologicalKrullDim_flagModel_le p 𝔠 c n hX)
        (Scheme.Modules.unitObj _) (a ::ₘ Multiset.replicate n (omegaPullback 𝔠 c ω)) := by
    intro a
    rw [← interFormQ_normModel p 𝔠 c (n + 1), ← interFormQ_normModel p 𝔠 c (n + 1),
      Multiset.map_cons, Multiset.map_cons, Multiset.map_replicate, Multiset.map_replicate, hν]
  rw [hzero, zero_smul, zero_add, hRphi]
  simp only [D, map_sub, FDiv.cls_single, picQ_centralDatum, one_smul]
  rw [MultisetForm.map_sub, MultisetForm.map_smul, interFormQ_central_omega n hX ω,
    interFormQ_flagVert_omega_eq_zero n hX ω hXn hn e hl₀,
    phi_trivial_eq 𝔞 hl₀ hmax, volQ]
  push_cast
  ring

/-- **[BJ22, `equ:mixedMA0`]**: `(0, f) ⋅ (ω, 0)^n = (ω^n) f(v_triv)` for every PL function `f`,
when `dim X = n ≥ 1`. This is the axiom `PairTriv` of lane BJ-PAIR. -/
theorem pairTriv (hXn : topologicalKrullDim X = n) (hn : 0 < n) : PairTriv p n hX ω := by
  intro f hf
  have hrest : ∀ z ∈ Multiset.replicate n ((1 : ℚ), (0 : BerkovichPoint p → ℝ)),
      z.2 ∈ plSubmodule p := fun z hz => by
    rw [Multiset.eq_of_mem_replicate hz]; exact Submodule.zero_mem _
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨𝔞, rfl⟩ := hx
    exact flagPair_triv_phi n hX ω hXn hn 𝔞
  | zero =>
    have h := flagPair_cons_smul n hX ω 0 ((0 : ℚ), (0 : BerkovichPoint p → ℝ)) _
      (Submodule.zero_mem _) hrest
    rw [zero_smul, zero_mul] at h
    rw [show ((0 : ℚ), (0 : BerkovichPoint p → ℝ)) = (0 : ℚ × (BerkovichPoint p → ℝ)) from rfl, h]
    simp
  | add x y hx' hy' hx hy =>
    have h := flagPair_cons_add n hX ω ((0 : ℚ), x) ((0 : ℚ), y) _ hx' hy' hrest
    rw [show ((0 : ℚ), x + y) = ((0 : ℚ), x) + ((0 : ℚ), y) by rw [Prod.mk_add_mk, add_zero], h]
    push_cast
    rw [hx, hy, Pi.add_apply]
    ring
  | smul q x hx' hx =>
    have h := flagPair_cons_smul n hX ω q ((0 : ℚ), x) _ hx' hrest
    rw [show ((0 : ℚ), q • x) = q • ((0 : ℚ), x) by rw [Prod.smul_mk, smul_zero], h]
    push_cast
    rw [hx, Pi.smul_apply, Rat.smul_def]
    ring

end pairTriv

end SGPT.NAPotential.BJ
