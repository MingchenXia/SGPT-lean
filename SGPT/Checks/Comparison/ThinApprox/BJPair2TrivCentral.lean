import SGPT.Checks.Comparison.ThinApprox.BJPair2TrivBase
import SGPT.Checks.Comparison.ThinApprox.TrivialIdeal
import SGPT.Foundations.Envelope.AlgGeom.SeshadriAmplenessCriterionDimensionDrop

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SGPT.NAPotential.ThinApprox.BJ
open SGPT.NAPotential.BJ

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Topology
open SGPT.NAPotential.Berkovich SGPT.NAPotential.BJModel SGPT.NAPotential.ThinApprox.BJModel SGPT.NAPotential.BJIntersect
open SGPT.NAPotential.BJHodge SGPT.NAPotential.BJ.NativePicard
open SGPT.Support.Alterations SGPT.Support.Alterations.Geometry
open FlagIdealBound

variable {X : Scheme.{0}} {p : X ⟶ Spec (.of ℂ)} [IsProjective p] [IsIntegral X]

local instance : IsProper p :=
  (SGPT.Foundations.Envelope.ProjectiveFactorizationRingIso.of_isProjective p).isProper

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
    rw [SGPT.NAPotential.BJ.picPullbackQ_picQ]
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
  rw [Multiset.map_replicate, map_smul, hsc, SGPT.NAPotential.BJ.picPullbackQ_picQ]
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
    have hgen := SGPT.NAPotential.ThinApprox.TrivialIdeal.stalkIdeal_genericPoint_eq_top he
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


end SGPT.NAPotential.ThinApprox.BJ
