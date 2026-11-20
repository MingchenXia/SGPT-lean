import SGPT.Convex.GrowthClasses
import SGPT.Convex.FiniteQualifiedConjugation
import Mathlib.Topology.Algebra.Group.Pointwise

namespace SGPT.Convex
open Set Filter
open scoped Topology Pointwise

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Actual set addition and the genuine independent support suprema give the exact support sum. -/
theorem support_add (B : F →ₗ[ℝ] E →ₗ[ℝ] ℝ) (P Q : Set F) :
    support B (P + Q) = fun x ↦ support B P x + support B Q x := by
  funext x
  apply le_antisymm
  · apply iSup_le
    intro z
    obtain ⟨a, ha, b, hb, hab⟩ := Set.mem_add.mp z.property
    change (B z x : EReal) ≤ _
    rw [← hab, map_add, LinearMap.add_apply, EReal.coe_add]
    exact add_le_add (le_iSup (fun a : P ↦ (B a x : EReal)) ⟨a, ha⟩)
      (le_iSup (fun b : Q ↦ (B b x : EReal)) ⟨b, hb⟩)
  · change (⨆ a : P, (B a x : EReal)) + (⨆ b : Q, (B b x : EReal)) ≤ _
    rw [iSup_add_iSup]
    apply iSup_le
    intro a
    apply iSup_le
    intro b
    have h := le_iSup (fun z : P + Q ↦ (B z x : EReal))
      ⟨a + b, Set.add_mem_add a.property b.property⟩
    simpa only [support, map_add, LinearMap.add_apply, EReal.coe_add] using h

variable [FiniteDimensional ℝ E]

/-- The actual perfect pairing transports the already produced genuine attaining split. -/
theorem exists_split_of_conjugate_ne_top_of_isContPerfPair
    (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) [B.IsContPerfPair] {f g : E → EReal}
    (hf : IsProper f) (hg : IsProper g) (m : F) {x₀ : E}
    (hx₀ : x₀ ∈ intrinsicInterior ℝ (effectiveDomain f))
    (hx₀' : x₀ ∈ intrinsicInterior ℝ (effectiveDomain g))
    (hfinite : conjugate B (fun x ↦ f x + g x) m ≠ ⊤) :
    ∃ ℓ : F, conjugate B f ℓ + conjugate B g (m - ℓ) =
      conjugate B (fun x ↦ f x + g x) m := by
  let e : F ≃ₗ[ℝ] StrongDual ℝ E := B.flip.toContPerfPair
  obtain ⟨ℓ, hℓ⟩ := exists_split_of_conjugate_ne_top hf hg (e m) hx₀ hx₀' hfinite
  refine ⟨e.symm ℓ, ?_⟩
  change conjugate continuousDualPairing f (e (e.symm ℓ)) +
    conjugate continuousDualPairing g (e (m - e.symm ℓ)) = _
  rw [e.apply_symm_apply, map_sub, e.apply_symm_apply]
  exact hℓ

omit [FiniteDimensional ℝ E] in
/-- Every true covector split gives the existing actual weak-duality bound. -/
theorem conjugate_add_le_split_of_isContPerfPair
    (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) [B.IsContPerfPair] {f g : E → EReal}
    (hf : IsProper f) (hg : IsProper g) (m ℓ : F) :
    conjugate B (fun x ↦ f x + g x) m ≤ conjugate B f ℓ + conjugate B g (m - ℓ) := by
  let e : F ≃ₗ[ℝ] StrongDual ℝ E := B.flip.toContPerfPair
  have h := conjugate_add_le_split hf hg (e m) (e ℓ)
  change conjugate continuousDualPairing (fun x ↦ f x + g x) (e m) ≤
    conjugate continuousDualPairing f (e ℓ) + conjugate continuousDualPairing g (e (m - ℓ))
  simpa only [← map_sub] using h

/-- Genuine common relative-interior qualification makes the actual conjugate domain additive. -/
theorem effectiveDomain_conjugate_add_of_common_intrinsicInterior
    (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) [B.IsContPerfPair] {f g : E → EReal}
    (hf : IsProper f) (hg : IsProper g) {x₀ : E}
    (hx₀ : x₀ ∈ intrinsicInterior ℝ (effectiveDomain f))
    (hx₀' : x₀ ∈ intrinsicInterior ℝ (effectiveDomain g)) :
    effectiveDomain (conjugate B (fun x ↦ f x + g x)) =
      effectiveDomain (conjugate B f) + effectiveDomain (conjugate B g) := by
  have hcf := isProper_conjugate_of_isContPerfPair B hf
  have hcg := isProper_conjugate_of_isContPerfPair B hg
  ext m
  constructor
  · intro hm
    obtain ⟨ℓ, hℓ⟩ := exists_split_of_conjugate_ne_top_of_isContPerfPair B hf hg m
      hx₀ hx₀' (ne_of_lt hm)
    have hnt : conjugate B f ℓ + conjugate B g (m - ℓ) ≠ ⊤ := by
      rw [hℓ]
      exact ne_of_lt hm
    obtain ⟨hl, hr⟩ := (EReal.add_ne_top_iff_ne_top₂ (hcf.2.2 _) (hcg.2.2 _)).mp hnt
    exact Set.mem_add.mpr ⟨ℓ, lt_top_iff_ne_top.mpr hl,
      m - ℓ, lt_top_iff_ne_top.mpr hr, by abel⟩
  · intro hm
    obtain ⟨ℓ, hl, r, hr, hsum⟩ := Set.mem_add.mp hm
    have hfinite : conjugate B f ℓ + conjugate B g r < ⊤ :=
      lt_top_iff_ne_top.mpr ((EReal.add_ne_top_iff_ne_top₂ (hcf.2.2 _) (hcg.2.2 _)).mpr
        ⟨ne_of_lt hl, ne_of_lt hr⟩)
    have heq : m - ℓ = r := by rw [← hsum]; abel
    have hbound := conjugate_add_le_split_of_isContPerfPair B hf hg m ℓ
    rw [heq] at hbound
    exact hbound.trans_lt hfinite

/-- Every actual full-domain proper convex function is source closed, by the existing closure agreement. -/
theorem isClosedConvex_of_isProper_full_domain {f : E → EReal}
    (hf : IsProper f) (hdom : effectiveDomain f = univ) : IsClosedConvex f := by
  apply (convexClosure_eq_self_iff_isClosedConvex hf.1).mp
  funext x
  rw [convexClosure_of_forall_ne_bot hf.2.2]
  apply regularization_eq_of_mem_intrinsicInterior hf
  apply interior_subset_intrinsicInterior
  simp [hdom]

omit [FiniteDimensional ℝ E] [NormedSpace ℝ F] in
/-- Genuine compact-plus-closed geometry gives the exact closure of the actual Minkowski sum. -/
theorem closure_add_of_isCompact_closure (s t : Set F) (hs : IsCompact (closure s)) :
    closure (s + t) = closure s + closure t := by
  apply subset_antisymm
  · exact closure_minimal (Set.add_subset_add subset_closure subset_closure)
      (isClosed_closure.add_left_of_isCompact hs)
  · rintro x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_add.mp hx
    have hp : (a, b) ∈ closure (s ×ˢ t) := by
      rw [closure_prod_eq]
      exact ⟨ha, hb⟩
    have h := image_closure_subset_closure_image
      (continuous_fst.add continuous_snd : Continuous (fun p : F × F ↦ p.1 + p.2))
      (mem_image_of_mem (fun p : F × F ↦ p.1 + p.2) hp)
    change a + b ∈ closure ((fun p : F × F ↦ p.1 + p.2) '' (s ×ˢ t)) at h
    rwa [Set.add_image_prod] at h

omit [FiniteDimensional ℝ E] in
/-- Actual original growth constants add using genuine finite support values. -/
theorem mem_growthClass_add
    (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) [B.IsContPerfPair] {P Q : Set F}
    (hP : IsCompact P) (hneP : P.Nonempty) (hQ : IsCompact Q) (hneQ : Q.Nonempty)
    {f g : E → EReal} (hf : f ∈ GrowthClass B P) (hg : g ∈ GrowthClass B Q) :
    (fun x ↦ f x + g x) ∈ GrowthClass B (P + Q) := by
  have hdf := effectiveDomain_eq_univ_of_mem_growthClass B hP hneP hf
  have hdg := effectiveDomain_eq_univ_of_mem_growthClass B hQ hneQ hg
  have hzero : (0 : E) ∈ effectiveDomain f := by simp [hdf]
  have hzero' : (0 : E) ∈ effectiveDomain g := by simp [hdg]
  refine ⟨isProper_add_of_common_domain hf.1 hg.1 hzero hzero', ?_⟩
  obtain ⟨C, hC⟩ := (SGPT.PSH.singularityLE_iff_exists_real _ _).mp hf.2
  obtain ⟨D, hD⟩ := (SGPT.PSH.singularityLE_iff_exists_real _ _).mp hg.2
  apply (SGPT.PSH.singularityLE_iff_exists_real _ _).mpr
  refine ⟨C + D, fun x ↦ ?_⟩
  obtain ⟨a, ha⟩ := exists_real_support_value B hP hneP x
  obtain ⟨b, hb⟩ := exists_real_support_value B hQ hneQ x
  have h := add_le_add (hC x) (hD x)
  rw [ha, hb, ← EReal.coe_add, ← EReal.coe_add, ← EReal.coe_add] at h
  rw [support_add]
  change f x + g x ≤ support B.flip P x + support B.flip Q x + ((C + D : ℝ) : EReal)
  rw [ha, hb, ← EReal.coe_add, ← EReal.coe_add]
  convert h using 1
  congr 1
  ring

variable [FiniteDimensional ℝ F]

/-- Exact source raw-image equality for actual finite convex inputs and an actual bounded conjugate domain. -/
theorem closure_rawSubgradientImage_add_of_full_domain
    (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) [B.IsContPerfPair] {f g : E → EReal}
    (hf : IsProper f) (hg : IsProper g)
    (hdf : effectiveDomain f = univ) (hdg : effectiveDomain g = univ)
    (hb : Bornology.IsBounded (effectiveDomain (conjugate B f))) :
    closure (rawSubgradientImage B (fun x ↦ f x + g x)) =
      closure (rawSubgradientImage B f) + closure (rawSubgradientImage B g) := by
  have hzero : (0 : E) ∈ effectiveDomain f := by simp [hdf]
  have hzero' : (0 : E) ∈ effectiveDomain g := by simp [hdg]
  have hsum := isProper_add_of_common_domain hf hg hzero hzero'
  have hdsum : effectiveDomain (fun x ↦ f x + g x) = univ := by
    rw [effectiveDomain_add_of_isProper hf hg, hdf, hdg, inter_self]
  have hri : (0 : E) ∈ intrinsicInterior ℝ (effectiveDomain f) := by
    apply interior_subset_intrinsicInterior
    simp [hdf]
  have hri' : (0 : E) ∈ intrinsicInterior ℝ (effectiveDomain g) := by
    apply interior_subset_intrinsicInterior
    simp [hdg]
  rw [closure_rawSubgradientImage_eq_closure_effectiveDomain_conjugate B hsum
      (lowerSemicontinuous_of_isClosedConvex (isClosedConvex_of_isProper_full_domain hsum hdsum)),
    closure_rawSubgradientImage_eq_closure_effectiveDomain_conjugate B hf
      (lowerSemicontinuous_of_isClosedConvex (isClosedConvex_of_isProper_full_domain hf hdf)),
    closure_rawSubgradientImage_eq_closure_effectiveDomain_conjugate B hg
      (lowerSemicontinuous_of_isClosedConvex (isClosedConvex_of_isProper_full_domain hg hdg)),
    effectiveDomain_conjugate_add_of_common_intrinsicInterior B hf hg hri hri',
    closure_add_of_isCompact_closure _ _ hb.isCompact_closure]

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- Real-valued convex functions genuinely give proper full-domain obstacles. -/
theorem isProper_coe_of_convexOn {f : E → ℝ} (hf : ConvexOn ℝ univ f) :
    IsProper (fun x ↦ (f x : EReal)) :=
  ⟨isConvex_coe_iff.mpr hf, ⟨0, EReal.coe_lt_top _⟩, fun x ↦ EReal.coe_ne_bot (f x)⟩

/-- Exact middle source clause for the original real-valued convex functions. -/
theorem closure_rawSubgradientImage_add_coe
    (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) [B.IsContPerfPair] {f g : E → ℝ}
    (hf : ConvexOn ℝ univ f) (hg : ConvexOn ℝ univ g)
    (hb : Bornology.IsBounded (effectiveDomain (conjugate B (fun x ↦ (f x : EReal))))) :
    closure (rawSubgradientImage B (fun x ↦ ((f x + g x : ℝ) : EReal))) =
      closure (rawSubgradientImage B (fun x ↦ (f x : EReal))) +
        closure (rawSubgradientImage B (fun x ↦ (g x : EReal))) := by
  have hdf : effectiveDomain (fun x ↦ (f x : EReal)) = univ := by
    ext x
    simp [effectiveDomain]
  have hdg : effectiveDomain (fun x ↦ (g x : EReal)) = univ := by
    ext x
    simp [effectiveDomain]
  simpa only [EReal.coe_add] using closure_rawSubgradientImage_add_of_full_domain B
    (isProper_coe_of_convexOn hf) (isProper_coe_of_convexOn hg) hdf hdg hb

/-- Exact final original full-image hypothesis produces membership in the actual full-mass sum class. -/
theorem mem_fullMassClass_add_of_image_closure_eq
    (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) [B.IsContPerfPair] {P Q : Set F}
    (hP : IsCompact P) (hneP : P.Nonempty) (hconvP : Convex ℝ P)
    (hQ : IsCompact Q) (hneQ : Q.Nonempty)
    {f g : E → EReal} (hf : f ∈ GrowthClass B P) (hg : g ∈ GrowthClass B Q)
    (himagef : closure (rawSubgradientImage B f) = P)
    (himageg : closure (rawSubgradientImage B g) = Q) :
    (fun x ↦ f x + g x) ∈ FullMassClass B (P + Q) := by
  refine ⟨mem_growthClass_add B hP hneP hQ hneQ hf hg, Or.inr ?_⟩
  have hsub : effectiveDomain (conjugate B f) ⊆ P := by
    intro m hm
    by_contra hout
    exact (ne_of_lt hm) (conjugate_eq_top_of_singularityLE_support B hP hconvP hf.1 hf.2 hout)
  rw [closure_rawSubgradientImage_add_of_full_domain B hf.1 hg.1
    (effectiveDomain_eq_univ_of_mem_growthClass B hP hneP hf)
    (effectiveDomain_eq_univ_of_mem_growthClass B hQ hneQ hg)
    (hP.isBounded.subset hsub), himagef, himageg]

end SGPT.Convex
