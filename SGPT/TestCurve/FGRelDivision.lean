import SGPT.LineBundle.SectionRing

/-!
# Division of sections by a family without common zeros

See [BHJ17, Prop. 2.15]. Let `M` be a line bundle with an atlas on a scheme `Y`,
`Ξ_i ∈ H⁰(Y, M^e)` a finite family of sections without common zeros (on every chart `U_c` the
basic opens of the coefficients of the `Ξ_i` cover `U_c`) and `Σ_i ∈ H⁰(Y, M^{e+m})` with
`Σ_i Ξ_{i'} = Σ_{i'} Ξ_i`. Then there is `σ ∈ H⁰(Y, M^m)` with `σ Ξ_i = Σ_i` for every `i`
(`exists_section_mul_eq`): on `{Ξ_i ≠ 0}` put `σ = Σ_i / Ξ_i` and glue.

This is the "saturation" step of the finite generation of the filtration of an ample test
configuration: a section over `𝓧 ∖ 𝓧₀` which becomes regular after multiplication by powers of
coordinate sections without common zeros is regular.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.TestCurve.FGRel

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Opposite TopologicalSpace

variable {Y : Scheme.{0}}

/-- Regular functions on an open (the ring in which atlas coefficients live). -/
abbrev Fn (U : Y.Opens) : CommRingCat := Y.sheaf.obj.obj (op U)

/-- Restriction of regular functions. -/
abbrev resF {U V : Y.Opens} (h : V ≤ U) : Fn U →+* Fn V :=
  (Y.sheaf.obj.map (homOfLE h).op).hom

theorem resF_resF {U V W : Y.Opens} (h1 : V ≤ U) (h2 : W ≤ V) (g : Fn U) :
    resF h2 (resF h1 g) = resF (h2.trans h1) g := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem isUnit_resF_of_le_basicOpen {U V : Y.Opens} (g : Fn U) (h : V ≤ Y.basicOpen g) :
    IsUnit (resF (h.trans (Y.basicOpen_le g)) g) := by
  have hu : IsUnit (resF (Y.basicOpen_le g) g) := Y.toRingedSpace.isUnit_res_basicOpen g
  have := hu.map (resF h)
  rwa [resF_resF] at this

/-- A function killed by functions whose nonvanishing loci cover its domain is zero. -/
theorem eq_zero_of_mul_eq_zero_cover {U : Y.Opens} (d : Fn U) {ι : Type} (u : ι → Fn U)
    (hcov : U ≤ ⨆ i, Y.basicOpen (u i)) (h : ∀ i, d * u i = 0) : d = 0 := by
  apply TopCat.Sheaf.eq_of_locally_eq' Y.sheaf (fun i => Y.basicOpen (u i)) U
    (fun i => homOfLE (Y.basicOpen_le _)) hcov
  intro i
  have hu := isUnit_resF_of_le_basicOpen (u i) le_rfl
  have h1 := congrArg (resF (Y.basicOpen_le (u i))) (h i)
  rw [map_mul, map_zero] at h1
  change resF (Y.basicOpen_le (u i)) d = resF (Y.basicOpen_le (u i)) 0
  rw [map_zero]
  exact (hu.mul_left_eq_zero).mp h1

/-- **Division of functions**: if `σ_i u_{i'} = σ_{i'} u_i` and the `D(u_i)` cover `U`, there is
`g` with `g u_i = σ_i` for all `i`. -/
theorem exists_mul_eq_of_cover {U : Y.Opens} {ι : Type} (u σ : ι → Fn U)
    (hcov : U ≤ ⨆ i, Y.basicOpen (u i)) (hcomp : ∀ i i', σ i * u i' = σ i' * u i) :
    ∃ g : Fn U, ∀ i, g * u i = σ i := by
  classical
  let V : ι → Y.Opens := fun i => Y.basicOpen (u i)
  have hV : ∀ i, V i ≤ U := fun i => Y.basicOpen_le _
  have hunit : ∀ i, IsUnit (resF (hV i) (u i)) := fun i => isUnit_resF_of_le_basicOpen (u i) le_rfl
  have hex : ∀ i, ∃ x : Fn (V i), x * resF (hV i) (u i) = resF (hV i) (σ i) := fun i =>
    ⟨resF (hV i) (σ i) * ↑(hunit i).unit⁻¹, by rw [mul_assoc, IsUnit.val_inv_mul, mul_one]⟩
  choose sf hsf using hex
  have hcompat : TopCat.Presheaf.IsCompatible Y.sheaf.obj V sf := by
    intro i i'
    have hW1 : V i ⊓ V i' ≤ V i := inf_le_left
    have hW2 : V i ⊓ V i' ≤ V i' := inf_le_right
    have hu1 : IsUnit (resF (hW1.trans (hV i)) (u i)) := by
      have := (hunit i).map (resF hW1)
      rwa [resF_resF] at this
    have hu2 : IsUnit (resF (hW2.trans (hV i')) (u i')) := by
      have := (hunit i').map (resF hW2)
      rwa [resF_resF] at this
    change resF hW1 (sf i) = resF hW2 (sf i')
    have e1 := congrArg (resF hW1) (hsf i)
    have e2 := congrArg (resF hW2) (hsf i')
    rw [map_mul, resF_resF, resF_resF] at e1 e2
    have hc := congrArg (resF (hW1.trans (hV i))) (hcomp i i')
    rw [map_mul, map_mul] at hc
    have hsame : ∀ g : Fn U, resF (hW1.trans (hV i)) g = resF (hW2.trans (hV i')) g :=
      fun g => rfl
    apply (hu1.mul (hu2)).mul_left_injective
    simp only [hsame] at hu1 e1 hc ⊢
    calc resF hW1 (sf i) * (resF (hW2.trans (hV i')) (u i) * resF (hW2.trans (hV i')) (u i'))
        = (resF hW1 (sf i) * resF (hW2.trans (hV i')) (u i)) *
            resF (hW2.trans (hV i')) (u i') := by ring
      _ = resF (hW2.trans (hV i')) (σ i) * resF (hW2.trans (hV i')) (u i') := by rw [e1]
      _ = resF (hW2.trans (hV i')) (σ i') * resF (hW2.trans (hV i')) (u i) := hc
      _ = (resF hW2 (sf i') * resF (hW2.trans (hV i')) (u i')) *
            resF (hW2.trans (hV i')) (u i) := by rw [e2]
      _ = resF hW2 (sf i') * (resF (hW2.trans (hV i')) (u i) *
            resF (hW2.trans (hV i')) (u i')) := by ring
  obtain ⟨g, hg, -⟩ := TopCat.Sheaf.existsUnique_gluing' Y.sheaf V U
    (fun i => homOfLE (hV i)) hcov sf hcompat
  refine ⟨g, fun i => ?_⟩
  rw [← sub_eq_zero]
  apply TopCat.Sheaf.eq_of_locally_eq' Y.sheaf V U (fun i => homOfLE (hV i)) hcov
  intro i'
  change resF (hV i') (g * u i - σ i) = resF (hV i') 0
  rw [map_zero, map_sub, map_mul]
  have hgi : resF (hV i') g = sf i' := hg i'
  rw [hgi]
  have key : (sf i' * resF (hV i') (u i) - resF (hV i') (σ i)) * resF (hV i') (u i') = 0 := by
    rw [sub_mul, mul_assoc, mul_comm (resF (hV i') (u i)), ← mul_assoc, hsf i',
      ← map_mul, ← map_mul, hcomp i' i, sub_self]
  exact (hunit i').mul_left_eq_zero.mp key

/-! ### Sections of a line bundle -/

variable {M : Y.Modules} (b : LineBundleAtlas M)

/-- Coefficient functions of the atlas on overlaps transform by powers of the transition. -/
theorem coeff_transition (n : ℕ) (c c' : b.I) (s : bundlePowerGlobalSections M n) :
    resF (inf_le_right : b.opens c ⊓ b.opens c' ≤ b.opens c') (atlasPowerGlobalCoefficients b n c' s) =
      (localBundleFrameTransition (b.frame c) (b.frame c') (homOfLE inf_le_left)
          (homOfLE inf_le_right) : Fn (b.opens c ⊓ b.opens c')) ^ n *
        resF (inf_le_left : b.opens c ⊓ b.opens c' ≤ b.opens c)
          (atlasPowerGlobalCoefficients b n c s) :=
  LocalBundleFrame.global_coefficients_transition (b.frame c) (b.frame c') _ _ n s

/-- A global section with prescribed coefficients, when these are compatible with the
transition functions. -/
theorem exists_section_of_coefficients (n : ℕ) (g : ∀ c, Fn (b.opens c))
    (hg : ∀ c c', resF (inf_le_right : b.opens c ⊓ b.opens c' ≤ b.opens c') (g c') =
      (localBundleFrameTransition (b.frame c) (b.frame c') (homOfLE inf_le_left)
          (homOfLE inf_le_right) : Fn (b.opens c ⊓ b.opens c')) ^ n *
        resF (inf_le_left : b.opens c ⊓ b.opens c' ≤ b.opens c) (g c)) :
    ∃ s : bundlePowerGlobalSections M n, ∀ c, atlasPowerGlobalCoefficients b n c s = g c := by
  let loc : ∀ c, bundleSections (bundleTensorPower M n) (b.opens c) := fun c =>
    (((b.frame c).tensorPower n).coefficients (𝟙 _)).symm (g c)
  have hloc : ∀ c {W : Y.Opens} (j : W ⟶ b.opens c),
      ((b.frame c).tensorPower n).coefficients j ((bundleTensorPower M n).val.map j.op (loc c)) =
        Y.sheaf.obj.map j.op (g c) := by
    intro c W j
    have h := ((b.frame c).tensorPower n).coefficients_restrict (𝟙 _) j (loc c)
    simpa only [Category.comp_id, loc, LinearEquiv.apply_symm_apply] using h
  have hcompat : TopCat.Presheaf.IsCompatible (bundleTensorPower M n).val.presheaf b.opens loc := by
    intro c c'
    let l : b.opens c ⊓ b.opens c' ⟶ b.opens c := homOfLE inf_le_left
    let r : b.opens c ⊓ b.opens c' ⟶ b.opens c' := homOfLE inf_le_right
    apply (((b.frame c').tensorPower n).coefficients r).injective
    calc ((b.frame c').tensorPower n).coefficients r
          ((bundleTensorPower M n).val.map l.op (loc c)) =
        (localBundleFrameTransition (b.frame c) (b.frame c') l r : Fn _) ^ n *
          ((b.frame c).tensorPower n).coefficients l
            ((bundleTensorPower M n).val.map l.op (loc c)) :=
        LocalBundleFrame.tensorPower_coefficients_transition (b.frame c) (b.frame c') l r _ _
      _ = (localBundleFrameTransition (b.frame c) (b.frame c') l r : Fn _) ^ n *
          Y.sheaf.obj.map l.op (g c) := by rw [hloc]
      _ = Y.sheaf.obj.map r.op (g c') := (hg c c').symm
      _ = ((b.frame c').tensorPower n).coefficients r
          ((bundleTensorPower M n).val.map r.op (loc c')) := (hloc c' r).symm
  have hcover : (⊤ : Y.Opens) ≤ iSup b.opens := by
    intro x _
    obtain ⟨i, hi⟩ := b.covers x
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, hi⟩
  let S : TopCat.Sheaf AddCommGrpCat Y :=
    ⟨(bundleTensorPower M n).val.presheaf, (bundleTensorPower M n).isSheaf⟩
  obtain ⟨s, hs, -⟩ := TopCat.Sheaf.existsUnique_gluing' S b.opens ⊤ (fun _ => homOfLE le_top)
    hcover loc hcompat
  refine ⟨s, fun c => ?_⟩
  change ((b.frame c).tensorPower n).coefficients (𝟙 _)
    ((bundleTensorPower M n).val.map (homOfLE le_top).op s) = g c
  have : (bundleTensorPower M n).val.map (homOfLE le_top).op s = loc c := hs c
  rw [this]
  exact LinearEquiv.apply_symm_apply _ _

/-- **Division of sections by a family without common zeros.** -/
theorem exists_section_mul_eq (m e : ℕ) {ι : Type} (Ξ : ι → bundlePowerGlobalSections M e)
    (Sg : ι → bundlePowerGlobalSections M (e + m))
    (hcov : ∀ c, b.opens c ≤ ⨆ i, Y.basicOpen (atlasPowerGlobalCoefficients b e c (Ξ i)))
    (hcomp : ∀ c i i', atlasPowerGlobalCoefficients b (e + m) c (Sg i) *
        atlasPowerGlobalCoefficients b e c (Ξ i') =
      atlasPowerGlobalCoefficients b (e + m) c (Sg i') * atlasPowerGlobalCoefficients b e c (Ξ i)) :
    ∃ σ : bundlePowerGlobalSections M m, ∀ c i,
      atlasPowerGlobalCoefficients b m c σ * atlasPowerGlobalCoefficients b e c (Ξ i) =
        atlasPowerGlobalCoefficients b (e + m) c (Sg i) := by
  choose g hg using fun c => exists_mul_eq_of_cover
    (fun i => atlasPowerGlobalCoefficients b e c (Ξ i))
    (fun i => atlasPowerGlobalCoefficients b (e + m) c (Sg i)) (hcov c) (hcomp c)
  obtain ⟨σ, hσ⟩ := exists_section_of_coefficients b m g (fun c c' => by
    rw [← sub_eq_zero]
    let W := b.opens c ⊓ b.opens c'
    let tr : Fn W := (localBundleFrameTransition (b.frame c) (b.frame c') (homOfLE inf_le_left)
      (homOfLE inf_le_right) : Fn W)
    apply eq_zero_of_mul_eq_zero_cover _
      (fun i => resF (inf_le_right : W ≤ b.opens c') (atlasPowerGlobalCoefficients b e c' (Ξ i)))
    · intro x hx
      have hx' : x ∈ b.opens c' := (inf_le_right : W ≤ b.opens c') hx
      obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp (hcov c' hx')
      refine TopologicalSpace.Opens.mem_iSup.mpr ⟨i, ?_⟩
      change x ∈ Y.basicOpen ((Y.presheaf.map (homOfLE _).op) _)
      rw [Scheme.basicOpen_res]
      exact ⟨hx, hi⟩
    · intro i
      have h1 := congrArg (resF (inf_le_right : W ≤ b.opens c')) (hg c' i)
      have h2 := congrArg (resF (inf_le_left : W ≤ b.opens c)) (hg c i)
      rw [map_mul] at h1 h2
      have t1 := coeff_transition b e c c' (Ξ i)
      have t2 := coeff_transition b (e + m) c c' (Sg i)
      rw [sub_mul, h1, t2, t1, ← h2, pow_add]
      ring)
  exact ⟨σ, fun c i => by rw [hσ c]; exact hg c i⟩

end SGPT.TestCurve.FGRel
