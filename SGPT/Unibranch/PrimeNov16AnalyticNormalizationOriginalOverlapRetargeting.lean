import SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalProperRestriction
import SGPT.Unibranch.HironakaG10ChowStrictTransformCalculus

/-! Actual overlap retargeting and a manufactured whole dense good inverse.
Blueprint: prime-nov16-analytic-normalization-original-overlap-retargeting.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology
namespace SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalOverlapRetargeting
open PrimeNov16AnalyticNormalizationOriginalProperRestriction
open HironakaG10ChowStrictTransformCalculus SourceReducedComplexSpace

theorem exists_actual_overlap_retargeting {N B₁ B₂ X : SourceReducedComplexSpace}
    (p : N ⟶ B₁) (hp : IsProperMap p.hom.left.base) (G : Set B₁.obj.left)
    (hGood : IsIsoOver p G) (hDense : Dense (p.hom.left.base ⁻¹' G))
    (J : B₁ ⟶ X) (K : B₂ ⟶ X)
    [LocallyRingedSpace.IsOpenImmersion J.hom.left]
    [LocallyRingedSpace.IsOpenImmersion K.hom.left]
    (U : Opens B₁.obj.left) [ParacompactSpace U]
    (hland : ∀ b : B₁.obj.left,b ∈ U → J.hom.left.base b ∈ range K.hom.left.base) :
    ∃ f : restrictedSource p hp U ⟶ B₂,
      f ≫ K = sourceInclusion p hp U ≫ p ≫ J ∧
      ∃ Gf : Set B₂.obj.left,IsIsoOver f Gf ∧ Dense (f.hom.left.base ⁻¹' Gf) := by
  let S := restrictedSource p hp U
  let i : S ⟶ N := sourceInclusion p hp U
  have hr : range (i ≫ p ≫ J).hom.left.base ⊆ range K.hom.left.base := by
    rintro _ ⟨s,rfl⟩
    exact hland _ s.property
  let L := LocallyRingedSpace.IsOpenImmersion.lift K.hom.left (i ≫ p ≫ J).hom.left hr
  have hLK : L ≫ K.hom.left = (i ≫ p ≫ J).hom.left :=
    LocallyRingedSpace.IsOpenImmersion.lift_fac _ _ hr
  have hscalar : L ≫ B₂.obj.hom = S.obj.hom := by
    rw [← Over.w K.hom,← Category.assoc,hLK]
    exact Over.w (i ≫ p ≫ J).hom
  let f : S ⟶ B₂ := ObjectProperty.homMk (Over.homMk L hscalar)
  have hf : f ≫ K = i ≫ p ≫ J := by
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    exact hLK
  have hpoint (s : S.obj.left) :
      K.hom.left.base (f.hom.left.base s) = J.hom.left.base (p.hom.left.base (i.hom.left.base s)) :=
    congrArg (fun t : S ⟶ X => t.hom.left.base s) hf
  obtain ⟨V,j,hj,hjr,hjp,hjpr⟩ := hGood
  let : LocallyRingedSpace.IsOpenImmersion j := hj
  let : LocallyRingedSpace.IsOpenImmersion (j ≫ p.hom.left) := hjp
  let O : Opens V := ⟨(j ≫ p.hom.left).base ⁻¹' (U : Set B₁.obj.left),
    U.isOpen.preimage (j ≫ p.hom.left).base.hom.continuous⟩
  let V' := V.restrict O.isOpenEmbedding
  let j₀ : V' ⟶ V := V.ofRestrict O.isOpenEmbedding
  let b : V' ⟶ N.obj.left := j₀ ≫ j
  let : LocallyRingedSpace.IsOpenImmersion j₀ := by dsimp only [j₀];infer_instance
  let : LocallyRingedSpace.IsOpenImmersion b := by dsimp only [b];infer_instance
  have hbRange : range b.base ⊆ range i.hom.left.base := by
    rintro _ ⟨v,rfl⟩
    exact ⟨⟨b.base v,v.property⟩,rfl⟩
  let a := LocallyRingedSpace.IsOpenImmersion.lift i.hom.left b hbRange
  have hai : a ≫ i.hom.left = b := LocallyRingedSpace.IsOpenImmersion.lift_fac _ _ hbRange
  let : LocallyRingedSpace.IsOpenImmersion (a ≫ i.hom.left) := hai.symm ▸ (inferInstance : LocallyRingedSpace.IsOpenImmersion b)
  have ha : LocallyRingedSpace.IsOpenImmersion a := isOpenImmersion_of_comp a i.hom.left
  let : LocallyRingedSpace.IsOpenImmersion a := ha
  have haPoint (v : V') : i.hom.left.base (a.base v) = j.base v.val :=
    congrArg (fun t : V' ⟶ N.obj.left => t.base v) hai
  have hafK : (a ≫ f.hom.left) ≫ K.hom.left = j₀ ≫ (j ≫ p.hom.left) ≫ J.hom.left := by
    change (a ≫ L) ≫ K.hom.left = _
    rw [Category.assoc,hLK]
    change a ≫ (i.hom.left ≫ p.hom.left ≫ J.hom.left) = _
    simpa only [b,Category.assoc] using
      congrArg (fun q : V' ⟶ N.obj.left => q ≫ p.hom.left ≫ J.hom.left) hai
  let : LocallyRingedSpace.IsOpenImmersion ((a ≫ f.hom.left) ≫ K.hom.left) := by
    rw [hafK]
    infer_instance
  have haf : LocallyRingedSpace.IsOpenImmersion (a ≫ f.hom.left) :=
    isOpenImmersion_of_comp (a ≫ f.hom.left) K.hom.left
  have hRange : range a.base = i.hom.left.base ⁻¹' (p.hom.left.base ⁻¹' G) := by
    ext s
    constructor
    · rintro ⟨v,rfl⟩
      change p.hom.left.base (i.hom.left.base (a.base v)) ∈ G
      rw [haPoint]
      rw [← hjpr]
      exact ⟨v.val,rfl⟩
    · intro hs
      have his : i.hom.left.base s ∈ range j.base := by rw [hjr];exact hs
      obtain ⟨v,hv⟩ := his
      have hvO : v ∈ O := by
        change p.hom.left.base (j.base v) ∈ U
        rw [hv]
        exact s.property
      refine ⟨⟨v,hvO⟩,?_⟩
      apply (show LocallyRingedSpace.IsOpenImmersion i.hom.left from inferInstance).base_open.injective
      exact (haPoint ⟨v,hvO⟩).trans hv
  let Gf : Set B₂.obj.left := range (a ≫ f.hom.left).base
  have hpre : f.hom.left.base ⁻¹' Gf = range a.base := by
    ext s
    constructor
    · rintro ⟨v,hv⟩
      have hpEq : p.hom.left.base (i.hom.left.base s) = p.hom.left.base (j.base v.val) := by
        apply (show LocallyRingedSpace.IsOpenImmersion J.hom.left from inferInstance).base_open.injective
        calc
          J.hom.left.base (p.hom.left.base (i.hom.left.base s)) = K.hom.left.base (f.hom.left.base s) := (hpoint s).symm
          _ = K.hom.left.base (f.hom.left.base (a.base v)) := congrArg K.hom.left.base hv.symm
          _ = J.hom.left.base (p.hom.left.base (i.hom.left.base (a.base v))) := hpoint (a.base v)
          _ = J.hom.left.base (p.hom.left.base (j.base v.val)) := congrArg (fun z => J.hom.left.base (p.hom.left.base z)) (haPoint v)
      rw [hRange]
      change p.hom.left.base (i.hom.left.base s) ∈ G
      rw [hpEq,← hjpr]
      exact ⟨v.val,rfl⟩
    · rintro ⟨v,rfl⟩
      exact ⟨v,rfl⟩
  have hD : Dense (range a.base) := by
    rw [hRange]
    exact hDense.preimage (show LocallyRingedSpace.IsOpenImmersion i.hom.left from inferInstance).base_open.isOpenMap
  exact ⟨f,hf,Gf,⟨V',a,ha,hpre.symm,haf,rfl⟩,hpre.symm ▸ hD⟩
end SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalOverlapRetargeting
