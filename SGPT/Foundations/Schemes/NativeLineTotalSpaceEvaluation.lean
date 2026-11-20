import SGPT.Foundations.Schemes.NativeLineTotalSpace
import SGPT.Foundations.Schemes.ConeSectionRingGeometry

/-!
# Evaluation from the native dual-line total space to the actual cone

The actual homogeneous section evaluations extend to the literal direct-sum
section ring. The native Γ–Spec adjunction and scheme colimit descend these
maps to the actual section-ring cone.
-/

open CategoryTheory Limits Opposite AlgebraicGeometry
open scoped DirectSum

namespace SGPT.Foundations.Schemes

universe u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X : Scheme.{u}}

@[simp]
theorem nativeFramedSectionCoefficient_zero {L : X.Modules} (a : LineBundleAtlas L)
    (n : ℕ) (c : NativeFramedOpen a) : nativeFramedSectionCoefficient a n 0 c = 0 := by
  simp [nativeFramedSectionCoefficient, atlasPowerGlobalCoefficients_zero]

@[simp]
theorem nativeFramedSectionCoefficient_add {L : X.Modules} (a : LineBundleAtlas L)
    (n : ℕ) (s t : bundlePowerGlobalSections L n) (c : NativeFramedOpen a) :
    nativeFramedSectionCoefficient a n (s + t) c =
      nativeFramedSectionCoefficient a n s c + nativeFramedSectionCoefficient a n t c := by
  simp [nativeFramedSectionCoefficient, atlasPowerGlobalCoefficients_add]

/-- Actual sheaf-glued homogeneous products have the literal product of the
actual framed-open coefficient functions. -/
theorem nativeFramedSectionCoefficient_mul {L : X.Modules} (a : LineBundleAtlas L)
    (m n : ℕ) (s : bundlePowerGlobalSections L m) (t : bundlePowerGlobalSections L n)
    (c : NativeFramedOpen a) :
    nativeFramedSectionCoefficient a (m + n) (atlasPowerGlobalMul a m n s t) c =
      nativeFramedSectionCoefficient a m s c * nativeFramedSectionCoefficient a n t c := by
  simp [nativeFramedSectionCoefficient, atlasPowerGlobalMul_coefficients]

@[simp]
theorem nativeFramedSectionCoefficient_one {L : X.Modules} (a : LineBundleAtlas L)
    (c : NativeFramedOpen a) :
    nativeFramedSectionCoefficient a 0 (bundlePowerGlobalOne L) c = 1 := by
  simp [nativeFramedSectionCoefficient, atlasPowerGlobalCoefficients_one]

/-- Homogeneous evaluation is a literal additive map on the actual section
module, including the zero tensor-power degree. -/
def nativeFramedHomogeneousMap {L : X.Modules} (a : LineBundleAtlas L)
    (n : ℕ) (c : NativeFramedOpen a) :
    bundlePowerGlobalSections L n →+ Γ(nativeAffineLine c.2.1.toScheme, ⊤) where
  toFun s := nativeFramedHomogeneousFunction a n s c
  map_zero' := by simp [nativeFramedHomogeneousFunction]
  map_add' s t := by simp [nativeFramedHomogeneousFunction, add_mul]

/-- Evaluation multiplies genuine homogeneous sections by their constructed
sheaf product and the ordinary sum of their degrees. -/
theorem nativeFramedHomogeneousFunction_mul {L : X.Modules} (a : LineBundleAtlas L)
    (m n : ℕ) (s : bundlePowerGlobalSections L m) (t : bundlePowerGlobalSections L n)
    (c : NativeFramedOpen a) :
    nativeFramedHomogeneousFunction a (m + n) (atlasPowerGlobalMul a m n s t) c =
      nativeFramedHomogeneousFunction a m s c * nativeFramedHomogeneousFunction a n t c := by
  simp only [nativeFramedHomogeneousFunction, nativeFramedSectionCoefficient_mul,
    map_mul, pow_add]
  ring

@[simp]
theorem nativeFramedHomogeneousFunction_one {L : X.Modules} (a : LineBundleAtlas L)
    (c : NativeFramedOpen a) :
    nativeFramedHomogeneousFunction a 0 (bundlePowerGlobalOne L) c = 1 := by
  simp [nativeFramedHomogeneousFunction]

/-- The actual homogeneous evaluations extend to an actual ring map from the
literal section ring by the direct-sum universal property. -/
def IntrinsicLineBundle.nativeChartEvaluation (L : IntrinsicLineBundle X)
    (c : NativeFramedOpen L.atlas) :
    L.sectionRing →+* Γ(nativeAffineLine c.2.1.toScheme, ⊤) := by
  let := atlasPowerGradedCommRing L.atlas
  exact DirectSum.toSemiring (fun n ↦ nativeFramedHomogeneousMap L.atlas n c)
    (nativeFramedHomogeneousFunction_one L.atlas c)
    (fun {m n} s t ↦ nativeFramedHomogeneousFunction_mul L.atlas m n s t c)

/-- An actual homogeneous summand evaluates as the actual coefficient
multiplied by the actual fiber-coordinate power. -/
theorem IntrinsicLineBundle.nativeChartEvaluation_ofSection (L : IntrinsicLineBundle X)
    (c : NativeFramedOpen L.atlas) (n : ℕ) (s : bundlePowerGlobalSections L.sheaf n) :
    L.nativeChartEvaluation c (L.ofSection n s) =
      nativeFramedHomogeneousFunction L.atlas n s c := by
  let := atlasPowerGradedCommRing L.atlas
  change DirectSum.toAddMonoid (fun m ↦ nativeFramedHomogeneousMap L.atlas m c)
    (DirectSum.of (bundlePowerGlobalSections L.sheaf) n s) = _
  exact DirectSum.toAddMonoid_of _ n s

/-- The actual whole-section-ring evaluations agree along every genuine
inverse-transition chart map. -/
theorem IntrinsicLineBundle.nativeChartEvaluation_naturality (L : IntrinsicLineBundle X)
    {c d : NativeFramedOpen L.atlas} (h : c ⟶ d) :
    (nativeFramedMap L.atlas h).appTop.hom.comp (L.nativeChartEvaluation d) =
      L.nativeChartEvaluation c := by
  ext x
  change (nativeFramedMap L.atlas h).appTop (L.nativeChartEvaluation d x) =
    L.nativeChartEvaluation c x
  induction x using DirectSum.induction_on with
  | zero => simp
  | of n s =>
      change (nativeFramedMap L.atlas h).appTop
        (L.nativeChartEvaluation d (L.ofSection n s)) =
          L.nativeChartEvaluation c (L.ofSection n s)
      rw [L.nativeChartEvaluation_ofSection, L.nativeChartEvaluation_ofSection]
      exact nativeFramedHomogeneousFunction_compatible L.atlas n s h
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The native Γ–Spec adjunction gives an actual chart morphism into the
actual section-ring cone, without any geometry theorem premise. -/
def IntrinsicLineBundle.nativeChartConeMap (L : IntrinsicLineBundle X)
    (c : NativeFramedOpen L.atlas) :
    nativeAffineLine c.2.1.toScheme ⟶ L.sectionRingCone :=
  (nativeAffineLine c.2.1.toScheme).toSpecΓ ≫
    Spec.map (CommRingCat.ofHom (L.nativeChartEvaluation c))

@[reassoc]
theorem IntrinsicLineBundle.nativeChartConeMap_naturality (L : IntrinsicLineBundle X)
    {c d : NativeFramedOpen L.atlas} (h : c ⟶ d) :
    nativeFramedMap L.atlas h ≫ L.nativeChartConeMap d = L.nativeChartConeMap c := by
  have he : CommRingCat.ofHom (L.nativeChartEvaluation d) ≫
      (nativeFramedMap L.atlas h).appTop =
      CommRingCat.ofHom (L.nativeChartEvaluation c) := by
    ext x
    exact DFunLike.congr_fun (L.nativeChartEvaluation_naturality h) x
  unfold nativeChartConeMap
  rw [Scheme.toSpecΓ_naturality_assoc, ← Spec.map_comp, he]

/-- The actual cone chart morphisms form a genuine cocone on the native
dual-line gluing diagram. -/
def IntrinsicLineBundle.nativeConeMapCocone (L : IntrinsicLineBundle X) :
    Cocone (nativeDualLineDiagram L.atlas) where
  pt := L.sectionRingCone
  ι :=
    { app := fun c ↦ L.nativeChartConeMap c
      naturality := fun c d h ↦ by
        change nativeFramedMap L.atlas h ≫ L.nativeChartConeMap d =
          L.nativeChartConeMap c ≫ 𝟙 L.sectionRingCone
        rw [Category.comp_id]
        exact L.nativeChartConeMap_naturality h }

/-- The actual cone evaluation morphism is descended by the native scheme
colimit from the actual sheaf-section evaluations on every chart. -/
def IntrinsicLineBundle.nativeConeMap (L : IntrinsicLineBundle X) :
    nativeDualLineTotalSpace L.atlas ⟶ L.sectionRingCone :=
  colimit.desc (nativeDualLineDiagram L.atlas) L.nativeConeMapCocone

@[reassoc (attr := simp)]
theorem IntrinsicLineBundle.nativeConeMap_on_open (L : IntrinsicLineBundle X)
    (c : NativeFramedOpen L.atlas) :
    colimit.ι (nativeDualLineDiagram L.atlas) c ≫ L.nativeConeMap =
      L.nativeChartConeMap c :=
  colimit.ι_desc _ _

@[reassoc (attr := simp)]
theorem IntrinsicLineBundle.nativeConeMap_on_chart (L : IntrinsicLineBundle X) (i : L.atlas.I) :
    nativeDualLineChart L.atlas i ≫ L.nativeConeMap =
      L.nativeChartConeMap ⟨i, ⟨L.atlas.opens i, le_rfl⟩⟩ :=
  L.nativeConeMap_on_open _

/-- Pullback of the actual affine-cone regular functions is exactly the
constructed chart evaluation, by the native adjunction inverse identity. -/
theorem IntrinsicLineBundle.nativeChartConeMap_appTop (L : IntrinsicLineBundle X)
    (c : NativeFramedOpen L.atlas) :
    (Scheme.ΓSpecIso (.of L.sectionRing)).inv ≫ (L.nativeChartConeMap c).appTop =
      CommRingCat.ofHom (L.nativeChartEvaluation c) :=
  ΓSpecIso_inv_ΓSpec_adjunction_homEquiv _

/-- The literal section-ring evaluation into actual global regular functions
on the actual total-space scheme. -/
def IntrinsicLineBundle.nativeTotalEvaluation (L : IntrinsicLineBundle X) :
    L.sectionRing →+* Γ(nativeDualLineTotalSpace L.atlas, ⊤) :=
  L.nativeConeMap.appTop.hom.comp (Scheme.ΓSpecIso (.of L.sectionRing)).inv.hom

/-- Its actual chart restrictions are precisely the previously constructed
local ring evaluations. -/
theorem IntrinsicLineBundle.nativeTotalEvaluation_on_open (L : IntrinsicLineBundle X)
    (c : NativeFramedOpen L.atlas) :
    (colimit.ι (nativeDualLineDiagram L.atlas) c).appTop.hom.comp L.nativeTotalEvaluation =
      L.nativeChartEvaluation c := by
  ext r
  change (colimit.ι (nativeDualLineDiagram L.atlas) c ≫ L.nativeConeMap).appTop
    ((Scheme.ΓSpecIso (.of L.sectionRing)).inv r) = L.nativeChartEvaluation c r
  rw [L.nativeConeMap_on_open]
  exact congrArg (fun q ↦ q r) (L.nativeChartConeMap_appTop c)

/-- Every actual homogeneous section restricts to its literal polynomial
evaluation on every genuine framed open. -/
theorem IntrinsicLineBundle.nativeTotalEvaluation_ofSection_on_open
    (L : IntrinsicLineBundle X) (c : NativeFramedOpen L.atlas) (n : ℕ)
    (s : bundlePowerGlobalSections L.sheaf n) :
    (colimit.ι (nativeDualLineDiagram L.atlas) c).appTop
      (L.nativeTotalEvaluation (L.ofSection n s)) =
      nativeFramedHomogeneousFunction L.atlas n s c :=
  (DFunLike.congr_fun (L.nativeTotalEvaluation_on_open c) (L.ofSection n s)).trans
    (L.nativeChartEvaluation_ofSection c n s)

/-- The descended cone map is exactly the native Γ–Spec morphism of the
literal global section-ring evaluation. -/
theorem IntrinsicLineBundle.nativeConeMap_eq_evaluation (L : IntrinsicLineBundle X) :
    (nativeDualLineTotalSpace L.atlas).toSpecΓ ≫
      Spec.map (CommRingCat.ofHom L.nativeTotalEvaluation) = L.nativeConeMap := by
  change (nativeDualLineTotalSpace L.atlas).toSpecΓ ≫
    Spec.map ((Scheme.ΓSpecIso (.of L.sectionRing)).inv ≫ L.nativeConeMap.appTop) = _
  rw [Spec.map_comp, ← Scheme.toSpecΓ_naturality_assoc]
  change L.nativeConeMap ≫ (Spec (.of L.sectionRing)).toSpecΓ ≫
    Spec.map (Scheme.ΓSpecIso (.of L.sectionRing)).inv = _
  rw [toSpecΓ_SpecMap_ΓSpecIso_inv]
  change L.nativeConeMap ≫ 𝟙 L.sectionRingCone = L.nativeConeMap
  exact Category.comp_id _

/-- The actual degree-zero framed coefficient is the literal restriction of
the actual base regular function. -/
theorem nativeFramedSectionCoefficient_degree_zero {L : X.Modules} (a : LineBundleAtlas L)
    (r : Γ(X, ⊤)) (c : NativeFramedOpen a) :
    nativeFramedSectionCoefficient a 0 r c = c.2.1.ι.appTop r := by
  simp only [nativeFramedSectionCoefficient, atlasPowerGlobalCoefficients_degree_zero]
  change c.2.1.topIso.inv
    (X.presheaf.map (homOfLE c.2.2).op (X.presheaf.map (homOfLE le_top).op r)) = _
  simp only [Scheme.Opens.topIso_inv, Scheme.Opens.ι_appTop,
    ← CommRingCat.comp_apply, ← Functor.map_comp]
  congr 2

/-- The actual local zero-section evaluation is precisely the literal
degree-zero augmentation followed by actual base restriction. -/
theorem IntrinsicLineBundle.nativeChartEvaluation_zero (L : IntrinsicLineBundle X)
    (c : NativeFramedOpen L.atlas) :
    (nativeAffineLineZero c.2.1.toScheme).appTop.hom.comp (L.nativeChartEvaluation c) =
      c.2.1.ι.appTop.hom.comp L.sectionRingAugmentation := by
  ext x
  change (nativeAffineLineZero c.2.1.toScheme).appTop (L.nativeChartEvaluation c x) =
    c.2.1.ι.appTop (L.sectionRingAugmentation x)
  induction x using DirectSum.induction_on with
  | zero => simp
  | of n s =>
      change (nativeAffineLineZero c.2.1.toScheme).appTop
        (L.nativeChartEvaluation c (L.ofSection n s)) =
          c.2.1.ι.appTop (L.sectionRingAugmentation (L.ofSection n s))
      rw [L.nativeChartEvaluation_ofSection]
      simp only [nativeFramedHomogeneousFunction, map_mul, map_pow,
        nativeAffineLineZero_coordinate]
      have hp : (nativeAffineLineZero c.2.1.toScheme).appTop
          ((nativeAffineLineProjection c.2.1.toScheme).appTop
            (nativeFramedSectionCoefficient L.atlas n s c)) =
          nativeFramedSectionCoefficient L.atlas n s c := by
        rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop,
          nativeAffineLineZero_projection, Scheme.Hom.id_appTop]
        rfl
      rw [hp]
      by_cases hn : n = 0
      · subst n
        simp only [pow_zero, mul_one, nativeFramedSectionCoefficient_degree_zero]
        change c.2.1.ι.appTop s = c.2.1.ι.appTop
          ((DirectSum.of (bundlePowerGlobalSections L.sheaf) 0 s) 0)
        rw [DirectSum.of_eq_same]
      · rw [zero_pow hn, mul_zero]
        change 0 = c.2.1.ι.appTop
          ((DirectSum.of (bundlePowerGlobalSections L.sheaf) n s) 0)
        rw [DirectSum.of_eq_of_ne n 0 s (Ne.symm hn), map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The native Γ–Spec construction recovers every literal morphism to an
actual affine spectrum from its literal map on actual global sections. -/
theorem nativeSchemeMap_eq_globalMap {T : Scheme.{u}} {R : CommRingCat.{u}}
    (q : T ⟶ Spec R) :
    T.toSpecΓ ≫ Spec.map ((Scheme.ΓSpecIso R).inv ≫ q.appTop) = q := by
  rw [Spec.map_comp, ← Scheme.toSpecΓ_naturality_assoc,
    toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]

/-- The zero-section chart composite factors through the literal actual
degree-zero augmentation, on every framed smaller open. -/
theorem IntrinsicLineBundle.nativeChartZeroConeMap (L : IntrinsicLineBundle X)
    (c : NativeFramedOpen L.atlas) :
    nativeAffineLineZero c.2.1.toScheme ≫ L.nativeChartConeMap c =
      c.2.1.ι ≫ X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom L.sectionRingAugmentation) := by
  have he : CommRingCat.ofHom (L.nativeChartEvaluation c) ≫
      (nativeAffineLineZero c.2.1.toScheme).appTop =
      CommRingCat.ofHom L.sectionRingAugmentation ≫ c.2.1.ι.appTop := by
    ext r
    exact DFunLike.congr_fun (L.nativeChartEvaluation_zero c) r
  unfold nativeChartConeMap
  rw [Scheme.toSpecΓ_naturality_assoc, Scheme.toSpecΓ_naturality_assoc,
    ← Spec.map_comp, ← Spec.map_comp, he]

/-- The actual global zero section maps to the actual augmentation spectrum.
This identity uses no properness, integrality, or contraction hypothesis. -/
@[reassoc]
theorem IntrinsicLineBundle.nativeZeroConeMap_factor (L : IntrinsicLineBundle X) :
    nativeDualLineZero L.atlas ≫ L.nativeConeMap =
      X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom L.sectionRingAugmentation) := by
  apply (nativeLineAtlasBaseCover L.atlas).hom_ext
  intro i
  change (L.atlas.opens i).ι ≫ nativeDualLineZero L.atlas ≫ L.nativeConeMap =
    (L.atlas.opens i).ι ≫ X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom L.sectionRingAugmentation)
  rw [nativeDualLineZero_on_chart_assoc, L.nativeConeMap_on_chart]
  exact L.nativeChartZeroConeMap ⟨i, ⟨L.atlas.opens i, le_rfl⟩⟩

/-- Restricting the actual global section-ring evaluation to the actual zero
section recovers exactly the literal augmentation ring map. -/
theorem IntrinsicLineBundle.nativeZeroEvaluation (L : IntrinsicLineBundle X) :
    (nativeDualLineZero L.atlas).appTop.hom.comp L.nativeTotalEvaluation =
      L.sectionRingAugmentation := by
  ext r
  change (nativeDualLineZero L.atlas ≫ L.nativeConeMap).appTop
    ((Scheme.ΓSpecIso (.of L.sectionRing)).inv r) = L.sectionRingAugmentation r
  rw [L.nativeZeroConeMap_factor]
  exact congrArg (fun q ↦ q r)
    (ΓSpecIso_inv_ΓSpec_adjunction_homEquiv (CommRingCat.ofHom L.sectionRingAugmentation))

/-- Every literal strictly positive homogeneous section vanishes on the
actual zero section of the actual dual-line total space. -/
theorem IntrinsicLineBundle.nativeZeroEvaluation_positive (L : IntrinsicLineBundle X)
    {n : ℕ} (hn : 0 < n) (s : bundlePowerGlobalSections L.sheaf n) :
    (nativeDualLineZero L.atlas).appTop (L.nativeTotalEvaluation (L.ofSection n s)) = 0 := by
  rw [show (nativeDualLineZero L.atlas).appTop (L.nativeTotalEvaluation (L.ofSection n s)) =
      L.sectionRingAugmentation (L.ofSection n s) from
    DFunLike.congr_fun L.nativeZeroEvaluation (L.ofSection n s)]
  change (DirectSum.of (bundlePowerGlobalSections L.sheaf) n s) 0 = 0
  exact DirectSum.of_eq_of_ne n 0 s (by omega)

section Vertex

variable {K : Type u} [Field K] [IsAlgClosed K] [IsIntegral X]

/-- Actual proper integral base geometry identifies the actual zero-section
augmentation image with the genuinely constructed rational cone vertex. -/
@[reassoc]
theorem IntrinsicLineBundle.nativeZeroConeMap_vertex (L : IntrinsicLineBundle X)
    (f : X ⟶ Spec (.of K)) [UniversallyClosed f] :
    nativeDualLineZero L.atlas ≫ L.nativeConeMap = f ≫ L.coneVertexMorphism f := by
  rw [L.nativeZeroConeMap_factor]
  have he : CommRingCat.ofHom L.sectionRingAugmentation =
      CommRingCat.ofHom (L.coneResidueMap f) ≫ CommRingCat.ofHom (schemeConstantMap f) := by
    ext r
    change L.sectionRingAugmentation r =
      (schemeConstantsRingEquiv f) ((schemeConstantsRingEquiv f).symm
        (L.sectionRingAugmentation r))
    exact ((schemeConstantsRingEquiv f).apply_symm_apply _).symm
  rw [he, Spec.map_comp]
  change X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (schemeConstantMap f)) ≫
    L.coneVertexMorphism f = f ≫ L.coneVertexMorphism f
  have hf : X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (schemeConstantMap f)) = f :=
    nativeSchemeMap_eq_globalMap f
  rw [← Category.assoc, hf]

/-- Every point of the actual zero section maps to the actual irrelevant
prime of the actual section-ring cone. -/
theorem IntrinsicLineBundle.nativeZeroConeMap_vertex_apply (L : IntrinsicLineBundle X)
    (f : X ⟶ Spec (.of K)) [UniversallyClosed f] (x : X) :
    L.nativeConeMap (nativeDualLineZero L.atlas x) = L.coneVertex := by
  change (nativeDualLineZero L.atlas ≫ L.nativeConeMap) x = L.coneVertex
  rw [L.nativeZeroConeMap_vertex f]
  exact L.coneVertexMorphism_apply f (f x)

end Vertex

end

end SGPT.Foundations.Schemes
