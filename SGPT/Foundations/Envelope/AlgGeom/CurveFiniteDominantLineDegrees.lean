import SGPT.Foundations.Envelope.AlgGeom.CurveFiniteCartierDegree
import SGPT.Foundations.Envelope.AlgGeom.CartierAdmissibleModulePullback

/-! # TRUE full Euler degree of EVERY original line under finite dominant curves, including singular targets -/
open AlgebraicGeometry CategoryTheory
open Scheme.Modules
noncomputable section
universe u
namespace SGPT.Foundations.Envelope.CurveFiniteDominantLineDegrees
open CurveLineDegrees CurveCartierLocalOrders
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Actual dominance and integrality give the TRUE original canonical Cartier
module pullback isomorphism, without flatness or a comap comparison certificate. -/
def cartierPullbackComapIso {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (g : Y ⟶ X) [IsDominant g] (I : X.IdealSheafData) (hI : I.IsInvertible) :
    (Scheme.Modules.pullback g).obj I.toModules ≅ (I.comap g).toModules := by
  let : IsIso (I.toModulesComapPullbackMap g) :=
    hI.toModulesComapPullbackMap_isIso_of_isInvertible_comap g (hI.comap_of_dominant_integral g)
  exact asIso (I.toModulesComapPullbackMap g)

/-- The SAME original whole ratio line pulls back to the ratio of its SAME
actual geometric comap ideals, with actual canonical tensor/dual comparisons. -/
def ratioPullbackComapIso {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (g : Y ⟶ X) [IsDominant g] (I J : X.IdealSheafData)
    (hI : I.IsInvertible) (hJ : J.IsInvertible) :
    (Scheme.Modules.pullback g).obj (I.ratioModule J) ≅ (I.comap g).ratioModule (J.comap g) :=
  I.ratioPullbackIso J hJ g ≪≫
    tensorObjCongr (cartierPullbackComapIso g I hI) (dualIsoObj (cartierPullbackComapIso g J hJ).symm)

/-- TRUE full Euler degree of the SAME original Cartier ratio line scales
under ANY actual finite dominant integral curve map, with no target normality or flatness. -/
theorem degree_pullback_ratio {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    {k : Type u} [Field k] (g : Y ⟶ X) [IsFinite g] [IsDominant g]
    (q : X ⟶ Spec (.of k)) (hq : IsProjectiveFactorization q)
    (hdimX : topologicalKrullDim X ≤ 1) (hdimY : topologicalKrullDim Y ≤ 1)
    (I J : X.IdealSheafData) (hI : I.IsInvertible) (hJ : J.IsInvertible) :
    letI : IsProper q := hq.isProper
    letI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace q
    letI : IsProper (g ≫ q) := (CurveFiniteMapDegrees.finite_comp_projectiveFactorization q hq g).isProper
    letI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (g ≫ q)
    letI := (DominantFunctionFieldMaps.functionFieldMap g).hom.toAlgebra
    degree (g ≫ q) ((Scheme.Modules.pullback g).obj (I.ratioModule J)) =
      (Module.finrank X.functionField Y.functionField : ℤ) * degree q (I.ratioModule J) := by
  let : IsProper q := hq.isProper
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace q
  let hqY := CurveFiniteMapDegrees.finite_comp_projectiveFactorization q hq g
  let : IsProper (g ≫ q) := hqY.isProper
  let : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (g ≫ q)
  let := (DominantFunctionFieldMaps.functionFieldMap g).hom.toAlgebra
  rw [degree_eq_of_iso _ (ratioPullbackComapIso g I J hI hJ)]
  change SchemeCoherentEulerCharacteristic.normalizedEulerCharacteristic _ _ =
    _ * SchemeCoherentEulerCharacteristic.normalizedEulerCharacteristic _ _
  rw [normalizedEulerCharacteristic_ratio_eq_finsum_difference (g ≫ q) hqY hdimY
      (I.comap g) (J.comap g) (hI.comap_of_dominant_integral g) (hJ.comap_of_dominant_integral g),
    normalizedEulerCharacteristic_ratio_eq_finsum_difference q hq hdimX I J hI hJ,
    CurveFiniteCartierDegree.finsum_comap g q hq hdimX hdimY J hJ,
    CurveFiniteCartierDegree.finsum_comap g q hq hdimX hdimY I hI, mul_sub]

/-- EVERY SAME original invertible line has its TRUE normalized full coherent
Euler degree multiplied by the degree of the SAME native original function-field
map under ANY actual finite dominant integral curve morphism.
The original target may be singular; no flatness or comparison premise is assumed. -/
theorem degree_pullback {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    {k : Type u} [Field k] (g : Y ⟶ X) [IsFinite g] [IsDominant g]
    (q : X ⟶ Spec (.of k)) (hq : IsProjectiveFactorization q)
    (hdimX : topologicalKrullDim X ≤ 1) (hdimY : topologicalKrullDim Y ≤ 1)
    (L : X.Modules) (hL : IsInvertible L) :
    letI : IsProper q := hq.isProper
    letI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace q
    letI : IsProper (g ≫ q) := (CurveFiniteMapDegrees.finite_comp_projectiveFactorization q hq g).isProper
    letI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (g ≫ q)
    letI := (DominantFunctionFieldMaps.functionFieldMap g).hom.toAlgebra
    degree (g ≫ q) ((Scheme.Modules.pullback g).obj L) =
      (Module.finrank X.functionField Y.functionField : ℤ) * degree q L := by
  let : IsProper q := hq.isProper
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace q
  let hqY := CurveFiniteMapDegrees.finite_comp_projectiveFactorization q hq g
  let : IsProper (g ≫ q) := hqY.isProper
  let : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (g ≫ q)
  let := (DominantFunctionFieldMaps.functionFieldMap g).hom.toAlgebra
  obtain ⟨I, J, hI, hJ, ⟨e⟩⟩ := ProjectiveLineCartierRatio.exists_cartier_ratio q hq L hL
  rw [degree_eq_of_iso _ ((Scheme.Modules.pullback g).mapIso e), degree_eq_of_iso q e]
  exact degree_pullback_ratio g q hq hdimX hdimY I J hI hJ

end SGPT.Foundations.Envelope.CurveFiniteDominantLineDegrees
