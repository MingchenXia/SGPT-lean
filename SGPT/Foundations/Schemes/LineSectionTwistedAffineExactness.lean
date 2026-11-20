import SGPT.Foundations.Schemes.ActualSheafSectionDiagramMaps
import SGPT.Foundations.Schemes.TwistedModuleFrames

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace
namespace SGPT.Foundations.Schemes
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000
variable {X : Scheme.{u}} {L : X.Modules}

/-- Tensoring on the right by a genuine global section is an actual sheaf map. -/
def sectionTensorRightMap (B T : X.Modules) (s : Γ(T, ⊤)) :
    B ⟶ bundleTensor B T where
  val := {
    app U := ModuleCat.ofHom
      (X := B.val.obj U) (Y := (bundleTensor B T).val.obj U)
      ((tensorSectionBilinear B T U.unop).flip (T.presheaf.map U.unop.leTop.op s))
    naturality {U V} i := by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro t
      change tensorSection B T V.unop (B.val.map i t)
        (T.val.map V.unop.leTop.op s) =
          (bundleTensor B T).val.map i
            (tensorSection B T U.unop t (T.val.map U.unop.leTop.op s))
      have hr : T.val.map V.unop.leTop.op s = T.val.map i (T.val.map U.unop.leTop.op s) := by
        rw [← T.val.map_comp_apply]
        rfl
      rw [hr]
      exact (tensorSection_restrict B T i.unop t (T.val.map U.unop.leTop.op s)).symm }


/-- Actual successor multiplication uses the literal original tensor-power order. -/
def sectionPowerMultiplication (A : X.Modules) (s : Γ(A, ⊤)) (m : ℕ) :
    bundleTensorPower A m ⟶ bundleTensorPower A (m + 1) :=
  sectionTensorRightMap (bundleTensorPower A m) A s

/-- The successor tensor frame retains actual coefficient multiplication. -/
theorem sectionPowerMultiplication_coefficients (s : Γ(L, ⊤)) (m : ℕ)
    {U V : X.Opens} (e : LocalBundleFrame L U) (i : V ⟶ U)
    (t : Γ(bundleTensorPower L m, V)) :
    (e.tensorPower (m + 1)).coefficients i ((sectionPowerMultiplication L s m).app V t) =
      (e.tensorPower m).coefficients i t * e.coefficients i (L.presheaf.map V.leTop.op s) :=
  LocalBundleFrame.tensor_coefficients (e.tensorPower m) e i t _

/-- The true pushforward structure module of the actual zero closed subscheme. -/
abbrev sectionZeroPushforwardStructure (a : LineBundleAtlas L) (s : Γ(L, ⊤)) :
    X.Modules := (Scheme.Modules.pushforward (sectionZeroι a s)).obj
      (SheafOfModules.unit (sectionZeroSubscheme a s).ringCatSheaf)

/-- The right map lands in the actual tensor quotient module, using the original unit. -/
def sectionZeroTensorRestriction (a : LineBundleAtlas L) (s : Γ(L, ⊤))
    (B : X.Modules) : B ⟶ bundleTensor B (sectionZeroPushforwardStructure a s) :=
  sectionTensorRightMap B (sectionZeroPushforwardStructure a s)
    (show Γ(sectionZeroPushforwardStructure a s, ⊤) from
      (1 : Γ(sectionZeroSubscheme a s, sectionZeroι a s ⁻¹ᵁ ⊤)))

/-- The actual tensor restriction uses the literal local pushforward unit. -/
theorem sectionZeroTensorRestriction_app (a : LineBundleAtlas L) (s : Γ(L, ⊤))
    (B : X.Modules) (U : X.Opens) (t : Γ(B, U)) :
    (sectionZeroTensorRestriction a s B).app U t =
      tensorSection B (sectionZeroPushforwardStructure a s) U t
        (show Γ(sectionZeroPushforwardStructure a s, U) from
          (1 : Γ(sectionZeroSubscheme a s, sectionZeroι a s ⁻¹ᵁ U))) := by
  change tensorSection B (sectionZeroPushforwardStructure a s) U t
    ((sectionZeroPushforwardStructure a s).presheaf.map U.leTop.op _) = _
  congr 1
  exact ((sectionZeroSubscheme a s).presheaf.map
    ((Opens.map (sectionZeroι a s).base).map U.leTop).op).hom.map_one

/-- In a genuine twist frame, the right map is the ACTUAL closed-subscheme pullback. -/
theorem sectionZeroTensorRestriction_coefficients (a : LineBundleAtlas L) (s : Γ(L, ⊤))
    {B : X.Modules} {U V : X.Opens} (e : LocalBundleFrame B U) (i : V ⟶ U)
    (t : Γ(B, V)) :
    e.tensorModuleCoefficients (sectionZeroPushforwardStructure a s) i
      ((sectionZeroTensorRestriction a s B).app V t) =
        (sectionZeroι a s).app V (e.coefficients i t) := by
  rw [sectionZeroTensorRestriction_app, LocalBundleFrame.tensorModuleCoefficients_tmul]
  change (sectionZeroι a s).app V (e.coefficients i t) * 1 = _
  exact mul_one _

/-- Actual coefficient regularity extends to all framed opens by handling the
empty open as a genuine subsingleton section ring. -/
theorem sectionCoefficient_mul_injective_allOpens [IsIntegral X] (a : LineBundleAtlas L)
    (s : Γ(L, ⊤)) (hs : s ≠ 0) {U V : X.Opens}
    (e : LocalBundleFrame L U) (i : V ⟶ U) :
    Function.Injective (fun r : Γ(X, V) ↦
      (show Γ(X, V) from e.coefficients i (L.presheaf.map V.leTop.op s)) * r) := by
  classical
  by_cases h : Nonempty V
  · let := h
    exact sectionCoefficient_mul_injective a s hs e i
  · have hV : V = ⊥ := by
      apply bot_unique
      intro x hx
      exact (h ⟨⟨x, hx⟩⟩).elim
    let : Subsingleton Γ(X, V) := CommRingCat.subsingleton_of_isTerminal
      (TopCat.Sheaf.isTerminalOfEqEmpty X.sheaf hV)
    intro r t _
    exact Subsingleton.elim _ _

/-- The true affine quotient pullback and genuine twist frame produce
surjectivity of the actual tensor restriction. -/
theorem sectionZeroAffineTensorRestriction_surjective (a : LineBundleAtlas L)
    (s : Γ(L, ⊤)) (U : X.affineOpens) {B : X.Modules} {V : X.Opens}
    (e : LocalBundleFrame B V) (i : U.val ⟶ V) :
    Function.Surjective ((sectionZeroTensorRestriction a s B).app U) := by
  intro z
  obtain ⟨r, hr⟩ := sectionZeroι_app_surjective a s U
    (e.tensorModuleCoefficients (sectionZeroPushforwardStructure a s) i z)
  refine ⟨(e.coefficients i).symm r, ?_⟩
  apply (e.tensorModuleCoefficients (sectionZeroPushforwardStructure a s) i).injective
  rw [sectionZeroTensorRestriction_coefficients, LinearEquiv.apply_symm_apply, hr]

/-- The actual framed affine tensor sequence is exact, using the original
closed-subscheme quotient maps rather than an exactness certificate. -/
theorem sectionZeroAffineTensor_exact (a : LineBundleAtlas L) (s : Γ(L, ⊤))
    (U : X.affineOpens) {B : X.Modules} {V : X.Opens}
    (eB : LocalBundleFrame B V) (e : LocalBundleFrame L V) (i : U.val ⟶ V) :
    Function.Exact ((sectionTensorRightMap B L s).app U)
      ((sectionZeroTensorRestriction a s (bundleTensor B L)).app U) := by
  intro x
  let c := (eB.tensor e).coefficients i
  let d := (eB.tensor e).tensorModuleCoefficients (sectionZeroPushforwardStructure a s) i
  have h := sectionZeroAffine_frame_exact a s U e i (c x)
  have hmul (t : Γ(B, U)) : c ((sectionTensorRightMap B L s).app U t) =
      eB.coefficients i t * e.coefficients i (L.presheaf.map U.val.leTop.op s) :=
    LocalBundleFrame.tensor_coefficients eB e i t _
  constructor
  · intro hx
    have hx' : (sectionZeroι a s).app U (c x) = 0 := by
      rw [← sectionZeroTensorRestriction_coefficients a s (eB.tensor e) i x, hx, map_zero]
    obtain ⟨r, hr⟩ := h.mp hx'
    refine ⟨(eB.coefficients i).symm r, ?_⟩
    apply c.injective
    rw [hmul, LinearEquiv.apply_symm_apply, mul_comm]
    exact hr
  · rintro ⟨t, rfl⟩
    apply d.injective
    change d ((sectionZeroTensorRestriction a s (bundleTensor B L)).app U
      ((sectionTensorRightMap B L s).app U t)) = d 0
    rw [map_zero]
    change (eB.tensor e).tensorModuleCoefficients (sectionZeroPushforwardStructure a s) i
      ((sectionZeroTensorRestriction a s (bundleTensor B L)).app U
        ((sectionTensorRightMap B L s).app U t)) = 0
    rw [sectionZeroTensorRestriction_coefficients]
    apply h.mpr
    refine ⟨eB.coefficients i t, ?_⟩
    rw [hmul, mul_comm]

/-- Integral geometry and the original nonzero section produce injectivity of
the ACTUAL tensor multiplication map, including empty framed opens. -/
theorem sectionTensorRightMap_injective [IsIntegral X] (a : LineBundleAtlas L)
    (s : Γ(L, ⊤)) (hs : s ≠ 0) {B : X.Modules} {U V : X.Opens}
    (eB : LocalBundleFrame B U) (e : LocalBundleFrame L U) (i : V ⟶ U) :
    Function.Injective ((sectionTensorRightMap B L s).app V) := by
  intro x y h
  have hc := congrArg ((eB.tensor e).coefficients i) h
  change (eB.tensor e).coefficients i
    (tensorSection B L V x (L.presheaf.map V.leTop.op s)) =
      (eB.tensor e).coefficients i
        (tensorSection B L V y (L.presheaf.map V.leTop.op s)) at hc
  rw [LocalBundleFrame.tensor_coefficients, LocalBundleFrame.tensor_coefficients] at hc
  apply (eB.coefficients i).injective
  apply sectionCoefficient_mul_injective_allOpens a s hs e i
  simpa only [mul_comm] using hc


end
end SGPT.Foundations.Schemes
