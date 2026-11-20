import SGPT.Checks.Comparison.BJAsmVarphian
import SGPT.Foundations.Envelope.AlgGeom.SeshadriAmplenessCriterionNefAmple
import SGPT.Foundations.Envelope.AlgGeom.AmpleTensorLines
import SGPT.Support.ModularCurves.EllipticCurve.PoleSheaf
import SGPT.Foundations.Envelope.AlgGeom.NativeNumericalNefCone
import SGPT.Foundations.Envelope.AlgGeom.CurveLineSectionPositivity
import SGPT.Foundations.Envelope.AlgGeom.NativeNumericalAmpleConeGeneration
import SGPT.Foundations.Schemes.ProjectiveSectionExtension
import SGPT.Foundations.Analysis.Pending.KahlerDomination
import Mathlib.Topology.Sheaves.LocallySurjective

/-!
# An ample line bundle with a Kähler-curvature metric (input of the surjectivity in `thm:DXZ`)

Source: `chapter_NApotential.tex`, `thm:DXZ`, proof of surjectivity: *Let `H` be an ample line
bundle … Fix a Kähler form `ω ∈ c₁(H)`.* The approximation theorem `thm:BJappseq`
(`SGPT.NAPotential.BJ.bjAppSeq_holds`) takes an ample line bundle in `SGPT.Foundations.Envelope`'s sense
(`SchemeLineAmpleness.IsAmple`: a positive tensor power is the pull-back of `𝒪(1)` along a closed
embedding), while the workspace's Kähler forms of algebraic origin come from the Fubini–Study
metric on `𝒪_X(1) = E.map^* 𝒪(1)` (`SGPT.NAPotential.FSPos.hyperplaneBundle`, a different model of
`𝒪(1)`). We connect the two without comparing the two models of `𝒪(1)`:

* `coordGeneratingSections`: the coordinate sections `x_0, …, x_N` generate `𝒪_X(1)`
  (in the atlas frame `x_i` the coefficient of `x_i` is `1`);
* `lineClass_hyperplaneBundle_mem_nefCone`: hence `𝒪_X(1)` is nef (global generation);
* `isAmple_ampleTwist`: for every ample `S` (in `SGPT.Foundations.Envelope`'s sense) and every `a`,
  `H = 𝒪_X(1)^{⊗ a} ⊗ S` is ample (Kleiman: nef plus ample is ample);
* `curvature_ampleTwistMetric`: with any smooth metric `h_S` on `S`, the product metric
  `h_FS^{⊗ a} ⊗ h_S` has curvature `a ω_FS + c₁(S, h_S)`;
* **`exists_isAmple_isKahler`**: there is an ample `H` with a smooth metric whose curvature is a
  Kähler form (take `a` large: Kähler domination of `c₁(S, h_S)` by `ω_FS`).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

noncomputable section

namespace SGPT.NAPotential.BJ.DXZSurj

open Set
open AlgebraicGeometry CategoryTheory SGPT.Foundations.Schemes SGPT.Okounkov
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.NAPotential.FSPos SGPT.NAPotential.BJ.NativePicard
open SGPT.Foundations.Envelope

attribute [local instance] Scheme.Modules.monoidalCategory Scheme.Modules.symmetricCategory

/-! ### Epimorphisms from local lifts -/

/-- A morphism of sheaves of modules on a scheme is an epimorphism as soon as every section of the
target lifts locally. -/
theorem epi_of_local_lifts {Y : Scheme.{0}} {M N : Y.Modules} (α : M ⟶ N)
    (h : ∀ (V : Y.Opens) (t : Γ(N, V)) (x : Y), x ∈ V →
      ∃ (W : Y.Opens) (hWV : W ≤ V), x ∈ W ∧
        ∃ s : Γ(M, W), α.val.app (.op W) s = N.val.map (homOfLE hWV).op t) : Epi α := by
  let F := SheafOfModules.toSheaf Y.ringCatSheaf
  have hl : TopCat.Presheaf.IsLocallySurjective (F.map α).hom := by
    apply (TopCat.Presheaf.isLocallySurjective_iff _).mpr
    intro V t x hx
    obtain ⟨W, hWV, hxW, s, hs⟩ := h V t x hx
    exact ⟨W, hWV, ⟨s, hs⟩, hxW⟩
  let : CategoryTheory.Sheaf.IsLocallySurjective (F.map α) := hl
  have he : Epi (F.map α) := inferInstance
  exact F.epi_of_epi_map he

/-! ### The coordinate sections generate `𝒪_X(1)` -/

section Generation

variable {X : Scheme.{0}} {f : X ⟶ Spec (.of ℂ)} (E : ClosedProjectiveEmbedding f)

/-- The coordinate sections `x_k` of `𝒪_X(1)`, as global sections of the sheaf of modules. -/
def coordSections : Fin (E.ambientDimension + 1) → (hyperplaneBundle E).sections :=
  fun k => (hyperplaneBundle E).unitHomEquiv (coordHom E k)

/-- `x_k|_U = (x_k|_V)|_U`, read through the generator `ιFree k`. -/
theorem ιFree_comp_coordSections (k : Fin (E.ambientDimension + 1)) :
    SheafOfModules.ιFree k ≫ (hyperplaneBundle E).freeHomEquiv.symm (coordSections E) =
      coordHom E k := by
  rw [← SheafOfModules.unitHomEquiv_symm_freeHomEquiv_apply, Equiv.apply_symm_apply]
  exact Equiv.symm_apply_apply _ _

/-- In the atlas frame `x_j` on `U_j`, the coefficient of `x_j` restricted to `W ⊆ U_j` is `1`. -/
theorem coefficients_coordSection_self (j : Fin (E.ambientDimension + 1)) {W : X.Opens}
    (h : W ⟶ coordOpen E j) :
    ((hyperplaneAtlas E).frame j).coefficients h (coordSection E j W) = 1 := by
  rw [coordCoef_restrict, coordCoef_atlas, ratio_self, map_one]

/-- **The coordinate sections generate `𝒪_X(1)`**: the evaluation `𝒪_X^{N+1} → 𝒪_X(1)` is an
epimorphism, since on `U_j` every section is a multiple of `x_j`. -/
theorem coordSections_epi :
    Epi ((hyperplaneBundle E).freeHomEquiv.symm (coordSections E)) := by
  apply epi_of_local_lifts
  intro V t x hx
  obtain ⟨j, hj⟩ := (hyperplaneAtlas E).covers x
  let W : X.Opens := V ⊓ coordOpen E j
  let hWU : W ⟶ coordOpen E j := homOfLE inf_le_right
  let e := ((hyperplaneAtlas E).frame j).coefficients hWU
  let tW : bundleSections (hyperplaneBundle E) W :=
    (hyperplaneBundle E).val.map (homOfLE (inf_le_left : W ≤ V)).op t
  let c := e tW
  refine ⟨W, inf_le_left, ⟨hx, hj⟩, (SheafOfModules.ιFree j).val.app (.op W) c, ?_⟩
  have h1 : ((hyperplaneBundle E).freeHomEquiv.symm (coordSections E)).val.app (.op W)
      ((SheafOfModules.ιFree j).val.app (.op W) c) = (coordHom E j).val.app (.op W) c := by
    rw [← ιFree_comp_coordSections E j]
    rfl
  have h2 : (coordHom E j).val.app (.op W) c = c • coordSection E j W := by
    have hc : c = c • (1 : X.sheaf.obj.obj (.op W)) := ((smul_eq_mul c 1).trans (mul_one c)).symm
    conv_lhs => rw [hc]
    exact map_smul ((coordHom E j).val.app (.op W)).hom c (1 : X.sheaf.obj.obj (.op W))
  rw [h1, h2]
  apply e.injective
  change e (c • coordSection E j W) = e tW
  rw [map_smul, coefficients_coordSection_self E j hWU, smul_eq_mul, mul_one]

/-- The coordinate sections, as generating sections of `𝒪_X(1)`. -/
def coordGeneratingSections : (hyperplaneBundle E).GeneratingSections where
  I := Fin (E.ambientDimension + 1)
  s := coordSections E
  epi := coordSections_epi E

/-- `𝒪_X(1)` is invertible. -/
theorem hyperplaneBundle_isInvertible : Scheme.Modules.IsInvertible (hyperplaneBundle E) :=
  isInvertible_of_atlas (hyperplaneAtlas E)

/-- **`𝒪_X(1)` is nef**: a globally generated invertible sheaf has nonnegative degree on every
closed integral curve. -/
theorem lineClass_hyperplaneBundle_mem_nefCone [IsProjective f] :
    NativeRealNumericalClasses.lineClass f (hyperplaneBundle E) (hyperplaneBundle_isInvertible E) ∈
      NativeRealNumericalClasses.nefCone f := by
  apply (NativeRealNumericalClasses.lineClass_mem_nefCone_iff f _ _).mpr
  intro C
  let : IsIntegral C.carrier := C.integral
  exact_mod_cast CurveLineSectionPositivity.degree_pullback_nonneg_of_generatingSections
    (C.structureMorphism f) (C.projectiveFactorization f) (le_of_eq C.dimension) C.inclusion
    (hyperplaneBundle E) (hyperplaneBundle_isInvertible E) (coordGeneratingSections E)

end Generation

/-! ### Ample twists of `𝒪_X(1)` -/

section Twist

variable {X : Scheme.{0}} {f : X ⟶ Spec (.of ℂ)} (E : ClosedProjectiveEmbedding f)

/-- The tensor powers of `SGPT.Foundations.Envelope` and of `SGPT.Foundations.Schemes` are the same sheaves. -/
theorem canonicalPower_eq (L : X.Modules) (n : ℕ) :
    CanonicalGeometry.bundleTensorPower L n = SGPT.Foundations.Schemes.bundleTensorPower L n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change CanonicalGeometry.bundleTensor (CanonicalGeometry.bundleTensorPower L n) L =
      SGPT.Foundations.Schemes.bundleTensor (SGPT.Foundations.Schemes.bundleTensorPower L n) L
    rw [ih]
    rfl

/-- The line bundle `H = 𝒪_X(1)^{⊗ a} ⊗ S`. -/
abbrev ampleTwist (S : X.Modules) (a : ℕ) : X.Modules :=
  bundleTensor (bundleTensorPower (hyperplaneBundle E) a) S

/-- **`𝒪_X(1)^{⊗ a} ⊗ S` is ample for every ample `S`** (nef plus ample is ample). -/
theorem isAmple_ampleTwist [IsProjective f] {S : X.Modules}
    (hS : SchemeLineAmpleness.IsAmple f S) (a : ℕ) :
    SchemeLineAmpleness.IsAmple f (ampleTwist E S a) := by
  have h := SeshadriAmplenessCriterionNefAmple.isAmple_tensorPower_tensor f (hyperplaneBundle E) S
    (hyperplaneBundle_isInvertible E) (lineClass_hyperplaneBundle_mem_nefCone E) hS a
  rw [canonicalPower_eq] at h
  exact AmpleTensorLines.ample_of_iso h (SGPT.Support.ModularCurves.monoidalTensorObjIso _ _)

/-- The atlas of `𝒪_X(1)^{⊗ a} ⊗ S` by tensor frames. -/
def ampleTwistAtlas {S : X.Modules} (bS : LineBundleAtlas S) (a : ℕ) :
    LineBundleAtlas (ampleTwist E S a) :=
  pairwiseTensorAtlas ((hyperplaneAtlas E).tensorPower a) bS

end Twist

section Metric

variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (n : ℕ) [SmoothOfRelativeDimension n f]
  (E : ClosedProjectiveEmbedding f)

local instance dxzSurjAmplePointTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance dxzSurjAmplePointCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f n

variable [IsSeparated f] [QuasiCompact f]

local instance dxzSurjAmplePointManifold : IsComplexManifold n (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f n

/-- The product metric `h_FS^{⊗ a} ⊗ h_S` on `𝒪_X(1)^{⊗ a} ⊗ S`. -/
def ampleTwistMetric {S : X.Modules} (bS : LineBundleAtlas S) (HS : SchemeLineBundleMetric f n E S)
    (a : ℕ) : SchemeLineBundleMetric f n E (ampleTwist E S a) :=
  ((fubiniStudyMetric f E n).tensorPower (hyperplaneAtlas E) a).tensorProduct HS
    ((hyperplaneAtlas E).tensorPower a) bS

/-- `c₁(𝒪_X(1)^{⊗ a} ⊗ S, h_FS^{⊗ a} ⊗ h_S) = c₁(S, h_S) + a ω_FS` on every chart target, for every
atlas. -/
theorem curvature_ampleTwistMetric {S : X.Modules} (bS : LineBundleAtlas S)
    (HS : SchemeLineBundleMetric f n E S) (a : ℕ) (b : LineBundleAtlas (ampleTwist E S a)) :
    ((ampleTwistMetric f n E bS HS a).curvature b).val.GeometricallyEq
      (HS.curvature bS + (a : ℝ) • (Assembly.fsBackground f n E).form).val := by
  intro e u hu
  have h1 := ((fubiniStudyMetric f E n).tensorPower (hyperplaneAtlas E) a).curvature_tensorProduct
    HS ((hyperplaneAtlas E).tensorPower a) bS b e hu
  have h2 := (fubiniStudyMetric f E n).curvature_tensorPower (hyperplaneAtlas E) a e hu
  change ((((fubiniStudyMetric f E n).tensorPower (hyperplaneAtlas E) a).tensorProduct HS
    ((hyperplaneAtlas E).tensorPower a) bS).curvature b).val.coeff e u =
    (HS.curvature bS + (a : ℝ) • (fubiniStudyMetric f E n).curvature (hyperplaneAtlas E)).val.coeff
      e u
  rw [h1, ClosedRealOneOneForm.coeff_add, h2, ClosedRealOneOneForm.coeff_add, add_comm]

variable [CompactSpace (SchemeComplexPoint f)]

/-- **An ample line bundle with a Kähler-curvature metric** (`thm:DXZ`: *Let `H` be an ample line
bundle … Fix a Kähler form `ω ∈ c₁(H)`*): there is an invertible sheaf `H`, ample in
`SGPT.Foundations.Envelope`'s sense (the hypothesis of `thm:BJappseq`), with an atlas and a smooth Hermitian
metric whose Chern form is a Kähler form on `X(ℂ)`. Explicitly `H = 𝒪_X(1)^{⊗ a} ⊗ S` for any ample
`S` and `a ≫ 0`. -/
theorem exists_isAmple_isKahler [IsProjective f] :
    ∃ H : X.Modules, SchemeLineAmpleness.IsAmple f H ∧ ∃ (bH : LineBundleAtlas H)
      (HH : SchemeLineBundleMetric f n E H), (HH.curvature bH).val.IsKahler := by
  obtain ⟨S, hS⟩ := NativeRealNumericalClasses.exists_geometric_ample_line f
  let bS : LineBundleAtlas S := atlasOfInvertible hS.isInvertible
  let HS : SchemeLineBundleMetric f n E S := schemeLineBundleMetric f n E bS
  let ω := Assembly.fsBackground f n E
  obtain ⟨A, -, hA⟩ := Pending.KahlerDomination.exists_pos_isSemipositive_add_smul ω
    (HS.curvature bS)
  have hA' : (HS.curvature bS + ((⌈A⌉₊ : ℕ) : ℝ) • ω.form).val.IsSemipositive :=
    Pending.KahlerDomination.isSemipositive_add_smul_mono ω.isSemipositive (Nat.le_ceil A) hA
  have hK := Pending.KahlerDomination.isKahler_add_smul_succ ω hA'
  refine ⟨ampleTwist E S (⌈A⌉₊ + 1), isAmple_ampleTwist E hS _, ampleTwistAtlas E bS _,
    ampleTwistMetric f n E bS HS _, ?_⟩
  refine ((curvature_ampleTwistMetric f n E bS HS (⌈A⌉₊ + 1) _).isKahler_iff).mpr ?_
  simpa only [Nat.cast_add, Nat.cast_one] using hK

end Metric

end SGPT.NAPotential.BJ.DXZSurj
