import SGPT.Okounkov.OF12NormalProjectiveResolution
import SGPT.Unibranch.UnibAnBirationalOpen
import SGPT.Unibranch.UnibAnSmoothIso
import SGPT.Unibranch.OriginalBimeromorphicSourceIso
import SGPT.Unibranch.OriginalSmoothSourceAnalytic
import SGPT.GAGA.OkoCloseDXMain
import SGPT.Foundations.Schemes.NativeFanoAlgebraicFiniteness
import SGPT.Foundations.Analysis.Pending.PshAnalyticSetExtension

/-! A projective algebraic model and its actual good open give an OF12 resolution.
The exceptional set is the literal analytified complement of that good open. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace SGPT.Okounkov.OF12

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Set TopologicalSpace
open SGPT.Unibranch SGPT.Unibranch.SourceReducedComplexSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending

private theorem schemeComplexPointMap_bijective_of_isIso
    {A B : Scheme.{0}} (g : B ⟶ Spec (.of ℂ)) (q : A ⟶ B) [IsIso q] :
    Function.Bijective (schemeComplexPointMap (q ≫ g) g q rfl) := by
  constructor
  · intro a b h
    apply Subtype.ext
    exact (cancel_mono q).mp (congrArg Subtype.val h)
  · intro b
    refine ⟨⟨b.val ≫ inv q, ?_⟩, ?_⟩
    · simp only [Category.assoc, IsIso.inv_hom_id_assoc, b.property]
    · apply Subtype.ext
      change (b.val ≫ inv q) ≫ q = b.val
      simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]

variable {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
  {f : X ⟶ Spec (.of ℂ)} [IsSeparated f] [QuasiCompact f] [LocallyOfFiniteType f]
  {m : ℕ} (ρ : Y ⟶ X) [SmoothOfRelativeDimension (m + 1) (ρ ≫ f)]

/-- The analytic projection used by OF12 is the analytification of the actual algebraic projection,
read through the canonical comparison on its smooth source. -/
theorem nonempty_resolution_of_projective_model_and_isIso_restrict
    (EY : ClosedProjectiveEmbedding (ρ ≫ f))
    (U : X.Opens) [Nonempty U] [IsIso (ρ ∣_ U)]
    (hZ : (UnibAn.analytification f).IsAnalyticSubset
      ((schemeComplexPointImage f ∘ UnibAn.pointMap f) ⁻¹' (U : Set X)ᶜ))
    (hthin : interior ((schemeComplexPointImage f ∘ UnibAn.pointMap f) ⁻¹' (U : Set X)ᶜ) = ∅) :
    Nonempty (Resolution f m) := by
  let g := ρ ≫ f
  let := EY.isSeparated
  let := EY.quasiCompact
  let := EY.locallyOfFiniteType
  let : TopologicalSpace (SchemeComplexPoint g) := schemeAnalyticPointTopology g
  let := schemeAnalyticTNChartedSpace g (m + 1)
  let := schemeAnalyticTN_isComplexManifold g (m + 1)
  obtain ⟨I, hI⟩ := UnibAn.exists_smoothModel_analytification_iso g (m + 1)
  let F : UnibAn.analytification g ⟶ UnibAn.analytification f :=
    UnibAn.analytificationMorphism ρ rfl
  let π : smoothModel g (m + 1) ⟶ UnibAn.analytification f := I.hom ≫ F
  have hπ (y : SchemeComplexPoint g) :
      UnibAn.pointMap f (π.hom.left.base ⟨y, mem_univ y⟩) =
        schemeComplexPointMap g f ρ rfl y := by
    change UnibAn.pointMap f (F.hom.left.base (I.hom.hom.left.base ⟨y, mem_univ y⟩)) = _
    exact (UnibAn.pointMap_analytificationMorphism ρ rfl _).trans
      (congrArg (schemeComplexPointMap g f ρ rfl) (hI y))
  let Z := (schemeComplexPointImage f ∘ UnibAn.pointMap f) ⁻¹' (U : Set X)ᶜ
  have hiso : IsIsoOver π Zᶜ := by
    change IsIsoOver (I.hom ≫ F) (((schemeComplexPointImage f ∘ UnibAn.pointMap f) ⁻¹'
      (U : Set X)ᶜ)ᶜ)
    rw [preimage_compl, compl_compl]
    exact (UnibAn.analytificationMorphism_isIsoOver_of_isIso_restrict f ρ U).precomp_iso I
  have hbij := schemeComplexPointMap_bijective_of_isIso (U.ι ≫ f) (ρ ∣_ U)
  let W := ρ ⁻¹ᵁ U
  let : Nonempty W := Nonempty.map (fun u : U.toScheme => (ρ ∣_ U).surjective u |>.choose) inferInstance
  let : IsIntegral W.toScheme := isIntegral_of_isOpenImmersion W.ι
  let : LocallyOfFiniteType (W.ι ≫ g) := inferInstance
  obtain ⟨y₀⟩ := integralFiniteTypeSchemeComplexPoint_nonempty (W.ι ≫ g)
  let y := schemeComplexPointMap (W.ι ≫ g) g W.ι rfl y₀
  have hy :
      schemeComplexPointImage f (schemeComplexPointMap g f ρ rfl y) ∈ (U : Set X) := by
    change ρ (W.ι (y₀.val default)) ∈ (U : Set X)
    exact (y₀.val default).property
  let : Nonempty (SchemeComplexPoint g) := ⟨y⟩
  let : ConnectedSpace (SchemeComplexPoint g) :=
    SGPT.GAGA.OkoClose.connectedSpace_of_isIntegral g EY (m + 1)
  let A := OriginalSmoothSourceAnalytic.pointMap π ⁻¹' Z
  have hA : IsComplexAnalyticSubset (n := m + 1) A :=
    OriginalSmoothSourceAnalytic.isComplexAnalyticSubset_preimage π hZ
  have hAproper : A ≠ univ := by
    intro h
    have hyA : y ∈ A := h.symm ▸ mem_univ y
    change schemeComplexPointImage f (UnibAn.pointMap f (π.hom.left.base ⟨y, mem_univ y⟩)) ∉
      (U : Set X) at hyA
    exact hyA (by rw [hπ]; exact hy)
  have hAthin :=
    PshAnalyticSetExtension.IsComplexAnalyticSubset.interior_eq_empty_of_ne_univ hA hAproper
  have hpre : interior (π.hom.left.base ⁻¹' Z) = ∅ := by
    change interior ((Homeomorph.Set.univ (SchemeComplexPoint g)) ⁻¹' A) = ∅
    rw [← (Homeomorph.Set.univ (SchemeComplexPoint g)).preimage_interior, hAthin, preimage_empty]
  exact ⟨Resolution.ofProjectiveModel ρ EY U hbij π hπ Z hZ hthin hpre hiso⟩

end SGPT.Okounkov.OF12
