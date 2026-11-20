import SGPT.NAPotential.GAGAMult2Faithful
import SGPT.Projective.BDivOriginalIdealStalk

/-! Blueprint first: BDivNov16OriginalAnalytificationStalkImage.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Projective.BDivNov16
open AlgebraicGeometry CategoryTheory SGPT.Foundations.Schemes SGPT.Okounkov
open SGPT.NAPotential.Berkovich SGPT.NAPotential.GAGAMult
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open scoped Topology Manifold
variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (n : ℕ)
  [SmoothOfRelativeDimension n f] [IsSeparated f] [QuasiCompact f]
local instance stalkImageTopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance stalkImageCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f n
local instance stalkImageManifold : IsComplexManifold n (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f n

theorem originalAnalytification_mem_iff_native_stalkImage
    (EX : ClosedProjectiveEmbedding f) (D : X.IdealSheafData) (p : SchemeComplexPoint f)
    (g : SchemeComplexPoint f → ℂ) (hg : HolomorphicAt n g p) :
    (analytificationIdeal f n EX D).mem p g ↔
      NativeHolGerm.mk g hg ∈ (D.stalkIdeal (schemeComplexPointImage f p)).map (schemeNativeStalkGerm f n p) := by
  constructor
  · exact mk_mem_map_stalkIdeal_of_mem_analytificationIdeal f n EX D p hg
  · intro hmem
    obtain ⟨V,hV,hpV,_hVtop⟩ := exists_isAffineOpen_mem_and_subset (X := X)
      (U := ⊤) (x := schemeComplexPointImage f p) trivial
    let U : X.affineOpens := ⟨V,hV⟩
    let S := fun s : SchemeComplexPoint f → ℂ => ∃ (W : X.affineOpens)
      (_ : schemeComplexPointImage f p ∈ (W : X.Opens)) (r : Γ(X,W)),
      r ∈ D.ideal W ∧ s = schemeOpenRegularFunction f n EX W r
    let J := spanGerms (n := n) S p
    have hle : (D.stalkIdeal (schemeComplexPointImage f p)).map (schemeNativeStalkGerm f n p) ≤ J := by
      rw [D.stalkIdeal_eq_affine (schemeComplexPointImage f p) U hpV,Ideal.map_map]
      apply Ideal.map_le_iff_le_comap.mpr
      intro r hr
      change schemeNativeStalkGerm f n p
        (X.presheaf.germ U.1 (schemeComplexPointImage f p) hpV r) ∈ J
      rw [← schemeOpenRegularFunction_germ f n EX U r p hpV]
      exact mk_mem_spanGerms (schemeOpenRegularFunction_holomorphicAt f n EX U r p hpV)
        ⟨U,hpV,r,hr,rfl⟩
    change IsInSpanAt (n := n) S p g
    exact isInSpanAt_of_mk_mem_spanGerms hg (hle hmem)
end SGPT.Projective.BDivNov16
