import SGPT.Unibranch.PrimeNov16AnalyticNormalizationGraphProper
import SGPT.Foundations.Analysis.Pending.HironakaActualAnalyticSubspaceOpenRestriction

/-! Actual full original LRS inverse on H≠0, from literal coordinates and actual
whole-carrier equations. No inverse/IsoOver/open-immersion certificate supplied.
Blueprint: prime-nov16-analytic-normalization-good-iso.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.HironakaActualAnalyticSubspace
open SGPT.Foundations.Analysis.Pending.HironakaActualAnalyticSubspaceMaps
open SGPT.Foundations.Analysis.Pending.HironakaActualAnalyticSubspacePresentationIndependence
open SGPT.Foundations.Analysis.Pending.HironakaActualAnalyticSubspaceOpenRestriction
namespace SGPT.Unibranch.PrimeNov16AnalyticNormalizationGoodIso
open PrimeNov16AnalyticNormalizationDenominatorGraph
open PrimeNov16AnalyticNormalizationGraphFinite

private theorem basePoint_smooth {n k : ℕ} (U : Opens (ComplexModel n)) :
    ContMDiff 𝓘(ℂ,ComplexModel (n+k)) 𝓘(ℂ,ComplexModel n) ∞ (basePoint (k := k) U) := by
  apply (ContMDiff.subtypeVal_comp_iff U _).mp
  exact (baseProjection n k).contMDiff.comp contMDiff_subtype_val

def goodBase {n : ℕ} (U : Opens (ComplexModel n)) (H : ComplexModel n → ℂ)
    (hH : DifferentiableOn ℂ H U) : Opens U :=
  ⟨{x | H x.val ≠ 0},by
    have hc : Continuous (fun x : U => H x.val) :=
      hH.continuousOn.comp_continuous continuous_subtype_val (fun x => x.property)
    exact (isClosed_eq (g := fun _ : U => (0 : ℂ)) hc continuous_const).isOpen_compl⟩

def goodWide {n k : ℕ} (U : Opens (ComplexModel n)) (H : ComplexModel n → ℂ)
    (hH : DifferentiableOn ℂ H U) : Opens (wideDomain k U) :=
  ⟨basePoint U ⁻¹' goodBase U H hH,
    (goodBase U H hH).isOpen.preimage (basePoint_smooth U).continuous⟩

def rationalVector {n k : ℕ} (H : ComplexModel n → ℂ) (G : Fin k → ComplexModel n → ℂ)
    (x : ComplexModel n) : ComplexModel k := WithLp.toLp 2 (fun i => G i x/H x)

private theorem base_split {n k : ℕ} (x : ComplexModel n) (w : ComplexModel k) :
    baseProjection n k ((EuclideanSpace.finAddEquivProd (𝕜 := ℂ)).symm (x,w)) = x := by
  change ((EuclideanSpace.finAddEquivProd (𝕜 := ℂ))
    ((EuclideanSpace.finAddEquivProd (𝕜 := ℂ)).symm (x,w))).1 = x
  rw [ContinuousLinearEquiv.apply_symm_apply]

private theorem fibre_split {n k : ℕ} (x : ComplexModel n) (w : ComplexModel k) :
    fibreProjection n k ((EuclideanSpace.finAddEquivProd (𝕜 := ℂ)).symm (x,w)) = w := by
  change ((EuclideanSpace.finAddEquivProd (𝕜 := ℂ))
    ((EuclideanSpace.finAddEquivProd (𝕜 := ℂ)).symm (x,w))).2 = w
  rw [ContinuousLinearEquiv.apply_symm_apply]

def rationalSection {n k : ℕ} (U : Opens (ComplexModel n)) (H : ComplexModel n → ℂ)
    (hH : DifferentiableOn ℂ H U) (G : Fin k → ComplexModel n → ℂ)
    (x : goodBase U H hH) : goodWide (k := k) U H hH := by
  refine ⟨⟨(EuclideanSpace.finAddEquivProd (𝕜 := ℂ)).symm
    (x.val.val,rationalVector H G x.val.val),?_⟩,?_⟩
  · change baseProjection n k _ ∈ U
    rw [base_split]
    exact x.val.property
  · change H (baseProjection n k _) ≠ 0
    rw [base_split]
    exact x.property

def goodProjection {n k : ℕ} (U : Opens (ComplexModel n)) (H : ComplexModel n → ℂ)
    (hH : DifferentiableOn ℂ H U) (z : goodWide (k := k) U H hH) : goodBase U H hH :=
  ⟨basePoint U z.val,z.property⟩

private theorem section_smooth {n k : ℕ} (U : Opens (ComplexModel n))
    (H : ComplexModel n → ℂ) (G : Fin k → ComplexModel n → ℂ)
    (hH : DifferentiableOn ℂ H U) (hG : ∀ i,DifferentiableOn ℂ (G i) U) :
    ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel (n+k)) ∞ (rationalSection U H hH G) := by
  have hR : ContDiffOn ℂ ∞ (rationalVector H G) {z | z ∈ U ∧ H z ≠ 0} := by
    apply (contDiffOn_piLp 2).mpr
    intro i
    exact ((contDiffOn_of_differentiableOn_complex (hG i) U.isOpen).mono (fun _ hz => hz.1)).div
      ((contDiffOn_of_differentiableOn_complex hH U.isOpen).mono (fun _ hz => hz.1)) (fun _ hz => hz.2)
  have hb : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞
      (fun x : goodBase U H hH => x.val.val) := contMDiff_subtype_val.comp contMDiff_subtype_val
  have hNative : ContDiffOn ℂ ∞ (fun z : ComplexModel n =>
      (EuclideanSpace.finAddEquivProd (𝕜 := ℂ) (n := n) (m := k)).symm
        (z,rationalVector H G z)) {z | z ∈ U ∧ H z ≠ 0} :=
    (EuclideanSpace.finAddEquivProd (𝕜 := ℂ) (n := n) (m := k)).symm.contDiff.comp_contDiffOn
      (contDiffOn_id.prodMk hR)
  have hs := hNative.contMDiffOn.comp_contMDiff hb (fun x => ⟨x.val.property,x.property⟩)
  apply (ContMDiff.subtypeVal_comp_iff (goodWide (k := k) U H hH) _).mp
  apply (ContMDiff.subtypeVal_comp_iff (wideDomain k U) _).mp
  exact hs

private theorem goodProjection_smooth {n k : ℕ} (U : Opens (ComplexModel n))
    (H : ComplexModel n → ℂ) (hH : DifferentiableOn ℂ H U) :
    ContMDiff 𝓘(ℂ,ComplexModel (n+k)) 𝓘(ℂ,ComplexModel n) ∞ (goodProjection (k := k) U H hH) := by
  apply (ContMDiff.subtypeVal_comp_iff (goodBase U H hH) _).mp
  exact (basePoint_smooth U).comp contMDiff_subtype_val

private theorem section_base {n k : ℕ} (U : Opens (ComplexModel n)) (H : ComplexModel n → ℂ)
    (hH : DifferentiableOn ℂ H U) (G : Fin k → ComplexModel n → ℂ) (x : goodBase U H hH) :
    basePoint U (rationalSection U H hH G x).val = x.val := by
  apply Subtype.ext
  exact base_split _ _

private theorem section_carrier {n k : ℕ} (U : Opens (ComplexModel n)) (C : Set U)
    (H : ComplexModel n → ℂ) (hH : DifferentiableOn ℂ H U) (G : Fin k → ComplexModel n → ℂ)
    (x : goodBase U H hH) (hx : x.val ∈ C) :
    (rationalSection U H hH G x).val ∈ graphClosure U C H G := by
  apply subset_closure
  refine ⟨(mem_denominatorSet U C H G _).mpr ⟨?_,?_⟩,?_⟩
  · rw [section_base]
    exact hx
  · intro i
    change H (baseProjection n k ((EuclideanSpace.finAddEquivProd (𝕜 := ℂ)).symm
      (x.val.val,rationalVector H G x.val.val))) *
      fibreProjection n k ((EuclideanSpace.finAddEquivProd (𝕜 := ℂ)).symm
        (x.val.val,rationalVector H G x.val.val)) i =
      G i (baseProjection n k ((EuclideanSpace.finAddEquivProd (𝕜 := ℂ)).symm
        (x.val.val,rationalVector H G x.val.val)))
    rw [base_split,fibre_split]
    change H x.val.val * (G i x.val.val/H x.val.val) = G i x.val.val
    have hn : H x.val.val ≠ 0 := x.property
    field_simp
  · intro hbad
    have hz := (mem_badSet U H (rationalSection U H hH G x).val).mp hbad
    change H (basePoint U (rationalSection U H hH G x).val).val = 0 at hz
    rw [section_base] at hz
    exact x.property hz

private theorem projection_section {n k : ℕ} (U : Opens (ComplexModel n)) (H : ComplexModel n → ℂ)
    (hH : DifferentiableOn ℂ H U) (G : Fin k → ComplexModel n → ℂ) (x : goodBase U H hH) :
    goodProjection U H hH (rationalSection U H hH G x) = x := by
  apply Subtype.ext
  exact section_base U H hH G x

private theorem section_projection {n k : ℕ} (U : Opens (ComplexModel n)) {C : Set U}
    (hC : IsComplexAnalyticSubset (n := n) C)
    (H : ComplexModel n → ℂ) (G : Fin k → ComplexModel n → ℂ)
    (hH : DifferentiableOn ℂ H U) (hG : ∀ i,DifferentiableOn ℂ (G i) U)
    (z : goodWide (k := k) U H hH) (hz : z.val ∈ graphClosure U C H G) :
    rationalSection U H hH G (goodProjection U H hH z) = z := by
  apply Subtype.ext
  apply Subtype.ext
  apply coordinates_injective
  · exact base_split _ _
  · change fibreProjection n k ((EuclideanSpace.finAddEquivProd (𝕜 := ℂ)).symm
      (baseProjection n k z.val.val,rationalVector H G (baseProjection n k z.val.val))) =
      fibreProjection n k z.val.val
    rw [fibre_split]
    ext i
    have hD := (mem_denominatorSet U C H G z.val).mp
      (graphClosure_subset_denominatorSet U hC H G hH hG hz)
    have hn : H (baseProjection n k z.val.val) ≠ 0 := z.property
    exact ((eq_div_iff hn).mpr ((mul_comm _ _).trans (hD.2 i))).symm

/-- Actual full ORIGINAL quotient sheaves, not merely an inverse point map. -/
def goodIso {n k : ℕ} (U : Opens (ComplexModel n)) {C : Set U}
    (hC : IsComplexAnalyticSubset (n := n) C)
    (H : ComplexModel n → ℂ) (G : Fin k → ComplexModel n → ℂ)
    (hH : DifferentiableOn ℂ H U) (hG : ∀ i,DifferentiableOn ℂ (G i) U) :
    actualSubspaceLocallyRingedSpace (n := n) ((Subtype.val : goodBase U H hH → U) ⁻¹' C) ≅
      actualSubspaceLocallyRingedSpace (n := n+k)
        ((Subtype.val : goodWide (k := k) U H hH → wideDomain k U) ⁻¹' graphClosure U C H G) :=
  actualSubspaceMutualRestrictionIso (section_smooth U H G hH hG) (goodProjection_smooth U H hH)
    (fun x hx => section_carrier U C H hH G x hx)
    (fun _z hz => (graphClosure_subset_denominatorSet U hC H G hH hG hz).1)
    (fun x _ => projection_section U H hH G x)
    (fun z hz => section_projection U hC H G hH hG z hz)

/-- The actual inverse commutes with projection as a FULL original sheaf map. -/
theorem goodIso_hom_over {n k : ℕ} (U : Opens (ComplexModel n)) {C : Set U}
    (hC : IsComplexAnalyticSubset (n := n) C)
    (H : ComplexModel n → ℂ) (G : Fin k → ComplexModel n → ℂ)
    (hH : DifferentiableOn ℂ H U) (hG : ∀ i,DifferentiableOn ℂ (G i) U) :
    ((goodIso U hC H G hH hG).hom ≫
      actualOpenSubspaceMap (n := n+k) (graphClosure U C H G) (goodWide U H hH)) ≫
        (projection U hC H G hH hG).hom.left =
      actualOpenSubspaceMap (n := n) C (goodBase U H hH) := by
  change ((actualSubspaceMap (section_smooth U H G hH hG)
    (fun x hx => section_carrier U C H hH G x hx)) ≫
      actualSubspaceMap contMDiff_subtype_val (fun _ hx => hx)) ≫
        actualSubspaceMap (basePoint_smooth U)
          (fun _z hz => (graphClosure_subset_denominatorSet U hC H G hH hG hz).1) =
      actualSubspaceMap contMDiff_subtype_val (fun _ hx => hx)
  rw [← actualSubspaceMap_comp,← actualSubspaceMap_comp]
  apply actualSubspaceMap_eqOn
  intro x hx
  exact section_base U H hH G x

end SGPT.Unibranch.PrimeNov16AnalyticNormalizationGoodIso
