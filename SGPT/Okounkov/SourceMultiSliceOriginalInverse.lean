import SGPT.Okounkov.SourceMultiSliceOriginalCarrier

/-! The genuine inverse canonical original carrier map is holomorphic in
both actual inherited atlases, including source/target dimension zero. -/
set_option autoImplicit false
noncomputable section
universe u
namespace SGPT.Okounkov.SourceMultiSlice
open Set
open scoped Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending

/-- At k=0 the genuine inverse is literal original subtype projection. -/
theorem originalCarrierHomeomorph_symm_zero (m : ℕ)
    (F : OriginalFlagGeometry.{u} (m + 0)) :
    ⇑(originalCarrierHomeomorph m 0 F).symm = Subtype.val := by
  funext x
  exact congrArg Subtype.val ((originalCarrierHomeomorph m 0 F).apply_symm_apply x)

/-- Reindex the same genuine inherited submanifold atlases along an actual
proved dimension equality; the regularity proofs are proof-irrelevant. -/
theorem contMDiff_inherited_iff_castDimension
    {nX nY d e : ℕ} {X Y : Type u}
    [TopologicalSpace X] [ChartedSpace (ComplexModel nX) X] [IsComplexManifold nX X]
    [TopologicalSpace Y] [ChartedSpace (ComplexModel nY) Y] [IsComplexManifold nY Y]
    {S : Set X} {T : Set Y} (hde : d = e)
    (hdX : d ≤ nX) (hdY : d ≤ nY) (heX : e ≤ nX) (heY : e ≤ nY)
    (hSd : ∀ x ∈ S, RegularAtDim (n := nX) S x d)
    (hTd : ∀ y ∈ T, RegularAtDim (n := nY) T y d)
    (hSe : ∀ x ∈ S, RegularAtDim (n := nX) S x e)
    (hTe : ∀ y ∈ T, RegularAtDim (n := nY) T y e) (f : S → T) :
    (letI := SubmanifoldChartedSpace.chartedSpace hdX hSd
     letI := SubmanifoldChartedSpace.chartedSpace hdY hTd
     ContMDiff 𝓘(ℂ, ComplexModel d) 𝓘(ℂ, ComplexModel d) ∞ f) ↔
    (letI := SubmanifoldChartedSpace.chartedSpace heX hSe
     letI := SubmanifoldChartedSpace.chartedSpace heY hTe
     ContMDiff 𝓘(ℂ, ComplexModel e) 𝓘(ℂ, ComplexModel e) ∞ f) := by
  subst e
  rfl

/-- Every nested-to-direct original carrier comparison is genuinely
biholomorphic, with both original inherited complex structures. -/
theorem originalCarrierHomeomorph_symm_contMDiff (m k : ℕ)
    (F : OriginalFlagGeometry.{u} (m + k)) :
    letI := directCarrierCharts m k F
    letI := directCarrierComplex m k F
    ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel m) ∞
      (originalCarrierHomeomorph m k F).symm := by
  induction k with
  | zero =>
      let _ := directCarrierCharts m 0 F
      let _ := directCarrierComplex m 0 F
      rw [originalCarrierHomeomorph_symm_zero]
      exact SubmanifoldChartedSpace.contMDiff_val (by omega) (directCarrier_regular m 0 F)
  | succ k ih =>
      let _ := directCarrierCharts m (k + 1) F
      let _ := directCarrierComplex m (k + 1) F
      let _ := directCarrierCharts m k F.tail
      let _ := directCarrierComplex m k F.tail
      let _ : ChartedSpace (ComplexModel m) (F.flag (originalIndex m k).succ) :=
        directCarrierCharts m (k + 1) F
      let _ : IsComplexManifold m (F.flag (originalIndex m k).succ) :=
        directCarrierComplex m (k + 1) F
      have htail : ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel m) ∞
          (F.tailComponentHomeomorph (originalIndex m k)).symm := by
        let d := m + k - k
        have hSd : ∀ x ∈ F.flag (originalIndex m k).succ,
            RegularAtDim (n := m + k + 1) (F.flag (originalIndex m k).succ) x d := by
          simpa only [originalIndex, Fin.val_succ, Fin.val_mk, d, Nat.add_sub_cancel] using
            (F.smooth.2.2 (originalIndex m k).succ).2.2
        have hTd : ∀ y ∈ F.tail.flag (originalIndex m k),
            RegularAtDim (n := m + k) (F.tail.flag (originalIndex m k)) y d :=
          (F.tail.smooth.2.2 (originalIndex m k)).2.2
        exact (contMDiff_inherited_iff_castDimension (by dsimp [d]; omega)
          (by dsimp [d]; omega) (by dsimp [d]; omega) (by omega) (by omega)
          hSd hTd (directCarrier_regular m (k + 1) F)
          (directCarrier_regular m k F.tail)
          (F.tailComponentHomeomorph (originalIndex m k)).symm).mp
            (F.contMDiff_tailComponentHomeomorph_symm (originalIndex m k))
      rw [originalCarrierHomeomorph_symm_succ]
      exact (ih F.tail).comp htail
end SGPT.Okounkov.SourceMultiSlice
