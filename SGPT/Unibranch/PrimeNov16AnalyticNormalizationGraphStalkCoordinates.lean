import SGPT.Unibranch.PrimeNov16AnalyticNormalizationCentralStalkInjective

/-! Actual coordinate polynomial surjectivity, from manufactured monic relations.
Blueprint: prime-nov16-analytic-normalization-graph-stalk-coordinates.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter TopologicalSpace Polynomial
open scoped Topology
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open HolGerm GermAlgebraicParametrization GermParametrizationData RegularLocusDense
open SGPT.Foundations.Analysis.Pending.HironakaActualAnalyticSubspace
namespace SGPT.Unibranch.PrimeNov16AnalyticNormalizationGraphStalkCoordinates
open PrimeNov16AnalyticNormalizationDenominatorGraph
open PrimeNov16AnalyticNormalizationGraphFinite
open PrimeNov16AnalyticNormalizationGraphStalkFinite
open PrimeNov16AnalyticNormalizationStalkCalculus
open PrimeNov16AnalyticNormalizationGraphOriginalStalk
open PrimeNov16AnalyticNormalizationCentralStalkInjective

theorem graph_native_monic_relations {n k : ℕ}
    (U : Opens (ComplexModel n)) (C : Set U)
    (H : ComplexModel n → ℂ) (G : Fin k → ComplexModel n → ℂ)
    (d : Fin k → ℕ) (a : Fin k → ℕ → ComplexModel n → ℂ)
    (ha : ∀ i j,j < d i → DifferentiableOn ℂ (a i j) U)
    (hmonic : ∀ x : C,H x.val.val ≠ 0 → ∀ i,
      monicEval (d i) (a i) x.val.val (G i x.val.val/H x.val.val) = 0)
    (p : graphClosure U C H G) :
    ∀ r (hr : r < n+k), n ≤ r →
      ∃ P : (HolGerm (ComplexModel n))[X], P.Monic ∧
        evalGerm (n+k) P (coordGerm (n+k) r hr) ∈
          AnalyticGermDecomposition.vanishingIdeal
            {v : ComplexModel (n+k) | v+p.val.val ∈ nativeCarrier U C H G} := by
  intro r hr hnr
  let i : Fin k := ⟨r-n,by omega⟩
  have hi : Fin.natAdd n i = (⟨r,hr⟩ : Fin (n+k)) := by
    apply Fin.ext
    simp only [Fin.val_natAdd]
    dsimp [i]
    omega
  let b : ℕ → ComplexModel n → ℂ := fun j x =>
    if j < d i then a i j (x+baseProjection n k p.val.val) else 0
  have hb : ∀ j,∀ᶠ x in 𝓝 (0 : ComplexModel n),DifferentiableAt ℂ (b j) x := by
    intro j
    by_cases hj : j < d i
    · have ht : Tendsto (fun x : ComplexModel n => x+baseProjection n k p.val.val)
          (𝓝 0) (𝓝 (baseProjection n k p.val.val)) := by
        simpa only [zero_add] using
          (show Continuous (fun x : ComplexModel n => x+baseProjection n k p.val.val)
            from continuous_id.add continuous_const).tendsto (0 : ComplexModel n)
      filter_upwards [ht.eventually (U.isOpen.mem_nhds p.val.property)] with x hx
      change DifferentiableAt ℂ (fun x => if j < d i then
        a i j (x+baseProjection n k p.val.val) else 0) x
      simp only [if_pos hj]
      exact ((ha i j hj).differentiableAt (U.isOpen.mem_nhds hx)).comp x
        (differentiableAt_id.add_const _)
    · change ∀ᶠ x in 𝓝 (0 : ComplexModel n),DifferentiableAt ℂ
        (fun x => if j < d i then a i j (x+baseProjection n k p.val.val) else 0) x
      simp only [if_neg hj]
      exact Eventually.of_forall fun _ => differentiableAt_const (0 : ℂ)
  apply PrimeNov16AnalyticNormalizationNativeMonic.exists_monic_germ_of_native_equation
    (nativeCarrier U C H G) p.val.val hr (d i) b hb
  apply Eventually.of_forall
  intro v hv
  obtain ⟨z,hz,hzv⟩ := hv
  have hroot := monic_on_graphClosure U H G d a ha hmonic hz i
  have hbase : baseProjection n k z.val =
      coordinateProjection (n+k) n v + baseProjection n k p.val.val := by
    rw [hzv,map_add,baseProjection_coordinateProjection]
  have hfibre : fibreProjection n k z.val i = v ⟨r,hr⟩+p.val.val ⟨r,hr⟩ := by
    rw [fibreProjection_coordinate,hzv]
    change (v+p.val.val) (Fin.natAdd n i) = _
    rw [hi]
    rfl
  rw [hbase,hfibre] at hroot
  change monicEval (d i) b (coordinateProjection (n+k) n v)
    (v ⟨r,hr⟩+p.val.val ⟨r,hr⟩) = 0
  rw [monicEval]
  convert hroot using 1
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  simp only [b,if_pos (Finset.mem_range.mp hj)]


def graphGermMap {n k : ℕ} (U : Opens (ComplexModel n)) (C : Set U)
    (H : ComplexModel n → ℂ) (G : Fin k → ComplexModel n → ℂ)
    (p : graphClosure U C H G) : HolGerm (ComplexModel (n+k)) →+*
      ((actualSubspaceSheaf (n := n+k) (graphClosure U C H G)).presheaf.stalk p).carrier :=
  (nativeOriginalStalkEquiv U C H G p).toRingHom.comp
    ((translatedStalkEquiv (nativeCarrier U C H G) (nativePoint U C H G p)).symm.toRingHom.comp
      (Ideal.Quotient.mk
        (AnalyticGermDecomposition.vanishingIdeal
          {v : ComplexModel (n+k) | v+p.val.val ∈ nativeCarrier U C H G})))

def graphCoordinate {n k : ℕ} (U : Opens (ComplexModel n)) (C : Set U)
    (H : ComplexModel n → ℂ) (G : Fin k → ComplexModel n → ℂ)
    (p : graphClosure U C H G) (i : Fin (n+k)) :
    ((actualSubspaceSheaf (n := n+k) (graphClosure U C H G)).presheaf.stalk p).carrier :=
  graphGermMap U C H G p (coord i)

theorem graphGermMap_base_square {n k : ℕ} (U : Opens (ComplexModel n)) (C : Set U)
    (H : ComplexModel n → ℂ) (G : Fin k → ComplexModel n → ℂ)
    (p : graphClosure U C H G) (f : HolGerm (ComplexModel n)) :
    graphGermMap U C H G p (projGerm (n+k) n f) = graphStalkStructureMap U C H G p f := rfl

theorem graphGermMap_polynomial {n k : ℕ} (U : Opens (ComplexModel n)) (C : Set U)
    (H : ComplexModel n → ℂ) (G : Fin k → ComplexModel n → ℂ)
    (p : graphClosure U C H G)
    (P : MvPolynomial (Fin (n+k)) (HolGerm (ComplexModel n))) :
    graphGermMap U C H G p (MvPolynomial.eval₂ (projGerm (n+k) n) coord P) =
      MvPolynomial.eval₂ (graphStalkStructureMap U C H G p) (graphCoordinate U C H G p) P := by
  rw [MvPolynomial.hom_eval₂]
  rfl

theorem actual_graph_polynomial_surjective {n k : ℕ}
    (U : Opens (ComplexModel n)) (C : Set U)
    (H : ComplexModel n → ℂ) (G : Fin k → ComplexModel n → ℂ)
    (d : Fin k → ℕ) (a : Fin k → ℕ → ComplexModel n → ℂ)
    (ha : ∀ i j,j < d i → DifferentiableOn ℂ (a i j) U)
    (hmonic : ∀ x : C,H x.val.val ≠ 0 → ∀ i,
      monicEval (d i) (a i) x.val.val (G i x.val.val/H x.val.val) = 0)
    (p : graphClosure U C H G) :
    Function.Surjective (MvPolynomial.eval₂ (graphStalkStructureMap U C H G p)
      (graphCoordinate U C H G p)) := by
  intro r
  obtain ⟨P,hP⟩ := actual_stalk_polynomial_surjective (Nat.le_add_right n k)
    (nativeCarrier U C H G) (nativePoint U C H G p)
    (graph_native_monic_relations U C H G d a ha hmonic p)
    ((nativeOriginalStalkEquiv U C H G p).symm r)
  refine ⟨P,?_⟩
  rw [← graphGermMap_polynomial]
  exact (congrArg (nativeOriginalStalkEquiv U C H G p) hP).trans
    ((nativeOriginalStalkEquiv U C H G p).apply_symm_apply r)

theorem central_graph_polynomial_surjective {n k : ℕ}
    {Z : Set (ComplexModel n)} (hZ : AnalyticGermDecomposition.IsIrreducibleGerm Z)
    (U : Opens (ComplexModel n))
    (hC : IsComplexAnalyticSubset (n := n) {x : U | x.val ∈ Z})
    (H : ComplexModel n → ℂ) (G : Fin k → ComplexModel n → ℂ)
    (hH : DifferentiableOn ℂ H U) (hG : ∀ i,DifferentiableOn ℂ (G i) U)
    (p : graphClosure U {x : U | x.val ∈ Z} H G)
    (hp : baseProjection n k p.val.val = 0)
    (d : Fin k → ℕ) (a : Fin k → ℕ → ComplexModel n → ℂ)
    (ha : ∀ i j,j < d i → DifferentiableOn ℂ (a i j) U)
    (hmonic : ∀ x : {x : U | x.val ∈ Z},H x.val.val ≠ 0 → ∀ i,
      monicEval (d i) (a i) x.val.val (G i x.val.val/H x.val.val) = 0) :
    Function.Surjective (MvPolynomial.eval₂ (centralBaseMap hZ U hC H G hH hG p hp)
      (graphCoordinate U {x : U | x.val ∈ Z} H G p)) := by
  intro r
  obtain ⟨P,hP⟩ := actual_graph_polynomial_surjective U _ H G d a ha hmonic p r
  refine ⟨MvPolynomial.map (Ideal.Quotient.mk (AnalyticGermDecomposition.vanishingIdeal Z)) P,?_⟩
  rw [MvPolynomial.eval₂_map]
  exact hP

end SGPT.Unibranch.PrimeNov16AnalyticNormalizationGraphStalkCoordinates
