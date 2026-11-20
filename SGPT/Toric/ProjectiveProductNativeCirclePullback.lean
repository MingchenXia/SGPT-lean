import SGPT.Toric.ProjectiveProductNativeDictionary
import SGPT.Foundations.Analysis.PlurisubharmonicPullback
import SGPT.Foundations.Analysis.Pending.AdmissiblePresentationHolomorphicPullback

set_option autoImplicit false
noncomputable section
namespace SGPT.Toric
open Set Filter
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.ProductComplexManifold
open scoped Topology

private def productChartLinear {n : ℕ} (a : Fin n → ℂˣ) (ε : Fin n → Bool) :
    ComplexModel n →ₗ[ℂ] ComplexModel n where
  toFun z := WithLp.toLp 2 (fun i => projectiveTorusChartFactor (a i) (ε i) * z i)
  map_add' z w := by
    ext i
    exact mul_add _ _ _
  map_smul' c z := by
    ext i
    change projectiveTorusChartFactor (a i) (ε i) * (c * z i) =
      c * (projectiveTorusChartFactor (a i) (ε i) * z i)
    ring

/-- The actual original binary-chart action is a genuine complex continuous linear map. -/
def projectiveProductTorusChartLinear {n : ℕ} (a : Fin n → ℂˣ) (ε : Fin n → Bool) :
    ComplexModel n →L[ℂ] ComplexModel n :=
  (productChartLinear a ε).toContinuousLinearMap

/-- The literal original factor quotient character is retained in every coordinate. -/
theorem projectiveProductTorusChartLinear_apply {n : ℕ} (a : Fin n → ℂˣ)
    (ε : Fin n → Bool) (z : ComplexModel n) (i : Fin n) :
    projectiveProductTorusChartLinear a ε z i = projectiveTorusChartFactor (a i) (ε i) * z i := rfl

private theorem chartLinear_split_fst (n : ℕ) (a : Fin (n + 1) → ℂˣ)
    (ε : Fin (n + 1) → Bool) (z : ComplexModel (n + 1)) :
    ((prodModelEquiv n 1).symm (projectiveProductTorusChartLinear a ε z)).1 =
      projectiveProductTorusChartLinear (Fin.init a) (Fin.init ε) ((prodModelEquiv n 1).symm z).1 := by
  ext i
  rfl

private theorem chartLinear_split_snd (n : ℕ) (a : Fin (n + 1) → ℂˣ)
    (ε : Fin (n + 1) → Bool) (z : ComplexModel (n + 1)) :
    ((prodModelEquiv n 1).symm (projectiveProductTorusChartLinear a ε z)).2 =
      projectiveTorusChartFactor (a (Fin.last n)) (ε (Fin.last n)) •
        ((prodModelEquiv n 1).symm z).2 := by
  ext i
  have hi : i = (0 : Fin 1) := Fin.eq_zero i
  subst i
  rfl

/-- The full original quotient action intertwines EVERY binary native inverse
chart with its actual complex diagonal map, also at coordinate boundary points. -/
theorem projectiveProductTorusAction_binary_chart_symm : (n : ℕ) → (a : Fin n → ℂˣ) →
    (ε : Fin n → Bool) → (z : ComplexModel n) →
    projectiveProductTorusAction n a ((projectiveProductNativeChart n ε).val.symm z) =
      (projectiveProductNativeChart n ε).val.symm (projectiveProductTorusChartLinear a ε z)
  | 0, _, _, z => by
    change z = projectiveProductTorusChartLinear _ _ z
    ext i
    exact Fin.elim0 i
  | n + 1, a, ε, z => by
    change (projectiveProductTorusAction n (Fin.init a)
        ((projectiveProductNativeChart n (Fin.init ε)).val.symm ((prodModelEquiv n 1).symm z).1),
      projectiveTorusAction (a (Fin.last n)) ((projectiveNativeChart (ε (Fin.last n))).val.symm
        ((prodModelEquiv n 1).symm z).2)) =
      ((projectiveProductNativeChart n (Fin.init ε)).val.symm
        ((prodModelEquiv n 1).symm (projectiveProductTorusChartLinear a ε z)).1,
      (projectiveNativeChart (ε (Fin.last n))).val.symm
        ((prodModelEquiv n 1).symm (projectiveProductTorusChartLinear a ε z)).2)
    rw [chartLinear_split_fst, chartLinear_split_snd]
    apply Prod.ext
    · exact projectiveProductTorusAction_binary_chart_symm n (Fin.init a) (Fin.init ε) _
    · exact projectiveTorusAction_chart_symm (a (Fin.last n)) (ε (Fin.last n)) _

/-- The exact original whole FS potential is unchanged by every binary-chart
unit character diagonal, including all zero coordinates. -/
theorem projectiveProductFSPotential_chartLinear {n : ℕ} {a : Fin n → ℂˣ}
    (ha : ∀ i, ‖(a i : ℂ)‖ = 1) (ε : Fin n → Bool) (z : ComplexModel n) :
    projectiveProductFSPotential n (projectiveProductTorusChartLinear a ε z) =
      projectiveProductFSPotential n z := by
  apply Finset.sum_congr rfl
  intro i _
  change Real.log (1 + Complex.normSq (projectiveTorusChartFactor (a i) (ε i) * z i)) = _
  simp only [← Complex.sq_norm, norm_mul, norm_projectiveTorusChartFactor (ha i), one_mul]

/-- The original circle action preserves arbitrary genuine native FS potentials.
Existing linear PSH pullback and open-map nondegeneracy are reused directly. -/
theorem isThetaPshPotential_comp_projectiveProductTorusAction {n : ℕ}
    {u : projectiveProductSpace n → EReal}
    (hu : IsThetaPshPotential (projectiveProductFSBackground n).form.val u)
    {a : Fin n → ℂˣ} (ha : ∀ i, ‖(a i : ℂ)‖ = 1) :
    IsThetaPshPotential (projectiveProductFSBackground n).form.val
      (fun p => u (projectiveProductTorusAction n a p)) := by
  refine ⟨?_, AdmissiblePresentationHolomorphicPullback.locallyNondegenerate_comp_of_isOpenMap
    (projectiveProductTorusHomeomorph n a).isOpenMap hu.2⟩
  intro e z _
  obtain ⟨ε, rfl⟩ := projectiveProductNativeChart_exhaustive e
  have hp := BoundedGlobalProduct.ThetaPlurisubharmonic.corrected_plurisubharmonicOn
    hu.1 (projectiveProductNativeChart n ε) (projectiveProductFSPotential_localPotential n ε)
  have hc : PlurisubharmonicOn (fun w =>
      chartFunction u (projectiveProductNativeChart n ε) (projectiveProductTorusChartLinear a ε w) +
        (projectiveProductFSPotential n (projectiveProductTorusChartLinear a ε w) : EReal)) univ := by
    simpa only [preimage_univ] using hp.comp_continuousLinearMap (projectiveProductTorusChartLinear a ε)
  refine ⟨univ, projectiveProductFSPotential n, mem_univ z,
    projectiveProductFSPotential_localPotential n ε, ?_⟩
  intro y hy
  apply (hc y hy).congr
  exact Eventually.of_forall fun w => by
    change u ((projectiveProductNativeChart n ε).val.symm (projectiveProductTorusChartLinear a ε w)) +
      (projectiveProductFSPotential n (projectiveProductTorusChartLinear a ε w) : EReal) =
        u (projectiveProductTorusAction n a ((projectiveProductNativeChart n ε).val.symm w)) +
          (projectiveProductFSPotential n w : EReal)
    rw [projectiveProductTorusAction_binary_chart_symm, projectiveProductFSPotential_chartLinear ha]

/-- Connectedness is transported from the actual finite product of original
connected projective lines through the produced coordinate homeomorphism. -/
instance projectiveProductConnectedSpace (n : ℕ) : ConnectedSpace (projectiveProductSpace n) :=
  (projectiveProductCoordinates n).symm.surjective.connectedSpace
    (projectiveProductCoordinates n).symm.continuous

end SGPT.Toric
