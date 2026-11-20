import SGPT.Foundations.Analysis.Pending.BlowupSequenceLocalDiscrepancy
import SGPT.Foundations.Analysis.Pending.HironakaAPI3
import SGPT.Foundations.Analysis.Pending.HolomorphicCoordinateFactorization

set_option autoImplicit false

/-! # Actual adapted Jacobian normal forms from admissible SNC geometry -/

open Set Filter Metric MeasureTheory
open scoped Topology Manifold ContDiff

universe u

namespace SGPT.Foundations.Analysis.Pending.AdmissibleSNCJacobianNormalForm

open FirstPass FirstPass.BlowupSequences FirstPass.HolomorphicMaps
  NormalCrossings HironakaAdmissibleSequence DivisorialChangeOfVariables

noncomputable section

private theorem mdifferentiableAt_adaptedPoint {n : ℕ} {Y : Type*}
    [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
    (x : Y) (Φ : LocalHolomorphicEquivAt (n := n) ((complexChartAt (n := n) x).val x))
    (hsrc : Φ.source ⊆ (complexChartAt (n := n) x).val.target)
    {z : ComplexModel n} (hz : z ∈ Φ.target) :
    MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n)
      (fun w => (complexChartAt (n := n) x).val.symm (Φ.invFun w)) z := by
  have hinv := (Φ.invFun_holomorphic.differentiableAt
    (Φ.isOpen_target.mem_nhds hz)).mdifferentiableAt
  have hsymm : MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n)
      (chartAt (ComplexModel n) x).symm (Φ.invFun z) :=
    ((contMDiffOn_chart_symm (I := 𝓘(ℂ, ComplexModel n)) (n := ∞) (x := x)).contMDiffAt
      ((chartAt (ComplexModel n) x).open_target.mem_nhds
        (hsrc (Φ.mapsTo_invFun hz)))).mdifferentiableAt (by simp)
  exact hsymm.comp z hinv

/-- Genuine nonexceptionality implies nonzero Jacobian in arbitrary actual adapted charts. -/
theorem complexJacobian_adapted_ne_zero_of_not_exceptional
    {n : ℕ} {X : Type u} [TopologicalSpace X]
    [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
    {Y : Type u} [TopologicalSpace Y]
    [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
    {π : Y → X} (hπ : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ π)
    (x : Y) (Φ : LocalHolomorphicEquivAt (n := n) ((complexChartAt (n := n) x).val x))
    (hsrc : Φ.source ⊆ (complexChartAt (n := n) x).val.target)
    {z : ComplexModel n} (hz : z ∈ Φ.target)
    (hzt : π ((complexChartAt (n := n) x).val.symm (Φ.invFun z)) ∈
      (complexChartAt (n := n) (π x)).val.source)
    (hne : (complexChartAt (n := n) x).val.symm (Φ.invFun z) ∉ exceptionalLocus n π) :
    complexJacobian (fun w => (complexChartAt (n := n) (π x)).val
      (π ((complexChartAt (n := n) x).val.symm (Φ.invFun w)))) z ≠ 0 := by
  classical
  let I := 𝓘(ℂ, ComplexModel n)
  let e := complexChartAt (n := n) x
  let d := complexChartAt (n := n) (π x)
  let T : ComplexModel n → Y := fun w => e.val.symm (Φ.invFun w)
  let C : Y → ComplexModel n := fun y => Φ.toFun (e.val y)
  have hp : MDifferentiableAt I I T z := mdifferentiableAt_adaptedPoint x Φ hsrc hz
  have hpoint : T z ∈ e.val.source := e.val.map_target (hsrc (Φ.mapsTo_invFun hz))
  have hround : e.val (T z) = Φ.invFun z := e.val.right_inv (hsrc (Φ.mapsTo_invFun hz))
  have hchart : MDifferentiableAt I I e.val (T z) :=
    ((contMDiffOn_chart (I := I) (n := ∞) (x := x)).contMDiffAt
      ((chartAt (ComplexModel n) x).open_source.mem_nhds hpoint)).mdifferentiableAt (by simp)
  have hto : DifferentiableAt ℂ Φ.toFun (e.val (T z)) := by
    rw [hround]
    exact Φ.toFun_holomorphic.differentiableAt (Φ.isOpen_source.mem_nhds (Φ.mapsTo_invFun hz))
  have hcoord : MDifferentiableAt I I C (T z) := hto.mdifferentiableAt.comp (T z) hchart
  have heq : (C ∘ T) =ᶠ[𝓝 z] id := by
    filter_upwards [Φ.isOpen_target.mem_nhds hz] with w hw
    dsimp only [C, T, Function.comp_apply, id_eq]
    rw [e.val.right_inv (hsrc (Φ.mapsTo_invFun hw)), Φ.right_inv w hw]
  have hleft : (mfderiv I I C (T z)).comp (mfderiv I I T z) =
      ContinuousLinearMap.id ℂ (ComplexModel n) := by
    rw [← mfderiv_comp z hcoord hp, heq.mfderiv_eq, mfderiv_id]
    rfl
  have hpinj : Function.Injective (mfderiv I I T z) := by
    have hli : Function.LeftInverse (mfderiv I I C (T z)) (mfderiv I I T z) :=
      fun v => DFunLike.congr_fun hleft v
    exact hli.injective
  let P : ComplexModel n →ₗ[ℂ] ComplexModel n :=
    { toFun := mfderiv I I T z
      map_add' := (mfderiv I I T z).map_add
      map_smul' := (mfderiv I I T z).map_smul }
  have hpbij : Function.Bijective (mfderiv I I T z) :=
    ⟨hpinj, (LinearMap.injective_iff_surjective (f := P)).mp hpinj⟩
  have hπbij : Function.Bijective (mfderiv I I π (T z)) := by
    simpa only [exceptionalLocus, mem_ofPred_eq, not_not] using hne
  have hd : MDifferentiableAt I I d.val (π (T z)) :=
    ((contMDiffOn_chart (I := I) (n := ∞) (x := π x)).contMDiffAt
      ((chartAt (ComplexModel n) (π x)).open_source.mem_nhds hzt)).mdifferentiableAt (by simp)
  have hdinv : (mfderiv I I d.val (π (T z))).IsInvertible := by
    have hmem : π (T z) ∈ (extChartAt I (π x)).source := by
      rw [extChartAt_source]
      exact hzt
    have h := isInvertible_mfderiv_extChartAt (I := I) (x := π x) hmem
    have hext : (extChartAt I (π x) : X → ComplexModel n) = d.val := by funext y; rfl
    rw [hext] at h
    exact h
  obtain ⟨L, hL⟩ := hdinv
  have hdbij : Function.Bijective (mfderiv I I d.val (π (T z))) := by
    rw [← hL]
    exact L.bijective
  have hπd : MDifferentiableAt I I π (T z) := (hπ (T z)).mdifferentiableAt (by simp)
  have hder : mfderiv I I (d.val ∘ π ∘ T) z =
      (mfderiv I I d.val (π (T z))).comp
        ((mfderiv I I π (T z)).comp (mfderiv I I T z)) := by
    rw [mfderiv_comp z hd (hπd.comp z hp), mfderiv_comp z hπd hp]
    rfl
  have hbij : Function.Bijective (mfderiv I I (d.val ∘ π ∘ T) z) := by
    rw [hder]
    exact hdbij.comp (hπbij.comp hpbij)
  rw [mfderiv_eq_fderiv] at hbij
  let Q := LinearEquiv.ofBijective (fderiv ℂ (d.val ∘ π ∘ T) z).toLinearMap hbij
  change LinearMap.det (fderiv ℂ (d.val ∘ π ∘ T) z).toLinearMap ≠ 0
  change LinearMap.det (Q : ComplexModel n →ₗ[ℂ] ComplexModel n) ≠ 0
  rw [← LinearEquiv.coe_det]
  exact Units.ne_zero _

private theorem differentiableOn_complexJacobian {n : ℕ}
    {F : ComplexModel n → ComplexModel n} {U : Set (ComplexModel n)}
    (hU : IsOpen U) (hF : DifferentiableOn ℂ F U) :
    DifferentiableOn ℂ (complexJacobian F) U := by
  classical
  have hentry (i j : Fin n) : DifferentiableOn ℂ
      (fun z => (fderiv ℂ F z (FirstPass.MongeAmpere.coordinateVector j)) i) U :=
    (EuclideanSpace.proj (𝕜 := ℂ) i).differentiable.comp_differentiableOn
      (FirstPass.differentiableOn_fderiv_apply_of_isOpen hF hU
        (FirstPass.MongeAmpere.coordinateVector j))
  have hdet : complexJacobian F = fun z =>
      ∑ σ : Equiv.Perm (Fin n), Equiv.Perm.sign σ •
        ∏ a : Fin n, (fderiv ℂ F z (FirstPass.MongeAmpere.coordinateVector a)) (σ a) := by
    funext z
    rw [complexJacobian, ContinuousLinearMap.det,
      ← FirstPass.MongeAmpere.det_standardMatrix, Matrix.det_apply]
    simp only [FirstPass.MongeAmpere.standardMatrix_apply]
    rfl
  rw [hdet]
  refine DifferentiableOn.fun_sum fun σ _ =>
    (?_ : DifferentiableOn ℂ _ U).const_smul _
  induction (Finset.univ : Finset (Fin n)) using Finset.induction_on with
  | empty => simp [differentiableOn_const]
  | insert a s ha ih =>
      simp only [Finset.prod_insert ha]
      exact (hentry (σ a) a).mul ih


/-- Genuine fixed adapted coordinates supply all Jacobian orders and the unit internally. -/
theorem exists_unit_monomial_jacobian_in_adapted_coordinates
    {n : ℕ} {X : Type u} [TopologicalSpace X]
    [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
    {Y : Type u} [TopologicalSpace Y]
    [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
    {E₀ : List (Set X)} {F : Set X} {π : Y → X} {E : List (Set Y)}
    (hπ : IsAdmissibleBlowupSequence n X E₀ F Y π E) (hE : IsSNCDivisor n E) (x : Y)
    (S : Fin E.length → Finset (Fin n))
    (Φ : LocalHolomorphicEquivAt (n := n) ((complexChartAt (n := n) x).val x))
    (hsrc : Φ.source ⊆ (complexChartAt (n := n) x).val.target)
    (h0 : Φ.toFun ((complexChartAt (n := n) x).val x) = 0)
    (hcard : ∀ i, x ∈ E.get i → (S i).card = 1)
    (hflat : ∀ i, x ∈ E.get i → ∀ {y : Y}, y ∈ (complexChartAt (n := n) x).val.source →
      (complexChartAt (n := n) x).val y ∈ Φ.source →
      (y ∈ E.get i ↔ Φ.toFun ((complexChartAt (n := n) x).val y) ∈ coordSubspace (S i))) :
    ∃ (b : Fin n → ℕ) (H : ComplexModel n → ℂ),
      (∀ᶠ z in 𝓝 0, DifferentiableAt ℂ H z) ∧ H 0 ≠ 0 ∧
      complexJacobian (fun z => (complexChartAt (n := n) (π x)).val
        (π ((complexChartAt (n := n) x).val.symm (Φ.invFun z)))) =ᶠ[𝓝 0]
        fun z => H z * ∏ j : Fin n, z j ^ b j := by
  classical
  let e := complexChartAt (n := n) x
  let d := complexChartAt (n := n) (π x)
  let T : ComplexModel n → Y := fun z => e.val.symm (Φ.invFun z)
  let G : ComplexModel n → ComplexModel n := fun z => d.val (π (T z))
  let U : Set (ComplexModel n) := Φ.target ∩ {z | π (T z) ∈ d.val.source}
  have hπc := hπ.isBlowupSequence.contMDiff
  have h0t : (0 : ComplexModel n) ∈ Φ.target := by
    rw [← h0]
    exact Φ.mapsTo_toFun Φ.center_mem_source
  have hinv0 : Φ.invFun 0 = e.val x := by
    rw [← h0]
    exact Φ.left_inv _ Φ.center_mem_source
  have hT0 : T 0 = x := by
    dsimp only [T]
    rw [hinv0, e.val.left_inv (mem_chart_source (ComplexModel n) x)]
  have hTc : ContinuousOn T Φ.target := fun z hz =>
    (mdifferentiableAt_adaptedPoint x Φ hsrc hz).continuousAt.continuousWithinAt
  have hU : IsOpen U :=
    (hπc.continuous.comp_continuousOn hTc).isOpen_inter_preimage Φ.isOpen_target d.val.open_source
  have h0U : (0 : ComplexModel n) ∈ U := by
    refine ⟨h0t, ?_⟩
    change π (T 0) ∈ d.val.source
    rw [hT0]
    exact mem_complexChartAt_source _
  have hT : Tendsto T (𝓝 0) (𝓝 x) := by
    have hc : ContinuousAt T 0 := (mdifferentiableAt_adaptedPoint x Φ hsrc h0t).continuousAt
    simpa only [hT0] using hc.tendsto
  have hG : DifferentiableOn ℂ G U := by
    intro z hz
    have hw : Φ.invFun z ∈ coordinateDomain π e d :=
      ⟨hsrc (Φ.mapsTo_invFun hz.1), hz.2⟩
    have hcd : DifferentiableAt ℂ (coordinateMap π e d) (Φ.invFun z) :=
      (coordinateMap_contDiffAt hπc e d hw).differentiableAt (by simp)
    have hi := Φ.invFun_holomorphic.differentiableAt (Φ.isOpen_target.mem_nhds hz.1)
    exact (hcd.comp z hi).differentiableWithinAt
  have hJ : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ (complexJacobian G) z := by
    have hJd := differentiableOn_complexJacobian hU hG
    filter_upwards [hU.mem_nhds h0U] with z hz
    exact hJd.differentiableAt (hU.mem_nhds hz)
  have havoid : ∀ᶠ y in 𝓝 x, ∀ i : Fin E.length, x ∉ E.get i → y ∉ E.get i := by
    apply eventually_all.mpr
    intro i
    by_cases hxi : x ∈ E.get i
    · exact Eventually.of_forall fun _ h => (h hxi).elim
    · have hi : ∀ᶠ y in 𝓝 x, y ∉ E.get i :=
        (hE.1 _ (List.get_mem _ _)).isOpen_compl.mem_nhds hxi
      exact hi.mono fun _ hy _ => hy
  have hzero : ∀ᶠ z in 𝓝 0, complexJacobian G z = 0 → ∃ j : Fin n, z j = 0 := by
    filter_upwards [hU.mem_nhds h0U, hT.eventually havoid] with z hz hzavoid hzero
    have hexc : T z ∈ exceptionalLocus n π := by
      by_contra hne
      exact complexJacobian_adapted_ne_zero_of_not_exceptional hπc x Φ hsrc hz.1 hz.2 hne hzero
    obtain ⟨H, hHE, hzH⟩ := mem_iUnion₂.mp
      ((HironakaAPI3.exceptionalLocus_subset_of_isAdmissibleBlowupSequence hπ).1 hexc)
    have hHE' : H ∈ E := List.mem_of_mem_drop hHE
    obtain ⟨i, hi⟩ := List.exists_mem_iff_get.mp (show ∃ H ∈ E, T z ∈ H from ⟨H, hHE', hzH⟩)
    have hxi : x ∈ E.get i := by
      by_contra hx
      exact hzavoid i hx hi
    have ht : Φ.invFun z ∈ e.val.target := hsrc (Φ.mapsTo_invFun hz.1)
    have hys : T z ∈ e.val.source := e.val.map_target ht
    have hps : e.val (T z) ∈ Φ.source := by
      dsimp only [T]
      rw [e.val.right_inv ht]
      exact Φ.mapsTo_invFun hz.1
    have heq : Φ.toFun (e.val (T z)) = z := by
      dsimp only [T]
      rw [e.val.right_inv ht, Φ.right_inv z hz.1]
    have hzsub : z ∈ coordSubspace (S i) := by
      rw [← heq]
      exact (hflat i hxi hys hps).mp hi
    have hpos : 0 < (S i).card := by rw [hcard i hxi]; norm_num
    obtain ⟨j, hj⟩ := Finset.card_pos.mp hpos
    exact ⟨j, hzsub j hj⟩
  obtain ⟨b, H, hH, hH0, heq⟩ :=
    HolomorphicCoordinateFactorization.exists_unit_mul_coordinate_monomial_of_zero_locus hJ hzero
  exact ⟨b, H, hH, hH0, heq⟩

/-- The unit and all Jacobian monomial orders follow from actual admissible SNC geometry. -/
theorem exists_adapted_unit_monomial_jacobian
    {n : ℕ} {X : Type u} [TopologicalSpace X]
    [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
    {Y : Type u} [TopologicalSpace Y]
    [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
    {E₀ : List (Set X)} {F : Set X} {π : Y → X} {E : List (Set Y)}
    (hπ : IsAdmissibleBlowupSequence n X E₀ F Y π E) (hE : IsSNCDivisor n E) (x : Y) :
    ∃ (S : Fin E.length → Finset (Fin n))
      (Φ : LocalHolomorphicEquivAt (n := n) ((complexChartAt (n := n) x).val x)),
      Φ.source ⊆ (complexChartAt (n := n) x).val.target ∧
      Φ.toFun ((complexChartAt (n := n) x).val x) = 0 ∧
      (∀ i, x ∈ E.get i → (S i).card = 1) ∧ Set.InjOn S {i | x ∈ E.get i} ∧
      (∀ i, x ∈ E.get i → ∀ {y : Y}, y ∈ (complexChartAt (n := n) x).val.source →
        (complexChartAt (n := n) x).val y ∈ Φ.source →
        (y ∈ E.get i ↔ Φ.toFun ((complexChartAt (n := n) x).val y) ∈ coordSubspace (S i))) ∧
      ∃ (b : Fin n → ℕ) (H : ComplexModel n → ℂ),
        (∀ᶠ z in 𝓝 0, DifferentiableAt ℂ H z) ∧ H 0 ≠ 0 ∧
        complexJacobian (fun z => (complexChartAt (n := n) (π x)).val
          (π ((complexChartAt (n := n) x).val.symm (Φ.invFun z)))) =ᶠ[𝓝 0]
          fun z => H z * ∏ j : Fin n, z j ^ b j := by
  obtain ⟨S, ⟨Φ, hsrc, h0, hflat⟩, hcard, hinj⟩ := hE.2 x
  obtain ⟨b, H, hH, hH0, heq⟩ :=
    exists_unit_monomial_jacobian_in_adapted_coordinates hπ hE x S Φ hsrc h0 hcard hflat
  exact ⟨S, Φ, hsrc, h0, hcard, hinj, hflat, b, H, hH, hH0, heq⟩

end
end SGPT.Foundations.Analysis.Pending.AdmissibleSNCJacobianNormalForm
