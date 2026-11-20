import SGPT.Foundations.Analysis.Pending.SubmanifoldACTopMass
import SGPT.Foundations.Analysis.Pending.GlobalDiagonalScaling
import SGPT.Foundations.Analysis.Pending.ShiftedRooftopLimit
import SGPT.Foundations.Analysis.Pending.CodimOneSupport

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The restricted absolutely continuous mass IS the non-pluripolar mass of the restriction

Blueprint `ana:mass-calculus`, second sentence: *if an almost positive current has smooth analytic
singularities and restricts to a closed complex submanifold, its positive perturbation has equal
absolutely continuous and non-pluripolar top-degree integrals on that submanifold.*

Let `p` be an admissible presentation along `V` (`T = θ + ddᶜu ∈ α` with smooth analytic
singularities, `T + εω ≥ 0`, `V ⊄ {u = -∞}`), where `V` is a closed submanifold: regular of
dimension `dim V` at each of its points.  Then

  `acTopMass p = ∫_V ⟨((θ + εω)|_V + ddᶜ(u|_V))^{dim V}⟩`
  (`acTopMass_eq_diagonalPotentialMass_restrict`).

* `≤` is `SubmanifoldACTopMass.acTopMass_le_diagonalPotentialMass_restrict`.
* `≥` (`diagonalPotentialMass_restrict_le_acTopMass`): every point `y` of the compact `↥V` is the
  centre of a regular patch `Q_y` of `V`, and the target patch of `Q_y`
  (`SubmanifoldPatchTransport.targetPatch`) parametrizes `↥V` on a ball `B(0, r_y)`.  The flattened
  coordinate of `Q_y` is continuous on `↥V`, so the points of `↥V` whose coordinate lies in that
  ball form an open neighbourhood `N_y` of `y`, entirely parametrized.  Finitely many `N_y` cover
  `↥V`; disjointify them and remove the poles.  The parameter pieces form a regular-piece family of
  `V`, the densities of `p` and of `p|_V` agree on them
  (`SubmanifoldRestrictedPresentation.patchDensity_targetPatch`), and on the complex manifold `↥V`
  each parameter integral is the non-pluripolar measure of its image
  (`FullSpaceAmbientComparison.lintegral_patchDensity_eq_globalMixedMeasure_image`).  The images
  exhaust `↥V` minus the poles, and the poles of a theta-PSH potential carry no non-pluripolar mass.

Sorry-free.
-/

open Set Filter MeasureTheory
open scoped Topology Manifold ContDiff ENNReal

universe u

namespace SGPT.Foundations.Analysis.Pending.RestrictedMassEquality

noncomputable section

open FirstPass FirstPass.PositiveClasses FirstPass.NumericalRestrictedVolumeScaffold
  FirstPass.NumericalRestrictedVolume SubmanifoldChartedSpace SubmanifoldPatchTransport
  SubmanifoldRestrictedPresentation GlobalNonPluripolar FirstPass.RegularLocusDense

variable {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] {V : ClosedIrreducibleAnalyticSubvariety n X}

variable (hk : V.dim ≤ n) (hW : ∀ x ∈ V.carrier, RegularAtDim (n := n) V.carrier x V.dim)

/-- The regular patch of `V` centred at a point of `V`, read off from the regularity of `V` there. -/
def patchAt (y : V.carrier) : RegularPatch V where
  center := y.1
  center_mem := (hW y.1 y.2).2.1
  flattening := (hW y.1 y.2).2.2.choose
  source_subset := (hW y.1 y.2).2.2.choose_spec.1
  center_to_zero := (hW y.1 y.2).2.2.choose_spec.2.1
  flattens := fun hy hyΦ => (hW y.1 y.2).2.2.choose_spec.2.2 hy hyΦ

theorem patchAt_center (y : V.carrier) : (patchAt hW y).center = y.1 := rfl

/-- The centre lies in the domain of the flattened coordinate of its patch. -/
theorem mem_ambSource_patchAt (y : V.carrier) :
    y.1 ∈ (patchFlatData (patchAt hW y)).ambSource :=
  ⟨mem_complexChartAt_source y.1, (hW y.1 y.2).2.2.choose.center_mem_source⟩

/-- The flattened coordinate of the centre is `0`. -/
theorem toCoord_patchAt_self (y : V.carrier) :
    (patchFlatData (patchAt hW y)).toCoord y = 0 := by
  change coordinateProjection n V.dim
    ((hW y.1 y.2).2.2.choose.toFun ((complexChartAt (n := n) y.1).val y.1)) = 0
  rw [(hW y.1 y.2).2.2.choose_spec.2.1, map_zero]

/-- The points of `↥V` whose flattened coordinate in the patch at `y` lies in the ball `B(0, r)`. -/
def coordNbhd (y : V.carrier) (r : ℝ) : Set V.carrier :=
  Subtype.val ⁻¹' (patchFlatData (patchAt hW y)).ambSource ∩
    (patchFlatData (patchAt hW y)).toCoord ⁻¹' Metric.ball (0 : ComplexModel V.dim) r

theorem isOpen_coordNbhd (y : V.carrier) (r : ℝ) : IsOpen (coordNbhd hW y r) :=
  (patchFlatData (patchAt hW y)).continuousOn_toCoord.isOpen_inter_preimage
    ((patchFlatData (patchAt hW y)).isOpen_ambSource.preimage continuous_subtype_val)
    Metric.isOpen_ball

theorem mem_coordNbhd_self (y : V.carrier) {r : ℝ} (hr : 0 < r) : y ∈ coordNbhd hW y r :=
  ⟨mem_ambSource_patchAt hW y, by
    rw [mem_preimage, toCoord_patchAt_self hW y]
    exact Metric.mem_ball_self hr⟩

variable [ConnectedSpace V.carrier] [Nonempty V.carrier]

/-- On the ball where the target patch is defined, it parametrizes `↥V` as the patch at `y` does. -/
theorem val_targetPatch_patchAt (y : V.carrier) {r : ℝ}
    (hball : ∀ v ∈ Metric.ball (0 : ComplexModel V.dim) r,
      v ∈ (patchAt hW y).parameterDomain ∧
        (letI := chartedSpace hk hW
        haveI := isComplexManifold_chartedSpace hk hW
        v - 0 ∈ (targetPatch hk hW (patchAt hW y)
          (RegularPatchNeighborhood.RegularPatch.zero_mem_parameterDomain _)).parameterDomain))
    {v : ComplexModel V.dim} (hv : v ∈ Metric.ball (0 : ComplexModel V.dim) r) :
    letI := chartedSpace hk hW
    haveI := isComplexManifold_chartedSpace hk hW
    (((targetPatch hk hW (patchAt hW y)
      (RegularPatchNeighborhood.RegularPatch.zero_mem_parameterDomain _)).toManifold v :
        V.carrier) : X) = (patchAt hW y).toManifold v := by
  let := chartedSpace hk hW
  have := isComplexManifold_chartedSpace hk hW
  have h := (hball v hv).2
  rw [sub_zero] at h
  rw [val_targetPatch_toManifold hk hW _ _ h, add_zero]

/-- Every point of the coordinate neighbourhood is the image of a parameter in the ball. -/
theorem exists_targetPatch_eq_of_mem_coordNbhd (y : V.carrier) {r : ℝ}
    (hball : ∀ v ∈ Metric.ball (0 : ComplexModel V.dim) r,
      v ∈ (patchAt hW y).parameterDomain ∧
        (letI := chartedSpace hk hW
        haveI := isComplexManifold_chartedSpace hk hW
        v - 0 ∈ (targetPatch hk hW (patchAt hW y)
          (RegularPatchNeighborhood.RegularPatch.zero_mem_parameterDomain _)).parameterDomain))
    {y' : V.carrier} (hy' : y' ∈ coordNbhd hW y r) :
    letI := chartedSpace hk hW
    haveI := isComplexManifold_chartedSpace hk hW
    ∃ v ∈ Metric.ball (0 : ComplexModel V.dim) r,
      (targetPatch hk hW (patchAt hW y)
        (RegularPatchNeighborhood.RegularPatch.zero_mem_parameterDomain _)).toManifold v = y' := by
  let := chartedSpace hk hW
  have := isComplexManifold_chartedSpace hk hW
  refine ⟨(patchFlatData (patchAt hW y)).toCoord y', hy'.2, Subtype.ext ?_⟩
  rw [val_targetPatch_patchAt hk hW y hball hy'.2, ← patchFlatData_ofCoord,
    (patchFlatData (patchAt hW y)).ofCoord_toCoord y' hy'.1]

/-- Points of `↥V` in some member of a finite family of sets lie in the first member that contains
them, and not in any earlier one. -/
theorem exists_mem_first {m : ℕ} (N : Fin m → Set V.carrier) {y : V.carrier}
    (hy : ∃ i, y ∈ N i) : ∃ i, y ∈ N i ∧ ∀ j < i, y ∉ N j := by
  classical
  obtain ⟨i, hi⟩ := hy
  have hne : (Finset.univ.filter fun j => y ∈ N j).Nonempty := ⟨i, by simpa using hi⟩
  refine ⟨(Finset.univ.filter fun j => y ∈ N j).min' hne, ?_, fun j hj hyj => ?_⟩
  · simpa using (Finset.univ.filter fun j => y ∈ N j).min'_mem hne
  · exact (not_le.mpr hj) (Finset.min'_le _ j (by simpa using hyj))

variable {omega : KahlerBackground n X} {alpha : RealBottChern n X} {ε : PositiveError}

/-- **The non-pluripolar mass on `V` of the restriction is at most the restricted absolutely
continuous mass.**  Finitely many coordinate neighbourhoods cover the compact `↥V`; their
disjointified parameter pieces, with the poles removed, form one regular-piece family of `V`
whose density integrals add up to the non-pluripolar mass of `↥V` minus the poles. -/
theorem diagonalPotentialMass_restrict_le_acTopMass [CompactSpace X] (hV : IsClosed V.carrier)
    (p : AdmissibleRestrictedCurrentPresentation omega alpha V ε) :
    letI := chartedSpace hk hW
    haveI := isComplexManifold_chartedSpace hk hW
    letI : MeasurableSpace V.carrier := borel _
    haveI : BorelSpace V.carrier := ⟨rfl⟩
    haveI : CompactSpace V.carrier := SubmanifoldMassCalculus.compactSpace_of_isClosed hV
    DiagonalMass.diagonalPotentialMass
      (ClosedRealOneOneForm.pullback (contMDiff_val hk hW) p.representative +
        (ε : ℝ) • (SubmanifoldKahlerRestriction.kahlerBackground hk hW omega).form)
      (fun y : V.carrier => p.potential y.1) (restrictPresentation hk hW p).potential_psh ≤
      acTopMass p := by
  classical
  let := chartedSpace hk hW
  have := isComplexManifold_chartedSpace hk hW
  let : MeasurableSpace V.carrier := borel _
  have : BorelSpace V.carrier := ⟨rfl⟩
  have : CompactSpace V.carrier := SubmanifoldMassCalculus.compactSpace_of_isClosed hV
  set q := restrictPresentation hk hW p with hq
  set μ : Measure V.carrier := globalMixedMeasure (fun _ : Fin V.dim => perturbedRepresentative q)
    (fun _ => q.potential) (fun _ => q.potential_psh.1) with hμ
  change μ univ ≤ acTopMass p
  -- the patch at each point, and a ball on which its target patch is defined
  have h0 : ∀ y : V.carrier, (0 : ComplexModel V.dim) ∈ (patchAt hW y).parameterDomain :=
    fun y => RegularPatchNeighborhood.RegularPatch.zero_mem_parameterDomain _
  have hrad := fun y : V.carrier => exists_ball_targetPatch hk hW (patchAt hW y) (h0 y)
  choose r hr hball using hrad
  set T : V.carrier → RegularPatch (DominationBigRestriction.univSubvariety (k := V.dim)
    (Z := V.carrier)) := fun y => targetPatch hk hW (patchAt hW y) (h0 y) with hT
  -- a finite subcover of `↥V` by coordinate neighbourhoods
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun y => coordNbhd hW y (r y))
    (fun y => isOpen_coordNbhd hW y (r y))
    (fun y _ => mem_iUnion.mpr ⟨y, mem_coordNbhd_self hW y (hr y)⟩)
  set m := t.card with hm
  set c : Fin m → V.carrier := fun i => (t.equivFin.symm i : V.carrier) with hc
  set N : Fin m → Set V.carrier := fun i => coordNbhd hW (c i) (r (c i)) with hN
  have hcover : ∀ y : V.carrier, ∃ i, y ∈ N i := by
    intro y
    obtain ⟨z, hzt, hyz⟩ := mem_iUnion₂.mp (ht (mem_univ y))
    refine ⟨t.equivFin ⟨z, hzt⟩, ?_⟩
    simp only [hN, hc, Equiv.symm_apply_apply]
    exact hyz
  -- the pole set, the disjointified pieces of `↥V`
  set P : Set V.carrier := {y | q.potential y = ⊥} with hP
  have hPmeas : MeasurableSet P := by
    have husc : UpperSemicontinuous q.potential :=
      ShiftedRooftopLimit.IsGlobalQuasiPshPotential.upperSemicontinuous
        ⟨q.potential_psh.1.quasiPlurisubharmonic, q.potential_psh.2⟩
    exact husc.measurable (measurableSet_singleton ⊥)
  set B : Fin m → Set V.carrier := fun i => (N i \ ⋃ j ∈ Finset.univ.filter (· < i), N j) ∩ Pᶜ
    with hB
  have hBmeas : ∀ i, MeasurableSet (B i) := fun i =>
    (((isOpen_coordNbhd hW _ _).measurableSet).diff
      (Finset.measurableSet_biUnion _ fun j _ => (isOpen_coordNbhd hW _ _).measurableSet)).inter
      hPmeas.compl
  have hBdisj : Pairwise (Function.onFun Disjoint B) := by
    intro i j hij
    refine disjoint_left.mpr fun y hyi hyj => ?_
    rcases lt_or_gt_of_ne hij with h | h
    · exact hyj.1.2 (mem_iUnion₂.mpr ⟨i, by simpa using h, hyi.1.1⟩)
    · exact hyi.1.2 (mem_iUnion₂.mpr ⟨j, by simpa using h, hyj.1.1⟩)
  have hBunion : (⋃ i, B i) = Pᶜ := by
    refine subset_antisymm (iUnion_subset fun i => inter_subset_right) fun y hy => ?_
    obtain ⟨i, hyi, hfirst⟩ := exists_mem_first N (hcover y)
    refine mem_iUnion.mpr ⟨i, ⟨hyi, fun hy' => ?_⟩, hy⟩
    obtain ⟨j, hj, hyj⟩ := mem_iUnion₂.mp hy'
    exact hfirst j (by simpa using hj) hyj
  -- parameter pieces
  set S : Fin m → Set (ComplexModel V.dim) := fun i =>
    Metric.ball (0 : ComplexModel V.dim) (r (c i)) ∩ (T (c i)).toManifold ⁻¹' B i with hS
  have hTmem : ∀ i, ∀ v ∈ Metric.ball (0 : ComplexModel V.dim) (r (c i)),
      v ∈ (T (c i)).parameterDomain := fun i v hv => by
    simpa only [sub_zero] using (hball (c i) v hv).2
  have hSmeas : ∀ i, MeasurableSet (S i) := by
    intro i
    have hcont : ContinuousOn (T (c i)).toManifold
        (Metric.ball (0 : ComplexModel V.dim) (r (c i))) :=
      (RegularPatchNeighborhood.RegularPatch.continuousOn_toManifold (T (c i))).mono
        fun v hv => hTmem i v hv
    have hmeas := (continuousOn_iff_continuous_domRestrict.mp hcont).measurable (hBmeas i)
    have himg := MeasurableSet.subtype_image (Metric.isOpen_ball.measurableSet) hmeas
    rwa [Set.domRestrict_eq, preimage_comp, Subtype.image_preimage_coe] at himg
  have hval : ∀ i, ∀ v ∈ S i, (((T (c i)).toManifold v : V.carrier) : X) =
      (patchAt hW (c i)).toManifold v := fun i v hv =>
    val_targetPatch_patchAt hk hW (c i) (hball (c i)) hv.1
  have himage : ∀ i, (T (c i)).toManifold '' S i = B i := by
    intro i
    refine subset_antisymm (by rintro _ ⟨v, hv, rfl⟩; exact hv.2) fun y hy => ?_
    obtain ⟨v, hv, hvy⟩ := exists_targetPatch_eq_of_mem_coordNbhd hk hW (c i) (hball (c i)) hy.1.1
    exact ⟨v, ⟨hv, by
      change (T (c i)).toManifold v ∈ B i
      rw [hT]; simp only; rw [hvy]; exact hy⟩, hvy⟩
  have himageX : ∀ i, (patchAt hW (c i)).toManifold '' S i = Subtype.val '' B i := by
    intro i
    rw [← himage i]
    ext x
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact ⟨_, ⟨v, hv, rfl⟩, hval i v hv⟩
    · rintro ⟨_, ⟨v, hv, rfl⟩, rfl⟩
      exact ⟨v, hv, (hval i v hv).symm⟩
  -- the regular-piece family of `V`
  let F : RegularPieceFamily V (poleSet p.potential) :=
    { size := m
      patch := fun i => patchAt hW (c i)
      piece := S
      measurableSet_piece := hSmeas
      piece_subset := fun i v hv => (hball (c i) v hv.1).1
      image_subset_regularLocus := fun i => by
        rintro _ ⟨v, hv, rfl⟩
        exact RegularPatchNeighborhood.RegularPatch.toManifold_mem_regularLocus _
          (hball (c i) v hv.1).1
      image_disjoint_avoid := fun i => by
        rw [himageX i]
        refine disjoint_left.mpr ?_
        rintro _ ⟨y, hy, rfl⟩ hpole
        exact hy.2 hpole
      pairwise_disjoint_image := fun i j hij => by
        dsimp only
        rw [himageX i, himageX j]
        exact (disjoint_image_iff Subtype.val_injective).mpr (hBdisj hij) }
  -- each piece integral is the non-pluripolar measure of its piece of `↥V`
  have hpiece : ∀ i, ∫⁻ w in S i, ENNReal.ofReal (patchDensity p (patchAt hW (c i)) w) =
      μ (B i) := by
    intro i
    have hcongr : ∫⁻ w in S i, ENNReal.ofReal (patchDensity p (patchAt hW (c i)) w) =
        ∫⁻ w in S i, ENNReal.ofReal (patchDensity q (T (c i)) w) := by
      refine setLIntegral_congr_fun (hSmeas i) fun v hv => ?_
      have hpole : (patchAt hW (c i)).toManifold (v + 0) ∉ poleSet p.potential := by
        rw [add_zero, ← hval i v hv]
        exact hv.2.2
      have h := patchDensity_targetPatch hk hW p (patchAt hW (c i)) (h0 (c i))
        (hTmem i v hv.1) hpole
      rw [add_zero] at h
      rw [← h]
    have hloc := FullSpaceAmbientComparison.lintegral_patchDensity_eq_globalMixedMeasure_image
      (V := DominationBigRestriction.univSubvariety (k := V.dim) (Z := V.carrier)) rfl rfl q
      (T (c i)) (hSmeas i) (fun v hv => hTmem i v hv.1)
      (by
        rintro _ ⟨v, hv, rfl⟩
        exact RegularPatchNeighborhood.RegularPatch.toManifold_mem_regularLocus _
          (hTmem i v hv.1))
      (by
        rw [himage i]
        refine disjoint_left.mpr fun y hy hpole => hy.2 hpole)
    calc _ = _ := hcongr
      _ = μ ((T (c i)).toManifold '' S i) := hloc.2
      _ = μ (B i) := by rw [himage i]
  -- assembly
  have hPnull : μ P = 0 :=
    GlobalDiagonalScaling.globalMixedMeasure_pole_null_of_nondegenerate _ q.potential_psh
  have hsum : μ Pᶜ = ∑ i, ∫⁻ w in F.piece i, ENNReal.ofReal (patchDensity p (F.patch i) w) := by
    rw [← hBunion, measure_iUnion hBdisj hBmeas, tsum_fintype]
    exact Finset.sum_congr rfl fun i _ => (hpiece i).symm
  calc μ univ ≤ μ Pᶜ + μ P := by
        rw [← union_compl_self P, union_comm]
        exact measure_union_le _ _
    _ = μ Pᶜ := by rw [hPnull, add_zero]
    _ ≤ acTopMass p := by
        rw [hsum]
        exact le_iSup (fun G : RegularPieceFamily V (poleSet p.potential) =>
          ∑ i, ∫⁻ w in G.piece i, ENNReal.ofReal (patchDensity p (G.patch i) w)) F

/-- **`ana:mass-calculus`, second sentence.**  For an admissible presentation along a closed
submanifold `V`, the absolutely continuous restricted top mass equals the non-pluripolar top mass on
`V` of the restriction: `∫_V ((T + εω)|_V)_ac^k = ∫_V ⟨((T + εω)|_V)^k⟩`. -/
theorem acTopMass_eq_diagonalPotentialMass_restrict [CompactSpace X] (hV : IsClosed V.carrier)
    (p : AdmissibleRestrictedCurrentPresentation omega alpha V ε) :
    letI := chartedSpace hk hW
    haveI := isComplexManifold_chartedSpace hk hW
    letI : MeasurableSpace V.carrier := borel _
    haveI : BorelSpace V.carrier := ⟨rfl⟩
    haveI : CompactSpace V.carrier := SubmanifoldMassCalculus.compactSpace_of_isClosed hV
    acTopMass p = DiagonalMass.diagonalPotentialMass
      (ClosedRealOneOneForm.pullback (contMDiff_val hk hW) p.representative +
        (ε : ℝ) • (SubmanifoldKahlerRestriction.kahlerBackground hk hW omega).form)
      (fun y : V.carrier => p.potential y.1) (restrictPresentation hk hW p).potential_psh :=
  le_antisymm (SubmanifoldACTopMass.acTopMass_le_diagonalPotentialMass_restrict hk hW hV p)
    (diagonalPotentialMass_restrict_le_acTopMass hk hW hV p)

omit [ConnectedSpace V.carrier] [Nonempty V.carrier] in
/-- `↥V` is connected: an irreducible analytic set is connected. -/
theorem connectedSpace_carrier : ConnectedSpace V.carrier :=
  Subtype.connectedSpace ⟨V.irreducible_carrier.nonempty,
    CodimOneSupport.isPreconnected_of_isComplexAnalyticallyIrreducible V.irreducible_carrier⟩

omit [ConnectedSpace V.carrier] [Nonempty V.carrier] in
/-- **`ana:mass-calculus`, second sentence, with no extra instance**: the connectedness and
nonemptiness of `↥V` that the restricted presentation uses come from the irreducibility of `V`. -/
theorem acTopMass_eq_diagonalPotentialMass_restrict' [CompactSpace X]
    (p : AdmissibleRestrictedCurrentPresentation omega alpha V ε) :
    letI := chartedSpace hk hW
    haveI := isComplexManifold_chartedSpace hk hW
    letI : MeasurableSpace V.carrier := borel _
    haveI : BorelSpace V.carrier := ⟨rfl⟩
    haveI : CompactSpace V.carrier :=
      SubmanifoldMassCalculus.compactSpace_of_isClosed V.isClosed_carrier
    haveI : ConnectedSpace V.carrier := connectedSpace_carrier
    haveI : Nonempty V.carrier := V.irreducible_carrier.nonempty.to_subtype
    acTopMass p = DiagonalMass.diagonalPotentialMass
      (ClosedRealOneOneForm.pullback (contMDiff_val hk hW) p.representative +
        (ε : ℝ) • (SubmanifoldKahlerRestriction.kahlerBackground hk hW omega).form)
      (fun y : V.carrier => p.potential y.1) (restrictPresentation hk hW p).potential_psh :=
  haveI : ConnectedSpace V.carrier := connectedSpace_carrier
  haveI : Nonempty V.carrier := V.irreducible_carrier.nonempty.to_subtype
  acTopMass_eq_diagonalPotentialMass_restrict hk hW V.isClosed_carrier p

end

end SGPT.Foundations.Analysis.Pending.RestrictedMassEquality
