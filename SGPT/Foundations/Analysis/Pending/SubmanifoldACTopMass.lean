import SGPT.Foundations.Analysis.Pending.SubmanifoldRestrictedPresentation
import SGPT.Foundations.Analysis.Pending.FullSpaceAmbientComparison

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The restricted absolutely continuous mass along `V` is a non-pluripolar mass on `V`

Route F, `F-b` step P1 (plan §8 of `scratch/tn23-envelopes-qea-plan-0117.md`; blueprint
`pc:f-restricted-volume-le`, "its restriction has smooth analytic singularities, so the absolutely
continuous integral of `(T + εω)|_V` is its non-pluripolar mass").  For an admissible presentation
`p` of a class along a closed connected submanifold `V` (`dim V = k`):

* `acTopMass_le_restrictPresentation`: `acTopMass p ≤ acTopMass (p|_V)` — every finite regular-piece
  family of `V ⊆ X` is transported to one of the whole complex manifold `↥V`: each piece is covered by
  countably many parameter balls on which `SubmanifoldPatchTransport.targetPatch` is defined, the
  balls are disjointified, translated to the origin, and the densities agree
  (`SubmanifoldRestrictedPresentation.patchDensity_targetPatch`).  The measure-theoretic skeleton is
  the one of `RestrictedVolumePushforwardMass.acTopMass_le_of_patchDensity_le_general` (with no
  exceptional set; the inclusion `↥V → X` is injective).
* `acTopMass_le_diagonalPotentialMass_restrict`: hence, by the full-space comparison on `↥V`
  (`FullSpaceAmbientComparison.acTopMass_le_perturbedDiagonalPotentialMass`),
  `acTopMass p ≤ ∫_V ⟨(θ_p|_V + εω_V)_{u_p|_V}^k⟩`.

Sorry-free.
-/

open Set Filter MeasureTheory
open scoped Topology Manifold ContDiff ENNReal

universe u

namespace SGPT.Foundations.Analysis.Pending.SubmanifoldACTopMass

noncomputable section

open FirstPass FirstPass.PositiveClasses FirstPass.NumericalRestrictedVolumeScaffold
  FirstPass.NumericalRestrictedVolume SubmanifoldChartedSpace SubmanifoldPatchTransport
  SubmanifoldRestrictedPresentation

variable {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] {V : ClosedIrreducibleAnalyticSubvariety n X}

variable (hk : V.dim ≤ n) (hW : ∀ x ∈ V.carrier, RegularAtDim (n := n) V.carrier x V.dim)
  [ConnectedSpace V.carrier] [Nonempty V.carrier]
  {omega : KahlerBackground n X} {alpha : RealBottChern n X} {ε : PositiveError}

/-- **The restricted mass along `V` is at most the restricted mass of the whole of `↥V`** for the
restricted presentation. -/
theorem acTopMass_le_restrictPresentation
    (p : AdmissibleRestrictedCurrentPresentation omega alpha V ε) :
    letI := chartedSpace hk hW
    haveI := isComplexManifold_chartedSpace hk hW
    acTopMass p ≤ acTopMass (restrictPresentation hk hW p) := by
  classical
  let := chartedSpace hk hW
  have := isComplexManifold_chartedSpace hk hW
  set Vt := DominationBigRestriction.univSubvariety (k := V.dim) (Z := V.carrier) with hVt
  -- local transport data at every parameter
  have hloc : ∀ (P : RegularPatch V) (v₀ : ComplexModel V.dim), v₀ ∈ P.parameterDomain →
      ∃ (P' : RegularPatch Vt) (r : ℝ), 0 < r ∧ ∀ v : ComplexModel V.dim, v ∈ Metric.ball v₀ r →
        v ∈ P.parameterDomain ∧ v - v₀ ∈ P'.parameterDomain ∧
        ((P'.toManifold (v - v₀) : V.carrier) : X) = P.toManifold v ∧
        (P.toManifold v ∉ poleSet p.potential →
          patchDensity (restrictPresentation hk hW p) P' (v - v₀) = patchDensity p P v) := by
    intro P v₀ hv₀
    obtain ⟨r, hr, hball⟩ := exists_ball_targetPatch hk hW P hv₀
    refine ⟨targetPatch hk hW P hv₀, r, hr, fun v hv => ?_⟩
    obtain ⟨hvP, hvT⟩ := hball v hv
    refine ⟨hvP, hvT, ?_, fun hpole => ?_⟩
    · rw [val_targetPatch_toManifold hk hW P hv₀ hvT, sub_add_cancel]
    · have h := patchDensity_targetPatch hk hW p P hv₀ hvT (by rwa [sub_add_cancel])
      rwa [sub_add_cancel] at h
  have : Nonempty (RegularPatch Vt) := RestrictedVolumePullbackLower.nonempty_regularPatch Vt
  choose! Pf rf hrf hPf using hloc
  refine iSup_le fun F => ?_
  set Qp : Fin F.size → RegularPatch V := F.patch with hQp
  set R : Fin F.size → ComplexModel V.dim → ℝ :=
    fun i v₀ => if v₀ ∈ F.piece i then rf (Qp i) v₀ else 0 with hRdef
  have hcover : ∀ i, ∃ c : ℕ → ComplexModel V.dim,
      F.piece i ⊆ ⋃ j, Metric.ball (c j) (R i (c j)) := by
    intro i
    obtain ⟨T, hTc, hT⟩ := TopologicalSpace.isOpen_iUnion_countable
      (fun v₀ => Metric.ball v₀ (R i v₀)) (fun _ => Metric.isOpen_ball)
    obtain ⟨c, hc⟩ := (hTc.insert 0).exists_eq_range (insert_nonempty _ _)
    refine ⟨c, fun v hv => ?_⟩
    have hmem : v ∈ ⋃ v₀, Metric.ball v₀ (R i v₀) := by
      refine mem_iUnion.mpr ⟨v, Metric.mem_ball_self ?_⟩
      simp only [hRdef, if_pos hv]
      exact hrf (Qp i) v (F.piece_subset i hv)
    rw [← hT] at hmem
    obtain ⟨v₀, hv₀T, hv⟩ := mem_iUnion₂.mp hmem
    have : v₀ ∈ range c := hc ▸ mem_insert_of_mem _ hv₀T
    obtain ⟨j, rfl⟩ := this
    exact mem_iUnion.mpr ⟨j, hv⟩
  choose c hc using hcover
  set D : Fin F.size → ℕ → Set (ComplexModel V.dim) := fun i j =>
    F.piece i ∩ disjointed (fun j => Metric.ball (c i j) (R i (c i j))) j with hDdef
  have hDmeas : ∀ i j, MeasurableSet (D i j) := fun i j =>
    (F.measurableSet_piece i).inter
      (MeasurableSet.disjointed (fun _ => Metric.isOpen_ball.measurableSet) j)
  have hDdisj : ∀ i, Pairwise (Function.onFun Disjoint (D i)) := fun i j j' hjj' =>
    ((disjoint_disjointed _ hjj').mono inter_subset_right inter_subset_right)
  have hDgood : ∀ i j, ∀ v ∈ D i j, c i j ∈ F.piece i ∧ v ∈ F.piece i ∧
      v ∈ Metric.ball (c i j) (rf (Qp i) (c i j)) := by
    intro i j v hv
    have hvb : v ∈ Metric.ball (c i j) (R i (c i j)) :=
      disjointed_le (fun j => Metric.ball (c i j) (R i (c i j))) j hv.2
    by_cases hcG : c i j ∈ F.piece i
    · refine ⟨hcG, hv.1, ?_⟩
      simpa only [hRdef, if_pos hcG] using hvb
    · simp only [hRdef, if_neg hcG, Metric.ball_zero, mem_empty_iff_false] at hvb
  set f : Fin F.size → ComplexModel V.dim → ℝ≥0∞ := fun i v =>
    ENNReal.ofReal (patchDensity p (Qp i) v) with hfdef
  set a : Fin F.size → ℕ → ℝ≥0∞ := fun i j => ∫⁻ v in D i j, f i v with hadef
  have hpiece : ∀ i, ∫⁻ v in F.piece i, f i v ≤ ⨆ N, ∑ j ∈ Finset.range N, a i j := by
    intro i
    have hsub : F.piece i ⊆ ⋃ j, D i j := by
      intro v hv
      have : v ∈ ⋃ j, disjointed (fun j => Metric.ball (c i j) (R i (c i j))) j := by
        rw [iUnion_disjointed]
        exact hc i hv
      obtain ⟨j, hj⟩ := mem_iUnion.mp this
      exact mem_iUnion.mpr ⟨j, hv, hj⟩
    calc ∫⁻ v in F.piece i, f i v
        ≤ ∫⁻ v in ⋃ j, D i j, f i v := lintegral_mono_set hsub
      _ = ∑' j, a i j := lintegral_iUnion (hDmeas i) (hDdisj i) _
      _ = ⨆ N, ∑ j ∈ Finset.range N, a i j := ENNReal.tsum_eq_iSup_nat
  refine (Finset.sum_le_sum fun i _ => hpiece i).trans ?_
  rw [ENNReal.finsetSum_iSup_of_monotone fun i N N' hNN' =>
    Finset.sum_le_sum_of_subset (Finset.range_mono hNN')]
  refine iSup_le fun N => ?_
  set e : Fin F.size × Fin N ≃ Fin (F.size * N) := finProdFinEquiv with he
  have hmapsP : ∀ i (j : ℕ), ∀ v ∈ D i j,
      v - c i j ∈ (Pf (Qp i) (c i j)).parameterDomain ∧
      (((Pf (Qp i) (c i j)).toManifold (v - c i j) : V.carrier) : X) = (Qp i).toManifold v ∧
      patchDensity (restrictPresentation hk hW p) (Pf (Qp i) (c i j)) (v - c i j) =
        patchDensity p (Qp i) v := by
    intro i j v hv
    obtain ⟨hcG, hvG, hvb⟩ := hDgood i j v hv
    obtain ⟨-, h1, h2, h3⟩ := hPf (Qp i) (c i j) (F.piece_subset i hcG) v hvb
    refine ⟨h1, h2, h3 fun hpv => ?_⟩
    exact disjoint_left.mp (F.image_disjoint_avoid i) ⟨v, hvG, rfl⟩ hpv
  have hmapsP' : ∀ i (j : ℕ) (v' : ComplexModel V.dim), v' + c i j ∈ D i j →
      v' ∈ (Pf (Qp i) (c i j)).parameterDomain ∧
      (((Pf (Qp i) (c i j)).toManifold v' : V.carrier) : X) = (Qp i).toManifold (v' + c i j) := by
    intro i j v' hv'
    have h := hmapsP i j _ hv'
    rw [add_sub_cancel_right] at h
    exact ⟨h.1, h.2.1⟩
  let Fy : RegularPieceFamily Vt (poleSet (restrictPresentation hk hW p).potential) :=
    { size := F.size * N
      patch := fun k => Pf (Qp (e.symm k).1) (c (e.symm k).1 (e.symm k).2)
      piece := fun k => (fun v' : ComplexModel V.dim => v' + c (e.symm k).1 (e.symm k).2) ⁻¹'
        D (e.symm k).1 (e.symm k).2
      measurableSet_piece := fun k => (hDmeas _ _).preimage
        ((continuous_add_const (c (e.symm k).1 (e.symm k).2)).measurable :
          Measurable fun v' : ComplexModel V.dim => v' + c (e.symm k).1 (e.symm k).2)
      piece_subset := fun k v' hv' => (hmapsP' _ _ v' hv').1
      image_subset_regularLocus := fun k => by
        rintro _ ⟨v', hv', rfl⟩
        exact RegularPatchNeighborhood.RegularPatch.toManifold_mem_regularLocus _
          (hmapsP' _ _ v' hv').1
      image_disjoint_avoid := fun k => by
        refine disjoint_left.mpr ?_
        rintro _ ⟨v', hv', rfl⟩ hpole'
        obtain ⟨-, hvG, -⟩ := hDgood _ _ _ hv'
        have hq' : p.potential
            (((Pf (Qp (e.symm k).1) (c (e.symm k).1 (e.symm k).2)).toManifold v' : V.carrier) :
              X) = ⊥ := hpole'
        rw [(hmapsP' _ _ v' hv').2] at hq'
        exact disjoint_left.mp (F.image_disjoint_avoid _) ⟨_, hvG, rfl⟩ hq'
      pairwise_disjoint_image := fun k k' hkk' => by
        obtain ⟨⟨i, j⟩, rfl⟩ := e.surjective k
        obtain ⟨⟨i', j'⟩, rfl⟩ := e.surjective k'
        have hne : (i, j) ≠ (i', j') := fun h => hkk' (congrArg e h)
        simp only [Equiv.symm_apply_apply]
        refine disjoint_left.mpr ?_
        rintro _ ⟨(v₁ : ComplexModel V.dim), hv₁, rfl⟩ ⟨(v₂ : ComplexModel V.dim), hv₂, heq⟩
        have hv₁' : v₁ + c i j ∈ D i j := hv₁
        have hv₂' : v₂ + c i' j' ∈ D i' j' := hv₂
        obtain ⟨-, hG₁, -⟩ := hDgood i j _ hv₁'
        obtain ⟨-, hG₂, -⟩ := hDgood i' j' _ hv₂'
        have g₁ := (hmapsP' i j v₁ hv₁').2
        have g₂ := (hmapsP' i' j' v₂ hv₂').2
        have hup : (Qp i').toManifold (v₂ + c i' j') = (Qp i).toManifold (v₁ + c i j) := by
          have h := congrArg Subtype.val heq
          rw [← g₁, ← g₂]
          exact h
        by_cases hi : i' = i
        · subst hi
          have hjj : (j : ℕ) ≠ j' := fun h => hne (Prod.ext rfl (Fin.ext h))
          have hw := RestrictedVolumePullbackLower.toManifold_injOn (Qp i')
            (F.piece_subset i' hG₂) (F.piece_subset i' hG₁) hup
          have h₂ : v₁ + c i' j ∈ D i' j' := by rw [← hw]; exact hv₂'
          exact disjoint_left.mp (hDdisj i' hjj) hv₁' h₂
        · exact disjoint_left.mp (F.pairwise_disjoint_image hi) ⟨_, hG₂, hup⟩ ⟨_, hG₁, rfl⟩ }
  have hle : (∑ k, ∫⁻ w in Fy.piece k,
      ENNReal.ofReal (patchDensity (restrictPresentation hk hW p) (Fy.patch k) w)) ≤
      acTopMass (restrictPresentation hk hW p) :=
    le_iSup (fun G : RegularPieceFamily Vt (poleSet (restrictPresentation hk hW p).potential) =>
      ∑ k, ∫⁻ w in G.piece k,
        ENNReal.ofReal (patchDensity (restrictPresentation hk hW p) (G.patch k) w)) Fy
  refine le_trans ?_ hle
  calc ∑ i, ∑ j ∈ Finset.range N, a i j
      = ∑ x : Fin F.size × Fin N, a x.1 x.2 := by
        rw [Fintype.sum_prod_type]
        exact Finset.sum_congr rfl fun i _ => (Fin.sum_univ_eq_sum_range (a i) N).symm
    _ = ∑ k : Fin (F.size * N), a (e.symm k).1 (e.symm k).2 :=
        (e.symm.sum_comp fun x => a x.1 x.2).symm
    _ ≤ ∑ k : Fin (F.size * N), ∫⁻ w in Fy.piece k,
          ENNReal.ofReal (patchDensity (restrictPresentation hk hW p) (Fy.patch k) w) := by
        refine Finset.sum_le_sum fun k _ => ?_
        set i := (e.symm k).1
        set j : ℕ := ((e.symm k).2 : ℕ)
        have htr := (measurePreserving_add_right (volume : Measure (ComplexModel V.dim))
          (c i j)).setLIntegral_comp_preimage_emb
          (Homeomorph.addRight (c i j)).measurableEmbedding
          (fun v => ENNReal.ofReal
            (patchDensity (restrictPresentation hk hW p) (Pf (Qp i) (c i j)) (v - c i j))) (D i j)
        simp only [add_sub_cancel_right] at htr
        change ∫⁻ v in D i j, f i v ≤ ∫⁻ v' in (fun v' => v' + c i j) ⁻¹' D i j,
          ENNReal.ofReal (patchDensity (restrictPresentation hk hW p) (Pf (Qp i) (c i j)) v')
        rw [htr]
        refine le_of_eq (setLIntegral_congr_fun (hDmeas i j) fun v hv => ?_)
        rw [(hmapsP i j v hv).2.2]

/-- **The restricted mass along `V` is at most the non-pluripolar mass on `V` of the restriction**:
`acTopMass p ≤ ∫_V ⟨(θ_p|_V + εω_V)_{u_p|_V}^k⟩`. -/
theorem acTopMass_le_diagonalPotentialMass_restrict [CompactSpace X] (hV : IsClosed V.carrier)
    (p : AdmissibleRestrictedCurrentPresentation omega alpha V ε) :
    letI := chartedSpace hk hW
    haveI := isComplexManifold_chartedSpace hk hW
    letI : MeasurableSpace V.carrier := borel _
    haveI : BorelSpace V.carrier := ⟨rfl⟩
    haveI : CompactSpace V.carrier := SubmanifoldMassCalculus.compactSpace_of_isClosed hV
    acTopMass p ≤ DiagonalMass.diagonalPotentialMass
      (ClosedRealOneOneForm.pullback (contMDiff_val hk hW) p.representative +
        (ε : ℝ) • (SubmanifoldKahlerRestriction.kahlerBackground hk hW omega).form)
      (fun y : V.carrier => p.potential y.1) (restrictPresentation hk hW p).potential_psh := by
  let := chartedSpace hk hW
  have := isComplexManifold_chartedSpace hk hW
  let : MeasurableSpace V.carrier := borel _
  have : BorelSpace V.carrier := ⟨rfl⟩
  have : CompactSpace V.carrier := SubmanifoldMassCalculus.compactSpace_of_isClosed hV
  exact (acTopMass_le_restrictPresentation hk hW p).trans
    (FullSpaceAmbientComparison.acTopMass_le_perturbedDiagonalPotentialMass rfl rfl _)

end

end SGPT.Foundations.Analysis.Pending.SubmanifoldACTopMass
