import SGPT.Foundations.Analysis.Pending.RegularPieceExhaustion
import SGPT.Foundations.Analysis.Pending.CoordinateDensityMixedPullback
import SGPT.Foundations.Analysis.Pending.CoordinateWedgeFamilyPairing
import SGPT.Foundations.Analysis.Pending.RegularPatchDensityContinuity

set_option autoImplicit false

/-!
# A countable decomposition of `V_reg`, and integrals over `V_reg`

Blueprint `ana:stokes-regular-decomposition` (TN.4 #4, Stokes against `[V]`, part B of
Stokes' theorem on the regular locus).

* `RegularDecomposition V`: regular patches `γⱼ` and measurable parameter pieces `Eⱼ`
  (`j ∈ ℕ`) whose images are pairwise disjoint and absorb every compact subset of `V_reg`
  (`nonempty_regularDecomposition`, by Lindelöf from `RegularPieceExhaustion.exists_localPatchData`:
  `Eⱼ = {w ∈ Ωⱼ : γⱼ w ∈ Uⱼ \ ⋃_{i<j} Uᵢ}`).  The first `N` pieces form a regular-piece family
  `partialFamily N`, and these exhaust `V_reg`.
* `iSup_formPieceMass_eq_tsum`: the regular-piece supremum of any smooth two-form is the series
  `∑ⱼ ∫_{Eⱼ} ρ_{γⱼ}(a)`.
* `measure`: the measure on `ℕ × ℂ^k` with `∫ F = ∑ⱼ ∫_{Eⱼ} F(j, ·)`.
-/

open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff

namespace SGPT.Foundations.Analysis.Pending.StokesRegularDecomposition

open FirstPass FirstPass.NumericalRestrictedVolume FirstPass.RegularPatchNeighborhood
open RegularPatchTransition PatchFormMass RegularPieceExhaustion

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- **A countable decomposition of the regular locus.**  Regular patches and measurable
parameter pieces with pairwise disjoint images, absorbing every compact subset of `V_reg` into
finitely many of them. -/
structure RegularDecomposition (V : ClosedIrreducibleAnalyticSubvariety n M) where
  patch : ℕ → RegularPatch V
  piece : ℕ → Set (ComplexModel V.dim)
  measurableSet_piece : ∀ j, MeasurableSet (piece j)
  piece_subset : ∀ j, piece j ⊆ (patch j).parameterDomain
  pairwise_disjoint : Pairwise fun i j =>
    Disjoint ((patch i).toManifold '' piece i) ((patch j).toManifold '' piece j)
  exhausts : ∀ K : Set M, IsCompact K → K ⊆ regularLocus (n := n) V.carrier V.dim →
    ∃ N, K ⊆ ⋃ j ∈ Finset.range N, (patch j).toManifold '' piece j

namespace RegularDecomposition

variable {V : ClosedIrreducibleAnalyticSubvariety n M} (D : RegularDecomposition V)

theorem image_subset_regularLocus (j : ℕ) :
    (D.patch j).toManifold '' D.piece j ⊆ regularLocus (n := n) V.carrier V.dim := by
  rintro _ ⟨w, hw, rfl⟩
  exact RegularPatch.toManifold_mem_regularLocus _ (D.piece_subset j hw)

/-- Every regular point lies in the image of some piece. -/
theorem exists_mem_image {y : M} (hy : y ∈ regularLocus (n := n) V.carrier V.dim) :
    ∃ j, ∃ w ∈ D.piece j, (D.patch j).toManifold w = y := by
  obtain ⟨N, hN⟩ := D.exhausts {y} isCompact_singleton (singleton_subset_iff.mpr hy)
  obtain ⟨j, -, w, hw, hwy⟩ := mem_iUnion₂.mp (hN rfl)
  exact ⟨j, w, hw, hwy⟩

/-- The first `N` pieces, as a regular-piece family. -/
def partialFamily (N : ℕ) : RegularPieceFamily V (∅ : Set M) where
  size := N
  patch i := D.patch i
  piece i := D.piece i
  measurableSet_piece i := D.measurableSet_piece i
  piece_subset i := D.piece_subset i
  image_subset_regularLocus i := D.image_subset_regularLocus i
  image_disjoint_avoid _ := disjoint_empty _
  pairwise_disjoint_image _ _ hij := D.pairwise_disjoint fun h => hij (Fin.ext h)

theorem coveredRegion_partialFamily (N : ℕ) :
    coveredRegion (D.partialFamily N) =
      ⋃ j ∈ Finset.range N, (D.patch j).toManifold '' D.piece j := by
  ext y
  simp only [coveredRegion, partialFamily, mem_iUnion, Finset.mem_range]
  constructor
  · rintro ⟨i, hi⟩; exact ⟨i, i.2, hi⟩
  · rintro ⟨j, hj, hy⟩; exact ⟨⟨j, hj⟩, hy⟩

theorem coveredRegion_partialFamily_mono (N : ℕ) :
    coveredRegion (D.partialFamily N) ⊆ coveredRegion (D.partialFamily (N + 1)) := by
  rw [coveredRegion_partialFamily, coveredRegion_partialFamily]
  exact biUnion_subset_biUnion_left fun j hj => by
    simp only [Finset.coe_range, mem_Iio] at hj ⊢; omega

theorem exhausts_partialFamily (K : Set M) (hK : IsCompact K)
    (hKreg : K ⊆ regularLocus (n := n) V.carrier V.dim) (_ : Disjoint K (∅ : Set M)) :
    ∃ N, K ⊆ coveredRegion (D.partialFamily N) := by
  obtain ⟨N, hN⟩ := D.exhausts K hK hKreg
  exact ⟨N, (D.coveredRegion_partialFamily N).symm ▸ hN⟩

/-- The mass of the first `N` pieces. -/
theorem formPieceMass_partialFamily (a : SmoothRealForm n M 2) (N : ℕ) :
    formPieceMass a (D.partialFamily N) =
      ∑ j ∈ Finset.range N, ∫⁻ w in D.piece j,
        ENNReal.ofReal (patchFormDensity a (D.patch j) w) := by
  rw [formPieceMass, ← Fin.sum_univ_eq_sum_range]
  rfl

/-- **The regular-piece supremum is the series over the decomposition.** -/
theorem iSup_formPieceMass_eq_tsum (a : SmoothRealForm n M 2) :
    (⨆ F : RegularPieceFamily V (∅ : Set M), formPieceMass a F) =
      ∑' j, ∫⁻ w in D.piece j, ENNReal.ofReal (patchFormDensity a (D.patch j) w) := by
  have h1 := tendsto_formPieceMass_of_exhaustion isClosed_empty
    (D.coveredRegion_partialFamily_mono) (D.exhausts_partialFamily) a
  have h2 := ENNReal.tendsto_nat_tsum fun j =>
    ∫⁻ w in D.piece j, ENNReal.ofReal (patchFormDensity a (D.patch j) w)
  simp only [formPieceMass_partialFamily] at h1
  exact tendsto_nhds_unique h1 h2

end RegularDecomposition

/-- **A countable decomposition of `V_reg` exists** (Lindelöf). -/
theorem nonempty_regularDecomposition (V : ClosedIrreducibleAnalyticSubvariety n M) :
    Nonempty (RegularDecomposition V) := by
  classical
  set R := regularLocus (n := n) V.carrier V.dim with hR
  have hloc : ∀ x : R, ∃ (P : RegularPatch V) (Ω : Set (ComplexModel V.dim)) (U : Set M),
      IsOpen Ω ∧ Ω ⊆ P.parameterDomain ∧ P.toManifold '' Ω ⊆ R ∧
        Disjoint (P.toManifold '' Ω) (∅ : Set M) ∧ IsOpen U ∧ (x : M) ∈ U ∧
          V.carrier ∩ U ⊆ P.toManifold '' Ω := fun x =>
    exists_localPatchData isClosed_empty x.2 (notMem_empty _)
  choose P Ω U hΩo hΩd _ _ hUo hxU hUV using hloc
  obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable U hUo
  have hmemT : ∀ y ∈ R, ∃ i ∈ T, y ∈ U i := fun y hy => by
    have : y ∈ ⋃ i ∈ T, U i := by rw [hTU]; exact mem_iUnion.2 ⟨⟨y, hy⟩, hxU _⟩
    obtain ⟨i, hiT, hyi⟩ := mem_iUnion₂.1 this
    exact ⟨i, hiT, hyi⟩
  have hTne : T.Nonempty := by
    obtain ⟨y, hy⟩ := V.regularLocus_nonempty
    obtain ⟨i, hiT, -⟩ := hmemT y hy
    exact ⟨i, hiT⟩
  obtain ⟨x, hx⟩ := hTc.exists_eq_range hTne
  have hcover : ∀ y ∈ R, ∃ j, y ∈ U (x j) := fun y hy => by
    obtain ⟨i, hiT, hyi⟩ := hmemT y hy
    rw [hx] at hiT
    obtain ⟨j, rfl⟩ := hiT
    exact ⟨j, hyi⟩
  set γ : ℕ → ComplexModel V.dim → M := fun j => (P (x j)).toManifold with hγ
  set W : ℕ → Set M := fun j => ⋃ i ∈ Finset.range j, U (x i) with hW
  set E : ℕ → Set (ComplexModel V.dim) := fun j =>
    (Ω (x j) ∩ γ j ⁻¹' U (x j)) \ (Ω (x j) ∩ γ j ⁻¹' W j) with hE
  have hcont : ∀ j, ContinuousOn (γ j) (Ω (x j)) := fun j =>
    (RegularPatch.continuousOn_toManifold _).mono (hΩd _)
  have hEsub : ∀ j, E j ⊆ Ω (x j) := fun j w hw => hw.1.1
  -- the image of a piece avoids the earlier open sets and lies in its own
  have hEU : ∀ j w, w ∈ E j → γ j w ∈ U (x j) := fun j w hw => hw.1.2
  have hEW : ∀ j w, w ∈ E j → γ j w ∉ W j := fun j w hw h => hw.2 ⟨hw.1.1, h⟩
  refine ⟨{ patch := fun j => P (x j)
            piece := E
            measurableSet_piece := fun j => ?_
            piece_subset := fun j => (hEsub j).trans (hΩd _)
            pairwise_disjoint := ?_
            exhausts := ?_ }⟩
  · exact ((hcont j).isOpen_inter_preimage (hΩo _) (hUo _)).measurableSet.diff
      ((hcont j).isOpen_inter_preimage (hΩo _)
        (isOpen_biUnion fun i _ => hUo _)).measurableSet
  · -- disjointness: a later piece avoids the open set of an earlier one
    have hlt : ∀ i j, i < j → Disjoint (γ i '' E i) (γ j '' E j) := by
      intro i j hij
      rw [Set.disjoint_left]
      rintro _ ⟨wi, hwi, rfl⟩ ⟨wj, hwj, hwij⟩
      refine hEW j wj hwj ?_
      rw [hwij]
      exact mem_iUnion₂.2 ⟨i, Finset.mem_range.2 hij, hEU i wi hwi⟩
    intro i j hij
    rcases lt_or_gt_of_ne hij with h | h
    · exact hlt i j h
    · exact (hlt j i h).symm
  · intro K hK hKR
    have hKU : K ⊆ ⋃ j, U (x j) := fun y hy => mem_iUnion.2 (hcover y (hKR hy))
    obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun j => U (x j)) (fun j => hUo _) hKU
    refine ⟨t.sup id + 1, fun y hy => ?_⟩
    have hex : ∃ j, y ∈ U (x j) := hcover y (hKR hy)
    set j0 := Nat.find hex with hj0
    have hyj0 : y ∈ U (x j0) := Nat.find_spec hex
    obtain ⟨j, hjt, hyj⟩ := mem_iUnion₂.1 (ht hy)
    have hj0le : j0 ≤ j := Nat.find_min' hex hyj
    have hjle : j ≤ t.sup id := Finset.le_sup (f := id) hjt
    obtain ⟨w, hwΩ, hwy⟩ := hUV (x j0) ⟨regularLocus_subset _ _ (hKR hy), hyj0⟩
    refine mem_iUnion₂.2 ⟨j0, Finset.mem_range.2 (by omega), w, ?_, hwy⟩
    refine ⟨⟨hwΩ, ?_⟩, fun h => ?_⟩
    · show γ j0 w ∈ U (x j0)
      rw [show γ j0 w = y from hwy]; exact hyj0
    · obtain ⟨i, hi, hyi⟩ := mem_iUnion₂.1 h.2
      have hlt : i < j0 := Finset.mem_range.1 hi
      exact Nat.find_min hex hlt (by rw [← show γ j0 w = y from hwy]; exact hyi)

/-! ### Density fields, and the transfer from the decomposition to one patch -/

theorem enorm_eq_ofReal_add_ofReal_neg (y : ℝ) :
    ‖y‖ₑ = ENNReal.ofReal y + ENNReal.ofReal (-y) := by
  rw [Real.enorm_eq_ofReal_abs]
  rcases le_total 0 y with h | h
  · rw [abs_of_nonneg h, ENNReal.ofReal_of_nonpos (neg_nonpos.mpr h), add_zero]
  · rw [abs_of_nonpos h, ENNReal.ofReal_of_nonpos h, zero_add]

section Transfer

variable {V : ClosedIrreducibleAnalyticSubvariety n M}

/-- **A density field**: a function on the parameters of every regular patch obeying the
transformation law of parameter densities, `Y_Q(w) = det_ℝ Dτ(w) · Y_P(τ w)` for the transition
`τ` from `Q` to `P`. -/
def IsDensityField (Y : RegularPatch V → ComplexModel V.dim → ℝ) : Prop :=
  ∀ (P Q : RegularPatch V) (w : ComplexModel V.dim), w ∈ transitionDomain P Q →
    Y Q w = LinearMap.det ((fderiv ℝ (transition P Q) w :
      ComplexModel V.dim →ₗ[ℝ] ComplexModel V.dim)) * Y P (transition P Q w)

theorem IsDensityField.neg {Y : RegularPatch V → ComplexModel V.dim → ℝ}
    (hY : IsDensityField Y) : IsDensityField fun P w => -Y P w := fun P Q w hw => by
  simp only
  rw [hY P Q w hw, mul_neg]

theorem IsDensityField.add {Y Z : RegularPatch V → ComplexModel V.dim → ℝ}
    (hY : IsDensityField Y) (hZ : IsDensityField Z) : IsDensityField fun P w => Y P w + Z P w :=
  fun P Q w hw => by simp only; rw [hY P Q w hw, hZ P Q w hw, mul_add]

theorem IsDensityField.sum {ι : Type*} (s : Finset ι)
    {Y : ι → RegularPatch V → ComplexModel V.dim → ℝ} (hY : ∀ i ∈ s, IsDensityField (Y i)) :
    IsDensityField fun P w => ∑ i ∈ s, Y i P w := fun P Q w hw => by
  simp only
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i hi => hY i hi P Q w hw

/-- A density field times a function on `M`, read through the parametrizations. -/
theorem IsDensityField.mul_comp {Y : RegularPatch V → ComplexModel V.dim → ℝ}
    (hY : IsDensityField Y) (g : M → ℝ) :
    IsDensityField fun P w => g (P.toManifold w) * Y P w := fun P Q w hw => by
  simp only
  rw [hY P Q w hw, toManifold_transition hw]
  ring

namespace RegularDecomposition

variable (D : RegularDecomposition V)

/-- **One piece, transferred to a patch `Q`**: if the field vanishes at the parameters of the
piece whose image `Q` does not see inside `Ω'`, its integral over the piece is its integral
over the transported overlap in `Q`'s parameters (change of variables). -/
theorem setLIntegral_piece_eq {Y : RegularPatch V → ComplexModel V.dim → ℝ}
    (hY : IsDensityField Y) (Q : RegularPatch V) {Ω' : Set (ComplexModel V.dim)}
    (hΩ' : MeasurableSet Ω') (hΩ'sub : Ω' ⊆ Q.parameterDomain)
    (hvan : ∀ j w, w ∈ D.piece j → (D.patch j).toManifold w ∉ Q.toManifold '' Ω' →
      Y (D.patch j) w = 0) (j : ℕ) :
    ∫⁻ w in D.piece j, ENNReal.ofReal (Y (D.patch j) w) =
      ∫⁻ u in transition Q (D.patch j) '' overlapParameters Q (D.patch j) (D.piece j) Ω',
        ENNReal.ofReal (Y Q u) := by
  set S := overlapParameters Q (D.patch j) (D.piece j) Ω' with hSdef
  have hS : MeasurableSet S :=
    measurableSet_overlapParameters Q (D.patch j) (D.measurableSet_piece j) hΩ'
  have hSsub : S ⊆ D.piece j := overlapParameters_subset _ _ _ _
  have hStr : S ⊆ transitionDomain Q (D.patch j) :=
    overlapParameters_subset_transitionDomain _ _ _ _
  -- outside the overlap the field vanishes
  have hrest : ∫⁻ w in D.piece j \ S, ENNReal.ofReal (Y (D.patch j) w) = 0 := by
    rw [← lintegral_zero (μ := volume.restrict (D.piece j \ S))]
    refine setLIntegral_congr_fun ((D.measurableSet_piece j).diff hS) fun w hw => ?_
    have hnot : (D.patch j).toManifold w ∉ Q.toManifold '' Ω' := fun hmem => hw.2 (by
      rw [hSdef, ← inter_preimage_image_toManifold Q (D.patch j) (D.piece_subset j) hΩ'sub]
      exact ⟨hw.1, hmem⟩)
    rw [hvan j w hw.1 hnot, ENNReal.ofReal_zero]
  have hsplit : D.piece j = S ∪ (D.piece j \ S) := (union_sdiff_cancel hSsub).symm
  rw [hsplit, lintegral_union ((D.measurableSet_piece j).diff hS) disjoint_sdiff_right, hrest,
    add_zero]
  -- change of variables on the overlap
  have hderiv : ∀ w ∈ S, HasFDerivWithinAt (transition Q (D.patch j))
      (fderiv ℝ (transition Q (D.patch j)) w) S w := fun w hw =>
    ((differentiableAt_transition (hStr hw)).restrictScalars ℝ).hasFDerivAt.hasFDerivWithinAt
  rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hS hderiv
    ((injOn_transition Q (D.patch j)).mono hStr)]
  refine setLIntegral_congr_fun hS fun w hw => ?_
  have hnn := det_fderiv_transition_nonneg (hStr hw)
  rw [hY Q (D.patch j) w (hStr hw), ENNReal.ofReal_mul hnn]
  congr 2
  exact (abs_of_nonneg hnn).symm

/-- **The transfer (nonnegative form).**  Summed over the decomposition, the integrals of a
density field vanishing off `Q(Ω')` are its integral over `Ω'` in `Q`'s parameters. -/
theorem tsum_setLIntegral_eq {Y : RegularPatch V → ComplexModel V.dim → ℝ}
    (hY : IsDensityField Y) (Q : RegularPatch V) {Ω' : Set (ComplexModel V.dim)}
    (hΩ' : MeasurableSet Ω') (hΩ'sub : Ω' ⊆ Q.parameterDomain)
    (hvan : ∀ j w, w ∈ D.piece j → (D.patch j).toManifold w ∉ Q.toManifold '' Ω' →
      Y (D.patch j) w = 0) :
    ∑' j, ∫⁻ w in D.piece j, ENNReal.ofReal (Y (D.patch j) w) =
      ∫⁻ u in Ω', ENNReal.ofReal (Y Q u) := by
  set T : ℕ → Set (ComplexModel V.dim) := fun j =>
    transition Q (D.patch j) '' overlapParameters Q (D.patch j) (D.piece j) Ω' with hT
  have hTm : ∀ j, MeasurableSet (T j) := fun j =>
    measurableSet_image_overlapParameters Q (D.patch j) (D.measurableSet_piece j) hΩ'
  -- each transported overlap lies over the image of its piece
  have hTimage : ∀ j u, u ∈ T j → ∃ w ∈ D.piece j, Q.toManifold u = (D.patch j).toManifold w := by
    rintro j _ ⟨w, hw, rfl⟩
    exact ⟨w, overlapParameters_subset _ _ _ _ hw,
      toManifold_transition (overlapParameters_subset_transitionDomain _ _ _ _ hw)⟩
  have hTdisj : Pairwise (Function.onFun Disjoint T) := by
    intro i j hij
    rw [Function.onFun, Set.disjoint_left]
    intro u hui huj
    obtain ⟨wi, hwi, hi⟩ := hTimage i u hui
    obtain ⟨wj, hwj, hj⟩ := hTimage j u huj
    exact Set.disjoint_left.mp (D.pairwise_disjoint hij) ⟨wi, hwi, rfl⟩ ⟨wj, hwj, by rw [← hj, hi]⟩
  have hTcover : (⋃ j, T j) = Ω' := by
    refine Subset.antisymm (iUnion_subset fun j => image_overlapParameters_subset _ _ _ _)
      fun u hu => ?_
    obtain ⟨j, w, hw, hwu⟩ := D.exists_mem_image
      (RegularPatch.toManifold_mem_regularLocus Q (hΩ'sub hu))
    obtain ⟨hmem, hτ⟩ := mem_transitionDomain_and_transition_eq (D.piece_subset j hw)
      (hΩ'sub hu) hwu
    exact mem_iUnion.2 ⟨j, w, ⟨⟨hw, hmem⟩, by rw [mem_preimage, hτ]; exact hu⟩, hτ⟩
  rw [← hTcover, lintegral_iUnion hTm hTdisj]
  exact tsum_congr fun j => D.setLIntegral_piece_eq hY Q hΩ' hΩ'sub hvan j

/-- **The transfer (signed form).**  A density field vanishing off `Q(Ω')`, integrable on `Ω'`
and a.e.-strongly measurable on the pieces, is integrable on every piece, and the integrals over
the pieces sum to its integral over `Ω'`. -/
theorem integrableOn_piece_and_hasSum {Y : RegularPatch V → ComplexModel V.dim → ℝ}
    (hY : IsDensityField Y) (Q : RegularPatch V) {Ω' : Set (ComplexModel V.dim)}
    (hΩ' : MeasurableSet Ω') (hΩ'sub : Ω' ⊆ Q.parameterDomain)
    (hvan : ∀ j w, w ∈ D.piece j → (D.patch j).toManifold w ∉ Q.toManifold '' Ω' →
      Y (D.patch j) w = 0)
    (hmeas : ∀ j, AEStronglyMeasurable (Y (D.patch j)) (volume.restrict (D.piece j)))
    (hint : IntegrableOn (Y Q) Ω') :
    (∀ j, IntegrableOn (Y (D.patch j)) (D.piece j)) ∧
      HasSum (fun j => ∫ w in D.piece j, Y (D.patch j) w) (∫ u in Ω', Y Q u) := by
  have hpos := D.tsum_setLIntegral_eq hY Q hΩ' hΩ'sub hvan
  have hneg := D.tsum_setLIntegral_eq hY.neg Q hΩ' hΩ'sub fun j w hw hnot => by
    rw [hvan j w hw hnot, neg_zero]
  have hposfin : ∫⁻ u in Ω', ENNReal.ofReal (Y Q u) ≠ ⊤ :=
    (hint.lintegral_lt_top).ne
  have hnegfin : ∫⁻ u in Ω', ENNReal.ofReal (-Y Q u) ≠ ⊤ :=
    (hint.neg.lintegral_lt_top).ne
  have hint_piece : ∀ j, IntegrableOn (Y (D.patch j)) (D.piece j) := by
    intro j
    refine ⟨hmeas j, ?_⟩
    have h1 : ∫⁻ w in D.piece j, ENNReal.ofReal (Y (D.patch j) w) ≠ ⊤ :=
      ne_top_of_le_ne_top (hpos ▸ hposfin) (ENNReal.le_tsum j)
    have h2 : ∫⁻ w in D.piece j, ENNReal.ofReal (-Y (D.patch j) w) ≠ ⊤ :=
      ne_top_of_le_ne_top (hneg ▸ hnegfin)
        (ENNReal.le_tsum (f := fun j => ∫⁻ w in D.piece j, ENNReal.ofReal (-Y (D.patch j) w)) j)
    rw [HasFiniteIntegral]
    have heq : (fun w => ‖Y (D.patch j) w‖ₑ) =
        fun w => ENNReal.ofReal (Y (D.patch j) w) + ENNReal.ofReal (-Y (D.patch j) w) :=
      funext fun w => enorm_eq_ofReal_add_ofReal_neg _
    rw [heq, lintegral_add_left' (hmeas j).aemeasurable.ennreal_ofReal]
    exact ENNReal.add_lt_top.mpr ⟨h1.lt_top, h2.lt_top⟩
  refine ⟨hint_piece, ?_⟩
  have hsum_pos := ENNReal.hasSum_toReal (hpos ▸ hposfin)
  have hsum_neg := ENNReal.hasSum_toReal (hneg ▸ hnegfin)
  rw [← ENNReal.tsum_toReal_eq (f := fun j => ∫⁻ w in D.piece j, ENNReal.ofReal (Y (D.patch j) w))
    fun j => ne_top_of_le_ne_top (hpos ▸ hposfin) (ENNReal.le_tsum j), hpos] at hsum_pos
  rw [← ENNReal.tsum_toReal_eq (f := fun j => ∫⁻ w in D.piece j, ENNReal.ofReal (-Y (D.patch j) w))
    fun j => ne_top_of_le_ne_top (hneg ▸ hnegfin)
      (ENNReal.le_tsum (f := fun j => ∫⁻ w in D.piece j, ENNReal.ofReal (-Y (D.patch j) w)) j),
    hneg] at hsum_neg
  have := hsum_pos.sub hsum_neg
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hint]
  refine this.congr_fun fun j => ?_
  exact integral_eq_lintegral_pos_part_sub_lintegral_neg_part (hint_piece j)

end RegularDecomposition

end Transfer

/-! ### The measure on `ℕ × ℂ^k` -/

section Measure

variable {V : ClosedIrreducibleAnalyticSubvariety n M}

namespace RegularDecomposition

variable (D : RegularDecomposition V)

/-- The measure on `ℕ × ℂ^k` carrying the pieces: `∫ F = ∑ⱼ ∫_{Eⱼ} F(j, ·)`. -/
def measure : Measure (ℕ × ComplexModel V.dim) :=
  Measure.sum fun j => (volume.restrict (D.piece j)).map (Prod.mk j)

theorem aestronglyMeasurable_measure_iff {F : ℕ × ComplexModel V.dim → ℝ} :
    AEStronglyMeasurable F D.measure ↔
      ∀ j, AEStronglyMeasurable (fun w => F (j, w)) (volume.restrict (D.piece j)) := by
  rw [measure, aestronglyMeasurable_sum_measure_iff]
  exact forall_congr' fun j => (measurableEmbedding_prodMk_left j).aestronglyMeasurable_map_iff

theorem lintegral_measure (G : ℕ × ComplexModel V.dim → ℝ≥0∞) (hG : Measurable G) :
    ∫⁻ x, G x ∂D.measure = ∑' j, ∫⁻ w in D.piece j, G (j, w) := by
  rw [measure, lintegral_sum_measure]
  exact tsum_congr fun j => lintegral_map hG measurable_prodMk_left

theorem integrable_measure_iff {F : ℕ × ComplexModel V.dim → ℝ} :
    Integrable F D.measure ↔
      (∀ j, AEStronglyMeasurable (fun w => F (j, w)) (volume.restrict (D.piece j))) ∧
        ∑' j, ∫⁻ w in D.piece j, ‖F (j, w)‖ₑ < ⊤ := by
  rw [Integrable, aestronglyMeasurable_measure_iff, HasFiniteIntegral, measure,
    lintegral_sum_measure]
  refine and_congr_right fun hm => ?_
  rw [tsum_congr fun j => (measurableEmbedding_prodMk_left j).lintegral_map _]

theorem hasSum_integral_measure {F : ℕ × ComplexModel V.dim → ℝ} (hF : Integrable F D.measure) :
    HasSum (fun j => ∫ w in D.piece j, F (j, w)) (∫ x, F x ∂D.measure) := by
  have h := MeasureTheory.hasSum_integral_measure (μ := fun j =>
    (volume.restrict (D.piece j)).map (Prod.mk j)) hF
  refine h.congr_fun fun j => ?_
  exact ((measurableEmbedding_prodMk_left j).integral_map _).symm

/-- **The transfer, on the measure of the decomposition.**  A density field vanishing off
`Q(Ω')`, integrable on `Ω'` and a.e.-strongly measurable on the pieces, read as the function
`(j, w) ↦ Y_{γⱼ}(w)`, is integrable for `D.measure`, with integral `∫_{Ω'} Y_Q`. -/
theorem integrable_measure_and_integral_eq {Y : RegularPatch V → ComplexModel V.dim → ℝ}
    (hY : IsDensityField Y) (Q : RegularPatch V) {Ω' : Set (ComplexModel V.dim)}
    (hΩ' : MeasurableSet Ω') (hΩ'sub : Ω' ⊆ Q.parameterDomain)
    (hvan : ∀ j w, w ∈ D.piece j → (D.patch j).toManifold w ∉ Q.toManifold '' Ω' →
      Y (D.patch j) w = 0)
    (hmeas : ∀ j, AEStronglyMeasurable (Y (D.patch j)) (volume.restrict (D.piece j)))
    (hint : IntegrableOn (Y Q) Ω') :
    Integrable (fun x : ℕ × ComplexModel V.dim => Y (D.patch x.1) x.2) D.measure ∧
      ∫ x, Y (D.patch x.1) x.2 ∂D.measure = ∫ u in Ω', Y Q u := by
  have hpos := D.tsum_setLIntegral_eq hY Q hΩ' hΩ'sub hvan
  have hneg := D.tsum_setLIntegral_eq hY.neg Q hΩ' hΩ'sub fun j w hw hnot => by
    rw [hvan j w hw hnot, neg_zero]
  have hF : Integrable (fun x : ℕ × ComplexModel V.dim => Y (D.patch x.1) x.2) D.measure := by
    rw [integrable_measure_iff]
    refine ⟨hmeas, ?_⟩
    have heq : ∀ j, ∫⁻ w in D.piece j, ‖Y (D.patch j) w‖ₑ =
        (∫⁻ w in D.piece j, ENNReal.ofReal (Y (D.patch j) w)) +
          ∫⁻ w in D.piece j, ENNReal.ofReal (-Y (D.patch j) w) := fun j => by
      simp_rw [enorm_eq_ofReal_add_ofReal_neg]
      exact lintegral_add_left' (hmeas j).aemeasurable.ennreal_ofReal _
    simp_rw [heq]
    rw [ENNReal.tsum_add, hpos, hneg]
    exact ENNReal.add_lt_top.mpr ⟨hint.lintegral_lt_top, hint.neg.lintegral_lt_top⟩
  refine ⟨hF, ?_⟩
  exact (D.hasSum_integral_measure hF).unique
    (D.integrableOn_piece_and_hasSum hY Q hΩ' hΩ'sub hvan hmeas hint).2

end RegularDecomposition

end Measure

/-! ### Mixed densities of smooth forms in patch parameters -/

section Mixed

variable {V : ClosedIrreducibleAnalyticSubvariety n M}

/-- The density, in the parameters of a regular patch, of the wedge product of the
pull-backs of `dim V` smooth real two-forms. -/
def patchMixedDensity (a : Fin V.dim → SmoothRealForm n M 2) (P : RegularPatch V)
    (w : ComplexModel V.dim) : ℝ :=
  MongeAmpere.actualMixedTopDensity fun i => patchCoordinateForm (a i) P w

theorem patchMixedDensity_const (a : SmoothRealForm n M 2) (P : RegularPatch V)
    (w : ComplexModel V.dim) : patchMixedDensity (fun _ => a) P w = patchFormDensity a P w :=
  MongeAmpere.actualMixedTopDensity_const _

/-- **Mixed patch densities are density fields** (the mixed pull-back law). -/
theorem isDensityField_patchMixedDensity (a : Fin V.dim → SmoothRealForm n M 2) :
    IsDensityField (patchMixedDensity a) := fun P Q w hw => by
  simp only [patchMixedDensity]
  rw [show (fun i => patchCoordinateForm (a i) Q w) = fun i =>
      (patchCoordinateForm (a i) P (transition P Q w)).compContinuousLinearMap
        (fderiv ℝ (transition P Q) w) from funext fun i => patchCoordinateForm_transition (a i) hw]
  exact MongeAmpere.actualMixedTopDensity_compContinuousLinearMap _ _

theorem continuous_actualMixedTopDensity (k : ℕ) :
    Continuous (fun A : Fin k → MongeAmpere.CoordinateRealTwoForm k =>
      MongeAmpere.actualMixedTopDensity A) := by
  have h : (fun A : Fin k → MongeAmpere.CoordinateRealTwoForm k =>
      MongeAmpere.actualMixedTopDensity A) = fun A => ((2 : ℝ) ^ k)⁻¹ *
        MongeAmpere.coordinatePairingSumFamily A
          (finProdFinEquiv : Fin k × Fin 2 → Fin (k * 2)) MongeAmpere.coordinateRealFrame :=
    funext MongeAmpere.actualMixedTopDensity_eq_pairingSum
  rw [h]
  unfold MongeAmpere.coordinatePairingSumFamily
  fun_prop

/-- The pulled-back coordinate form is continuous on the parameter domain. -/
theorem continuousOn_patchCoordinateForm (a : SmoothRealForm n M 2) (P : RegularPatch V) :
    ContinuousOn (patchCoordinateForm a P) P.parameterDomain := by
  have hparam : ContDiffOn ℝ ∞ P.coordinateParametrization P.parameterDomain := by
    have hinv : ContDiffOn ℝ ∞ P.flattening.invFun P.flattening.target :=
      contDiffOn_real_of_differentiableOn_complex P.flattening.invFun_holomorphic
        P.flattening.isOpen_target
    exact hinv.comp ((AdmissibleCurrentFormPositivity.planeInclusionCLM V.dim n).restrictScalars
      ℝ).contDiff.contDiffOn fun w hw => hw
  have hderiv : ContinuousOn (fderiv ℝ P.coordinateParametrization) P.parameterDomain :=
    hparam.continuousOn_fderiv_of_isOpen
      (AdmissibleCurrentFormPositivity.RegularPatchDerivative.isOpen_parameterDomain P) (by simp)
  have hcoeff : ContinuousOn (fun w =>
      a.coeff (complexChartAt (n := n) P.center) (P.coordinateParametrization w))
      P.parameterDomain := by
    refine (a.smooth _).continuousOn.comp hparam.continuousOn ?_
    intro w hw
    exact P.source_subset (P.flattening.mapsTo_invFun hw)
  change ContinuousOn (fun w =>
    (ContinuousAlternatingMap.compContinuousLinearMapCLM
      (fderiv ℝ P.coordinateParametrization w)) (a.coeff (complexChartAt (n := n) P.center)
        (P.coordinateParametrization w))) P.parameterDomain
  exact (ContinuousAlternatingMap.continuous_compContinuousLinearMapCLM.comp_continuousOn
    hderiv).clm_apply hcoeff

theorem continuousOn_patchMixedDensity (a : Fin V.dim → SmoothRealForm n M 2)
    (P : RegularPatch V) : ContinuousOn (patchMixedDensity a P) P.parameterDomain :=
  (continuous_actualMixedTopDensity V.dim).comp_continuousOn
    (continuousOn_pi.2 fun i => continuousOn_patchCoordinateForm (a i) P)

end Mixed

end

end SGPT.Foundations.Analysis.Pending.StokesRegularDecomposition
