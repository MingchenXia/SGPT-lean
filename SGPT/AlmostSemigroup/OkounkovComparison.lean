import SGPT.AlmostSemigroup.OkounkovExtension

/-! Actual source carrier comparison for the genuine almost-semigroup body extension. -/

noncomputable section
namespace SGPT.AlmostSemigroup.OkounkovComparison
open Set Filter MeasureTheory Metric
open scoped Topology
open Okounkov Class OkounkovExtension

/-- Actual density supplies actual full-source sequences converging in the source pseudometric. -/
theorem exists_full_sequence {n : ℕ} {C : AdmissibleCone n} (S : AlmostSpace C) :
    ∃ u : ℕ → FullSemigroup C, Tendsto (fun i ↦ fullToAlmost (u i)) atTop (𝓝 S) := by
  obtain ⟨u, hu, hlim⟩ := mem_closure_iff_seq_limit.mp (denseRange_fullToAlmost C S)
  choose v hv using hu
  refine ⟨v, ?_⟩
  convert hlim using 1
  funext i
  exact hv i

/-- Genuine positive original intersections are actual full source members. -/
def fullIntersection {n : ℕ} {C : AdmissibleCone n} (S T : FullSemigroup C)
    (hpos : 0 < (ConeSubset.inter S.val T.val).volume) : FullSemigroup C :=
  ⟨ConeSubset.inter S.val T.val, ⟨fun x hx y hy ↦
    ⟨S.property.1 x hx.1 y hy.1, T.property.1 x hx.2 y hy.2⟩, by
      change LatticeSlices.generatedGroup (S.semigroup ⊓ T.semigroup) = ⊤
      exact Intersection.generatedGroup_intersection_eq_top C S.semigroup T.semigroup
        S.semigroup_le_source T.semigroup_le_source S.generatedGroup_eq_top
        T.generatedGroup_eq_top hpos⟩⟩

/-- Actual original source inclusion produces genuine original body inclusion. -/
theorem bodyMap_mono {n : ℕ} {C : AdmissibleCone n} (S T : FullSemigroup C)
    (hST : S.val.val ⊆ T.val.val) :
    (bodyMap S : Set (EuclideanSpace ℝ (Fin n))) ⊆ bodyMap T := by
  apply image_mono
  intro x hx
  exact Intersection.closedCone_mono (fun _ hy ↦ hST hy) hx

/-- Actual carrier inclusion is closed under genuine Euclidean Hausdorff limits. -/
theorem body_subset_of_tendsto {n : ℕ}
    {u v : ℕ → ConvexBody (EuclideanSpace ℝ (Fin n))}
    {K L : ConvexBody (EuclideanSpace ℝ (Fin n))}
    (hu : Tendsto u atTop (𝓝 K)) (hv : Tendsto v atTop (𝓝 L))
    (hsub : ∀ i, (u i : Set (EuclideanSpace ℝ (Fin n))) ⊆ v i) :
    (K : Set (EuclideanSpace ℝ (Fin n))) ⊆ L := by
  intro x hx
  obtain ⟨p, hp, hpx⟩ := Hyperspace.exists_member_sequence_of_tendsto
    (Hyperspace.isometry_carrierMap.continuous.continuousAt.tendsto.comp hu) hx
  exact Hyperspace.mem_of_tendsto_members
    (Hyperspace.isometry_carrierMap.continuous.continuousAt.tendsto.comp hv)
    (fun i ↦ hsub i (hp i)) hpx

/-- SGPT cor:Okocompapp: actual almost-semigroup inclusion preserves actual extended-body inclusion. -/
theorem bodyExtension_mono {n : ℕ} {C : AdmissibleCone n} (S T : AlmostSpace C)
    (hST : S.val.val ⊆ T.val.val) :
    (bodyExtension S : Set (EuclideanSpace ℝ (Fin n))) ⊆ bodyExtension T := by
  obtain ⟨u, hu⟩ := exists_full_sequence S
  obtain ⟨v, hv⟩ := exists_full_sequence T
  have huu : Tendsto (fun i ↦ (u i).val) atTop (𝓝 S.val) :=
    (continuous_subtype_val : Continuous (fun R : AlmostSpace C ↦ R.val)).tendsto S |>.comp hu
  have hvv : Tendsto (fun i ↦ (v i).val) atTop (𝓝 T.val) :=
    (continuous_subtype_val : Continuous (fun R : AlmostSpace C ↦ R.val)).tendsto T |>.comp hv
  have hinter : ConeSubset.inter S.val T.val = S.val := by
    apply Subtype.ext
    exact inter_eq_left.mpr hST
  have hi := ConeSubset.tendsto_inter (fun i ↦ (u i).val) (fun i ↦ (v i).val) S.val T.val huu hvv
  rw [hinter] at hi
  have hvol := ConeSubset.continuous_volume.tendsto S.val |>.comp hi
  have hpos : ∀ᶠ i in atTop, 0 < (ConeSubset.inter (u i).val (v i).val).volume :=
    hvol.eventually (isOpen_Ioi.mem_nhds S.property.2)
  let w : ℕ → FullSemigroup C := fun i ↦
    if h : 0 < (ConeSubset.inter (u i).val (v i).val).volume
    then fullIntersection (u i) (v i) h else v i
  have hwval : (fun i ↦ (w i).val) =ᶠ[atTop]
      (fun i ↦ ConeSubset.inter (u i).val (v i).val) := by
    filter_upwards [hpos] with i hi
    dsimp only [w]
    rw [dif_pos hi]
    rfl
  have hw : Tendsto (fun i ↦ fullToAlmost (w i)) atTop (𝓝 S) := by
    apply tendsto_subtype_rng.mpr
    exact hi.congr' hwval.symm
  have hwbody : Tendsto (fun i ↦ bodyMap (w i)) atTop (𝓝 (bodyExtension S)) := by
    have h := ((continuous_bodyExtension C).tendsto S).comp hw
    change Tendsto (fun i ↦ bodyExtension (fullToAlmost (w i))) atTop (𝓝 (bodyExtension S)) at h
    simpa only [bodyExtension_source] using h
  have hvbody : Tendsto (fun i ↦ bodyMap (v i)) atTop (𝓝 (bodyExtension T)) := by
    have h := ((continuous_bodyExtension C).tendsto T).comp hv
    change Tendsto (fun i ↦ bodyExtension (fullToAlmost (v i))) atTop (𝓝 (bodyExtension T)) at h
    simpa only [bodyExtension_source] using h
  apply body_subset_of_tendsto hwbody hvbody
  intro i
  apply bodyMap_mono
  dsimp only [w]
  split_ifs with h
  · exact fun _ hx ↦ hx.2
  · exact Subset.rfl

end SGPT.AlmostSemigroup.OkounkovComparison
