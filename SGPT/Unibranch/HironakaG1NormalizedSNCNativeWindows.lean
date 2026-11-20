import SGPT.Foundations.Analysis.Pending.HironakaG1SNCReaderNormalization
import SGPT.Unibranch.HironakaG1PrimaryNativeGraph

/-!
# Actual normalized SNC native windows and whole scalar calibration

The ordinary original data derive the readers first. Their actual inverse
ambient functions construct normalized carriers/native window maps; every
old-slot calibration uses WHOLE ideals and the actual scalar maps.
BP FIRST: `hironaka-g1-normalized-snc-native-windows.tex`.
-/
set_option autoImplicit false
open Set Filter TopologicalSpace CategoryTheory Opposite AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace SGPT.Unibranch.HironakaG1NormalizedSNCNativeWindows

open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
  SGPT.Foundations.Analysis.FirstPass.BlowupSequences SGPT.Foundations.Analysis.Pending
  BlowupTowers BlowupFlatCoordinates NormalCrossings
  HironakaG1SNCReaderNormalization HironakaActualAnalyticSubspace
  HironakaActualAnalyticSubspaceMaps HironakaActualAnalyticSubspaceOpenRestriction
  HironakaActualAnalyticSubspacePresentationIndependence HironakaActualAnalyticSubspaceIntrinsicLifting
  HironakaActualIntrinsicLabelledBoundaryIdeals HironakaSmoothCentreRealDomainActualSheafStalk
  HironakaActualWholeStalkHolomorphicPullback HironakaG1PrimaryNativeGraph
  HironakaReducedComplexAnalyticSpaces
  HironakaHolomorphicJetRankLoci HironakaHolomorphicJetChartInvariance

noncomputable section

variable {n r a : ℕ} {M : CMfd.{0} n} {p : M}
  (C : Set M) (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) p p))
  (hsrc : Φ.source ⊆ (chartAt (ComplexModel n) p).target) (σ : Fin (r+a) ≃ Fin n)

local notation "P0" => readerTarget Φ σ
local notation "U0" => readerSource Φ
local notation "D0" => readerDiffeomorph Φ hsrc σ

/-- Actual inverse ambient reader into the ORIGINAL ambient manifold. -/
def ambientInverse (y : P0) : M := ((D0).symm y).val

theorem ambientInverse_holomorphic :
    ContMDiff 𝓘(ℂ,ComplexModel (r+a)) 𝓘(ℂ,ComplexModel n) ∞ (ambientInverse Φ hsrc σ) :=
  contMDiff_subtype_val.comp (D0).symm.contMDiff

/-- The genuine normalized carrier, retaining the actual original defining carrier. -/
def normalizedCarrier : Set P0 := (ambientInverse Φ hsrc σ) ⁻¹' C

theorem normalizedCarrier_analytic (hC : IsComplexAnalyticSubset (n := n) C) :
    IsComplexAnalyticSubset (n := r+a) (normalizedCarrier C Φ hsrc σ) :=
  AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage (ambientInverse_holomorphic Φ hsrc σ) hC

/-- FULL native quotient isomorphism before the original open-restriction inclusion. -/
def nativeReaderIso : actualSubspaceLocallyRingedSpace (n := r+a) (normalizedCarrier C Φ hsrc σ) ≅
    actualSubspaceLocallyRingedSpace (n := n) ((Subtype.val : U0 → M) ⁻¹' C) :=
  actualSubspaceMutualRestrictionIso (D0).symm.contMDiff (D0).contMDiff
    (fun _ hy => hy) (fun x hx => by
      change ((D0).symm (D0 x)).val ∈ C
      rw [(D0).symm_apply_apply]
      exact hx)
    (fun y _ => (D0).apply_symm_apply y) (fun x _ => (D0).symm_apply_apply x)

/-- The SAME actual descended original window map, not only its point function. -/
def normalizedWindowMap : actualSubspaceLocallyRingedSpace (n := r+a) (normalizedCarrier C Φ hsrc σ) ⟶
    actualSubspaceLocallyRingedSpace (n := n) C :=
  actualSubspaceMap (ambientInverse_holomorphic Φ hsrc σ) (fun _ hy => hy)

theorem normalizedWindowMap_factor : normalizedWindowMap C Φ hsrc σ =
    (nativeReaderIso C Φ hsrc σ).hom ≫ actualOpenSubspaceMap (n := n) C U0 := by
  exact actualSubspaceMap_comp (D0).symm.contMDiff (contMDiff_subtype_val (U := U0))
    (C := normalizedCarrier C Φ hsrc σ) (D := (Subtype.val : U0 → M) ⁻¹' C) (E := C)
    (fun _ hy => hy) (fun _ hx => hx)

instance normalizedWindowMap_isOpenImmersion :
    LocallyRingedSpace.IsOpenImmersion (normalizedWindowMap C Φ hsrc σ) := by
  rw [normalizedWindowMap_factor]
  infer_instance

theorem normalizedWindowMap_point : normalizedWindowMap C Φ hsrc σ ≫ subspacePointMap (n := n) C =
    subspacePointMap (n := r+a) (normalizedCarrier C Φ hsrc σ) :=
  actualSubspaceMap_point (ambientInverse_holomorphic Φ hsrc σ) (fun _ hy => hy)

/-- Entire actual ambient inclusion/scalar triangle of the ORIGINAL reader. -/
theorem normalizedWindowMap_inclusion : normalizedWindowMap C Φ hsrc σ ≫ actualSubspaceInclusion (n := n) C =
    actualSubspaceInclusion (n := r+a) (normalizedCarrier C Φ hsrc σ) ≫
      ChartedSpace.locallyRingedSpaceMap (ambientInverse Φ hsrc σ) (ambientInverse_holomorphic Φ hsrc σ) :=
  (actualSubspaceMap_inclusion (ambientInverse_holomorphic Φ hsrc σ) (fun _ hy => hy)).symm

include hsrc in
private theorem reader_zero_mem (hzero : Φ.toFun (chartAt (ComplexModel n) p p) = 0) :
    (0 : ComplexModel (r+a)) ∈ P0 := by
  have hp := (D0 ⟨p,mem_flatDomain_self Φ⟩).property
  rw [readerDiffeomorph_center Φ hsrc σ hzero] at hp
  exact hp

private theorem ambientInverse_zero (hzero : Φ.toFun (chartAt (ComplexModel n) p p) = 0) :
    ambientInverse Φ hsrc σ ⟨0,reader_zero_mem Φ hsrc σ hzero⟩ = p := by
  let x : U0 := ⟨p,mem_flatDomain_self Φ⟩
  let y : P0 := ⟨0,reader_zero_mem Φ hsrc σ hzero⟩
  have hxy : D0 x = y := Subtype.ext (readerDiffeomorph_center Φ hsrc σ hzero)
  have hinv : (D0).symm y = x := (congrArg (D0).symm hxy).symm.trans ((D0).symm_apply_apply x)
  exact congrArg Subtype.val hinv

/-- The genuine normalized zero point is derived from the SAME original point. -/
def normalizedZero (hp : p ∈ C) (hzero : Φ.toFun (chartAt (ComplexModel n) p p) = 0) :
    normalizedCarrier C Φ hsrc σ :=
  ⟨⟨0,reader_zero_mem Φ hsrc σ hzero⟩,by
    change ambientInverse Φ hsrc σ ⟨0,reader_zero_mem Φ hsrc σ hzero⟩ ∈ C
    rw [ambientInverse_zero Φ hsrc σ hzero]
    exact hp⟩

theorem normalizedZero_original (hp : p ∈ C) (hzero : Φ.toFun (chartAt (ComplexModel n) p p) = 0) :
    (normalizedWindowMap C Φ hsrc σ).base (normalizedZero C Φ hsrc σ hp hzero) = ⟨p,hp⟩ :=
  Subtype.ext (ambientInverse_zero Φ hsrc σ hzero)

private theorem native_function {n m : ℕ} {M N : Type} [TopologicalSpace M] [TopologicalSpace N]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    [ChartedSpace (ComplexModel m) N] [IsComplexManifold m N]
    (f : M → N) (hf : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel m) ∞ f)
    (x : M) (g : N → ℂ) (hg : HolomorphicAt m g (f x)) :
    (ChartedSpace.locallyRingedSpaceMap f hf).stalkMap x (actualOriginalFunctionGerm (f x) g hg) =
      actualOriginalFunctionGerm x (g ∘ f) (hg.comp_contMDiff (Eventually.of_forall fun _ => hf.contMDiffAt)) := by
  apply (actualStalkChartEquiv (n := n) x).injective
  rw [actualNativeStalk_chart_pullback,actualOriginalFunctionGerm_chart,
    actualHolomorphicGermPullback_original_function,actualOriginalFunctionGerm_chart]

private theorem original_eq {n : ℕ} {M : Type} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    (x : M) (f g : M → ℂ) (hf : HolomorphicAt n f x) (hg : HolomorphicAt n g x) (heq : f = g) :
    actualOriginalFunctionGerm x f hf = actualOriginalFunctionGerm x g hg := by
  cases heq
  rfl

private theorem map_singleton {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (x : R) :
    Ideal.map f (Ideal.span {x}) = Ideal.span {f x} := by rw [Ideal.map_span,Set.image_singleton]

/-- The actual original inclusion/window stalk square on EVERY whole original function. -/
theorem normalizedWindowMap_function (y : normalizedCarrier C Φ hsrc σ) (f : M → ℂ)
    (hf : HolomorphicAt n f (ambientInverse Φ hsrc σ y.val)) :
    (normalizedWindowMap C Φ hsrc σ).stalkMap y
      ((actualSubspaceInclusion (n := n) C).stalkMap ((normalizedWindowMap C Φ hsrc σ).base y)
        (actualOriginalFunctionGerm (ambientInverse Φ hsrc σ y.val) f hf)) =
      (actualSubspaceInclusion (n := r+a) (normalizedCarrier C Φ hsrc σ)).stalkMap y
        (actualOriginalFunctionGerm y.val (f ∘ ambientInverse Φ hsrc σ)
          (hf.comp_contMDiff (Eventually.of_forall fun _ => (ambientInverse_holomorphic Φ hsrc σ).contMDiffAt))) := by
  have hs := ConcreteCategory.congr_hom
    (actualSubspaceRingedMap_stalk_square (ambientInverse_holomorphic Φ hsrc σ) (fun _ hy => hy) y)
    (actualOriginalFunctionGerm (ambientInverse Φ hsrc σ y.val) f hf)
  exact hs.trans (congrArg ((actualSubspaceInclusion (n := r+a) (normalizedCarrier C Φ hsrc σ)).stalkMap y)
    (native_function (ambientInverse Φ hsrc σ) (ambientInverse_holomorphic Φ hsrc σ) y.val f hf))

private theorem inverse_flat_coordinate (j : Fin r) :
    flatCoord Φ (σ (j.castAdd a)) ∘ ambientInverse Φ hsrc σ = fun y : P0 => y.val (j.castAdd a) := by
  funext y
  exact (readerDiffeomorph_active Φ hsrc σ ((D0).symm y) j).symm.trans
    (congrArg (fun v : P0 => v.val (j.castAdd a)) ((D0).apply_symm_apply y))

private theorem coordinate_holomorphic (j : Fin (r+a)) :
    ContMDiff 𝓘(ℂ,ComplexModel (r+a)) 𝓘(ℂ,ℂ) ∞ (fun y : P0 => y.val j) := by
  have h : ContMDiff 𝓘(ℂ,ComplexModel (r+a)) 𝓘(ℂ,ℂ) ∞ (fun z : ComplexModel (r+a) => z j) :=
    (EuclideanSpace.proj (𝕜 := ℂ) j : ComplexModel (r+a) →L[ℂ] ℂ).contMDiff
  exact h.comp (contMDiff_subtype_val (U := P0))

private theorem coordinate_original_section (y : P0) (j : Fin (r+a)) :
    actualOriginalFunctionGerm y (fun z : P0 => z.val j)
      (Eventually.of_forall fun _ => (coordinate_holomorphic Φ σ j).contMDiffAt.mdifferentiableAt (by simp)) =
    (actualComplexStructureSheaf (n := r+a) P0).presheaf.germ ⊤ y (by trivial) (actualCoordinateSection P0 j) := by
  apply actualOriginalFunctionGerm_eq_section ⊤ y (by trivial) (actualCoordinateSection P0 j)
  exact Eventually.of_forall fun z => (sectionExtension_apply ⊤ (actualCoordinateSection P0 j) z (by trivial)).trans rfl

/-- The ENTIRE normalized native slot, using the literal actual coordinate section. -/
def normalizedSlotIdeal {l : ℕ} (slot : Fin l → Option (Fin r))
    (y : normalizedCarrier C Φ hsrc σ) (i : Fin l) :
    Ideal (((actualSubspaceSheaf (n := r+a) (normalizedCarrier C Φ hsrc σ)).presheaf.stalk y).carrier) :=
  match slot i with
  | none => ⊤
  | some j => coordinateImageIdeal P0 (normalizedCarrier C Φ hsrc σ) y (j.castAdd a)

private theorem active_whole_slot {E : List (Set M)} (i : Fin E.length) (j : Fin r)
    (hm : ∀ x ∈ flatDomain Φ, x ∈ E.get i ↔ flatCoord Φ (σ (j.castAdd a)) x = 0)
    (y : normalizedCarrier C Φ hsrc σ) :
    Ideal.map ((normalizedWindowMap C Φ hsrc σ).stalkMap y).hom
      (actualLabelledBoundaryTraceIdeal C E i ((normalizedWindowMap C Φ hsrc σ).base y)) =
        coordinateImageIdeal P0 (normalizedCarrier C Φ hsrc σ) y (j.castAdd a) := by
  let q := (normalizedWindowMap C Φ hsrc σ).base y
  have hq : q.val ∈ flatDomain Φ := ((D0).symm y.val).property
  have hw := actualWholeHyperplaneStalkIdeal_eq_span Φ hm q.val hq
  have ho : actualLabelledBoundaryTraceIdeal C E i q =
      Ideal.span {(actualSubspaceInclusion (n := n) C).stalkMap q
        (actualOriginalFunctionGerm q.val (flatCoord Φ (σ (j.castAdd a))) (holomorphicAt_flatCoord Φ _ hq))} :=
    (congrArg (Ideal.map ((actualSubspaceInclusion (n := n) C).stalkMap q).hom) hw).trans (map_singleton _ _)
  have hf : HolomorphicAt n (flatCoord Φ (σ (j.castAdd a))) (ambientInverse Φ hsrc σ y.val) :=
    holomorphicAt_flatCoord Φ (σ (j.castAdd a)) hq
  have hcoord : HolomorphicAt (r+a) (fun z : P0 => z.val (j.castAdd a)) y.val :=
    Eventually.of_forall fun _ => (coordinate_holomorphic Φ σ (j.castAdd a)).contMDiffAt.mdifferentiableAt (by simp)
  have hg := original_eq y.val _ _
    (hf.comp_contMDiff (Eventually.of_forall fun _ => (ambientInverse_holomorphic Φ hsrc σ).contMDiffAt))
    hcoord (inverse_flat_coordinate Φ hsrc σ j)
  have helem := (normalizedWindowMap_function C Φ hsrc σ y (flatCoord Φ (σ (j.castAdd a))) hf).trans
    (congrArg ((actualSubspaceInclusion (n := r+a) (normalizedCarrier C Φ hsrc σ)).stalkMap y)
      (hg.trans (coordinate_original_section Φ σ y.val (j.castAdd a))))
  exact ((congrArg (Ideal.map ((normalizedWindowMap C Φ hsrc σ).stalkMap y).hom) ho).trans (map_singleton _ _)).trans
    (congrArg (fun x => Ideal.span {x}) helem)

private theorem original_one (x : M) :
    actualOriginalFunctionGerm (n := n) x (fun _ : M => (1 : ℂ)) (holomorphicAt_const (n := n) (x := x) 1) = 1 := by
  have h := actualOriginalFunctionGerm_eq_section (n := n) (⊤ : Opens M) x (by trivial)
    (1 : actualComplexSection (n := n) (⊤ : Opens M)) (fun _ : M => (1 : ℂ)) (holomorphicAt_const 1)
    (Eventually.of_forall fun z => (sectionExtension_apply ⊤ (1 : actualComplexSection (n := n) (⊤ : Opens M)) z (by trivial)).trans rfl)
  exact h.trans (map_one _)

private theorem inactive_whole_slot {E : List (Set M)} (i : Fin E.length)
    (hm : ∀ x ∈ flatDomain Φ, x ∉ E.get i) (y : normalizedCarrier C Φ hsrc σ) :
    Ideal.map ((normalizedWindowMap C Φ hsrc σ).stalkMap y).hom
      (actualLabelledBoundaryTraceIdeal C E i ((normalizedWindowMap C Φ hsrc σ).base y)) = ⊤ := by
  let q := (normalizedWindowMap C Φ hsrc σ).base y
  have hq : q.val ∈ flatDomain Φ := ((D0).symm y.val).property
  have hmem : (vanishingIdeal (n := n) (E.get i)).mem q.val (fun _ : M => (1 : ℂ)) := by
    refine ⟨holomorphicAt_const 1,?_⟩
    filter_upwards [(isOpen_flatDomain Φ).mem_nhds hq] with x hx hxi
    exact (hm x hx hxi).elim
  have ht : actualWholeSheafStalkIdeal (vanishingIdeal (n := n) (E.get i)) q.val = ⊤ := by
    apply (Ideal.eq_top_iff_one _).mpr
    have h := Ideal.subset_span (s := {g | ∃ (f : M → ℂ) (hf : HolomorphicAt n f q.val),
      (vanishingIdeal (n := n) (E.get i)).mem q.val f ∧ g = actualOriginalFunctionGerm q.val f hf})
      ⟨fun _ : M => (1 : ℂ),holomorphicAt_const 1,hmem,rfl⟩
    exact (original_one (n := n) q.val) ▸ h
  have ho : actualLabelledBoundaryTraceIdeal C E i q = ⊤ :=
    (congrArg (Ideal.map ((actualSubspaceInclusion (n := n) C).stalkMap q).hom) ht).trans (Ideal.map_top _)
  exact (congrArg (Ideal.map ((normalizedWindowMap C Φ hsrc σ).stalkMap y).hom) ho).trans (Ideal.map_top _)

/-- ENTIRE original old-slot scalar calibration on EVERY actual normalized point. -/
theorem whole_slot_calibration {E : List (Set M)} (slot : Fin E.length → Option (Fin r))
    (hm : ∀ x ∈ flatDomain Φ, ∀ i : Fin E.length,
      x ∈ E.get i ↔ ∃ j, slot i = some j ∧ flatCoord Φ (σ (j.castAdd a)) x = 0)
    (y : normalizedCarrier C Φ hsrc σ) (i : Fin E.length) :
    Ideal.map ((normalizedWindowMap C Φ hsrc σ).stalkMap y).hom
      (actualLabelledBoundaryTraceIdeal C E i ((normalizedWindowMap C Φ hsrc σ).base y)) =
        normalizedSlotIdeal C Φ hsrc σ slot y i := by
  cases hs : slot i with
  | none =>
    have ha : ∀ x ∈ flatDomain Φ, x ∉ E.get i := by
      intro x hx hxi
      obtain ⟨j,hj,_⟩ := (hm x hx i).mp hxi
      have hbad : (none : Option (Fin r)) = some j := hs.symm.trans hj
      cases hbad
    simpa only [normalizedSlotIdeal,hs] using inactive_whole_slot C Φ hsrc σ i ha y
  | some j =>
    have ha : ∀ x ∈ flatDomain Φ, x ∈ E.get i ↔ flatCoord Φ (σ (j.castAdd a)) x = 0 := by
      intro x hx
      constructor
      · intro hxi
        obtain ⟨j',hj',hz⟩ := (hm x hx i).mp hxi
        have hjj : j' = j := Option.some.inj (hj'.symm.trans hs)
        exact hjj ▸ hz
      · intro hz
        exact (hm x hx i).mpr ⟨j,hs,hz⟩
    simpa only [normalizedSlotIdeal,hs] using active_whole_slot C Φ hsrc σ i j ha y

/-- ORDINARY original native overlap/SNC/whole-old-slot data internally yield
both actual normalized analytic native windows and EVERY whole scalar calibration.
No normalized reader or calibration packet is a premise. -/
theorem exists_actual_normalized_native_windows {n₁ n₂ : ℕ} {M₁ : CMfd.{0} n₁} {M₂ : CMfd.{0} n₂}
    (C₁ : Set M₁) (C₂ : Set M₂)
    (e : actualSubspaceLocallyRingedSpace (n := n₁) C₁ ≅ actualSubspaceLocallyRingedSpace (n := n₂) C₂)
    (p₁ : C₁) {E₁ : List (Set M₁)} {E₂ : List (Set M₂)}
    (hE₁ : IsSNCDivisor n₁ E₁) (hE₂ : IsSNCDivisor n₂ E₂)
    (τ : Fin E₁.length ≃ Fin E₂.length)
    (hI : ∀ i : Fin E₁.length, Ideal.map (e.hom.stalkMap p₁).hom
      (actualLabelledBoundaryTraceIdeal C₂ E₂ (τ i) (e.hom.base p₁)) =
        actualLabelledBoundaryTraceIdeal C₁ E₁ i p₁)
    (hC₁ : IsComplexAnalyticSubset (n := n₁) C₁) (hC₂ : IsComplexAnalyticSubset (n := n₂) C₂) :
    ∃ R : RelativeReaders p₁.val (e.hom.base p₁).val E₁ E₂ τ,
      IsComplexAnalyticSubset (n := R.r+R.a) (normalizedCarrier C₁ R.Φ₁ R.hsrc₁ R.σ₁) ∧
      IsComplexAnalyticSubset (n := R.r+R.b) (normalizedCarrier C₂ R.Φ₂ R.hsrc₂ R.σ₂) ∧
      (∀ (y : normalizedCarrier C₁ R.Φ₁ R.hsrc₁ R.σ₁) (i : Fin E₁.length),
        Ideal.map ((normalizedWindowMap C₁ R.Φ₁ R.hsrc₁ R.σ₁).stalkMap y).hom
          (actualLabelledBoundaryTraceIdeal C₁ E₁ i ((normalizedWindowMap C₁ R.Φ₁ R.hsrc₁ R.σ₁).base y)) =
            normalizedSlotIdeal C₁ R.Φ₁ R.hsrc₁ R.σ₁ R.slot y i) ∧
      ∀ (y : normalizedCarrier C₂ R.Φ₂ R.hsrc₂ R.σ₂) (i : Fin E₂.length),
        Ideal.map ((normalizedWindowMap C₂ R.Φ₂ R.hsrc₂ R.σ₂).stalkMap y).hom
          (actualLabelledBoundaryTraceIdeal C₂ E₂ i ((normalizedWindowMap C₂ R.Φ₂ R.hsrc₂ R.σ₂).base y)) =
            normalizedSlotIdeal C₂ R.Φ₂ R.hsrc₂ R.σ₂ (fun i => R.slot (τ.symm i)) y i := by
  obtain ⟨R⟩ := exists_relative_readers C₁ C₂ e p₁ hE₁ hE₂ τ hI
  refine ⟨R,normalizedCarrier_analytic C₁ R.Φ₁ R.hsrc₁ R.σ₁ hC₁,
    normalizedCarrier_analytic C₂ R.Φ₂ R.hsrc₂ R.σ₂ hC₂,?_,?_⟩
  · intro y i
    exact whole_slot_calibration C₁ R.Φ₁ R.hsrc₁ R.σ₁ R.slot R.member₁ y i
  · intro y i
    apply whole_slot_calibration C₂ R.Φ₂ R.hsrc₂ R.σ₂ (fun i => R.slot (τ.symm i)) ?_ y i
    intro x hx j
    simpa only [τ.apply_symm_apply] using R.member₂ x hx (τ.symm j)

end
end SGPT.Unibranch.HironakaG1NormalizedSNCNativeWindows
