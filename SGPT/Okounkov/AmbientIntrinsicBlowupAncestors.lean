import SGPT.Okounkov.AmbientIntrinsicBlowupTower
import SGPT.Foundations.Analysis.Pending.HironakaAdmissibleCalculus

set_option autoImplicit false

noncomputable section

universe u v

namespace SGPT.Okounkov

open Set
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.RegularLocusDense
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open SGPT.Foundations.Analysis.Pending

/-- Empty interior in the actual smaller carrier produces density of the
same centre complement in every containing ancestor. -/
theorem ancestor_subset_closure_sdiff_of_subtype_thin
    {X : Type u} [TopologicalSpace X] {N A : Set X}
    (hNA : N ⊆ A) (C : Set N) (hCi : interior C = ∅) :
    A ⊆ closure (A \ Subtype.val '' C) := by
  have hNclosure : N ⊆ closure (N \ Subtype.val '' C) := by
    intro x hx
    let p : N := ⟨x, hx⟩
    have hp : p ∈ closure Cᶜ :=
      (interior_eq_empty_iff_dense_compl.mp hCi).closure_eq ▸ mem_univ p
    have himg : Subtype.val '' closure Cᶜ ⊆ closure (Subtype.val '' Cᶜ) :=
      image_closure_subset_closure_image continuous_subtype_val
    apply closure_mono ?_ (himg ⟨p, hp, rfl⟩)
    rintro y ⟨z, hz, rfl⟩
    refine ⟨z.2, ?_⟩
    rintro ⟨c, hc, hcz⟩
    exact hz (Subtype.val_injective hcz ▸ hc)
  intro x hx
  by_cases hxC : x ∈ Subtype.val '' C
  · obtain ⟨p, _, rfl⟩ := hxC
    exact closure_mono (sdiff_subset_sdiff_left hNA) (hNclosure p.2)
  · exact subset_closure ⟨hx, hxC⟩

/-- The actual one-step blowup preserves a closed smooth ancestor in its
literal exceptional-locus strict carrier, without relative thinness data
for that ancestor. -/
theorem regularAtDim_strictTransform_ancestor
    {n d : ℕ} {X Y : Type u}
    [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
    [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
    {N A : Set X} (hNA : N ⊆ A) (hAc : IsClosed A)
    (hA : ∀ x ∈ A, RegularAtDim (n := n) A x d)
    (C : Set N) (hCi : interior C = ∅) {a : Y → X}
    (ha : IsBlowupAlong n (Subtype.val '' C) a) :
    IsClosed (strictTransform n a A) ∧
      (∀ y ∈ strictTransform n a A,
        RegularAtDim (n := n) (strictTransform n a A) y d) ∧
      strictTransform n a A ⊆ a ⁻¹' A ∧
      strictTransform n a N ⊆ strictTransform n a A := by
  have hCA : Subtype.val '' C ⊆ A := by
    rintro x ⟨p, _, rfl⟩
    exact hNA p.2
  have heq := BlowupStrictIdeal.geoStrictTransform_eq_strictTransform ha
    (ancestor_subset_closure_sdiff_of_subtype_thin hNA C hCi)
  refine ⟨isClosed_closure, ?_,
    HironakaAdmissibleCalculus.strictTransform_subset_preimage ha.contMDiff.continuous hAc,
    HironakaAdmissibleCalculus.strictTransform_mono a hNA⟩
  rw [← heq]
  exact fun _ hy => BlowupStrictSubmanifold.regularAtDim_geoStrictTransform ha hAc hA hCA hy

/-- An actual finite intrinsic sequence is realized by one compact Kähler
ambient tower that manufactures the smoothness of every earlier ancestor.
The final projections are the literal inherited-atlas restrictions.
Original nested ancestor inclusions are retained simultaneously. -/
theorem exists_ambientRealization_of_intrinsicBlowupSequence_preservingAncestors
    {n k : ℕ} {X : Type u} [TopologicalSpace X]
    [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X] [CompactSpace X]
    (omegaX : KahlerBackground n X) {N : Set X} (hk : k ≤ n) (hNc : IsClosed N)
    (hN : ∀ x ∈ N, RegularAtDim (n := n) N x k)
    {I : Type v} (A : I → Set X) (d : I → ℕ) (hd : ∀ i, d i ≤ n)
    (hNA : ∀ i, N ⊆ A i) (hAc : ∀ i, IsClosed (A i))
    (hA : ∀ i, ∀ x ∈ A i, RegularAtDim (n := n) (A i) x (d i))
    {Nt : Type u} [TopologicalSpace Nt]
    [ChartedSpace (ComplexModel k) Nt] [IsComplexManifold k Nt]
    {q : Nt → N}
    (hq : letI := SubmanifoldChartedSpace.chartedSpace hk hN
      letI := SubmanifoldChartedSpace.isComplexManifold_chartedSpace hk hN
      IsBlowupSequence k N Nt q) :
    ∃ (Y : Type u) (_ : TopologicalSpace Y) (_ : ChartedSpace (ComplexModel n) Y)
      (_ : IsComplexManifold n Y) (_ : CompactSpace Y) (_ : KahlerBackground n Y)
      (p : Y → X) (S : Set Y) (hS : ∀ y ∈ S, RegularAtDim (n := n) S y k),
      IsBlowupSequence n X Y p ∧ IsClosed S ∧ S = strictTransform n p N ∧
      ∃ hA' : ∀ i, ∀ y ∈ strictTransform n p (A i),
          RegularAtDim (n := n) (strictTransform n p (A i)) y (d i),
        (letI := SubmanifoldChartedSpace.chartedSpace hk hN
         letI := SubmanifoldChartedSpace.chartedSpace hk hS
         ∃ (e : Nt → S) (f : S → Nt),
           ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel k) ∞ e ∧
           ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel k) ∞ f ∧
           f ∘ e = id ∧ e ∘ f = id ∧
           p ∘ ((Subtype.val : S → Y) ∘ e) = (Subtype.val : N → X) ∘ q) ∧
        (∀ i j, A i ⊆ A j → strictTransform n p (A i) ⊆ strictTransform n p (A j)) ∧
        ∀ i, IsClosed (strictTransform n p (A i)) ∧
          S ⊆ strictTransform n p (A i) ∧
          ∃ hi : ∀ y ∈ strictTransform n p (A i), p y ∈ A i,
            letI := SubmanifoldChartedSpace.chartedSpace (hd i) (hA i)
            letI := SubmanifoldChartedSpace.chartedSpace (hd i) (hA' i)
            let r : strictTransform n p (A i) → A i :=
              fun y => ⟨p y.1, hi y.1 y.2⟩
            ContMDiff 𝓘(ℂ, ComplexModel (d i)) 𝓘(ℂ, ComplexModel (d i)) ∞ r ∧
              IsProperMap r := by
  classical
  let := SubmanifoldChartedSpace.chartedSpace hk hN
  let := SubmanifoldChartedSpace.isComplexManifold_chartedSpace hk hN
  have hcore : ∃ (Y : Type u) (_ : TopologicalSpace Y)
      (_ : ChartedSpace (ComplexModel n) Y) (_ : IsComplexManifold n Y)
      (_ : CompactSpace Y) (_ : KahlerBackground n Y)
      (p : Y → X) (S : Set Y) (hS : ∀ y ∈ S, RegularAtDim (n := n) S y k),
      IsBlowupSequence n X Y p ∧ IsClosed S ∧ S = strictTransform n p N ∧
      (∀ i, ∀ y ∈ strictTransform n p (A i),
        RegularAtDim (n := n) (strictTransform n p (A i)) y (d i)) ∧
      letI := SubmanifoldChartedSpace.chartedSpace hk hN
      letI := SubmanifoldChartedSpace.chartedSpace hk hS
      ∃ (e : Nt → S) (f : S → Nt),
        ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel k) ∞ e ∧
        ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel k) ∞ f ∧
        f ∘ e = id ∧ e ∘ f = id ∧
        p ∘ ((Subtype.val : S → Y) ∘ e) = (Subtype.val : N → X) ∘ q := by
    induction hq with
    | refl =>
        have hid : ∀ B : Set X, IsClosed B → strictTransform n (id : X → X) B = B := by
          intro B hBc
          simp only [strictTransform, exceptionalLocus_id, preimage_id, sdiff_empty,
            hBc.closure_eq]
        refine ⟨X, inferInstance, inferInstance, inferInstance, inferInstance, omegaX,
          id, N, hN, IsBlowupSequence.refl, hNc, (hid N hNc).symm, ?_,
          id, id, contMDiff_id, contMDiff_id, rfl, rfl, rfl⟩
        intro i
        rw [hid (A i) (hAc i)]
        exact hA i
    | @step N0 N1 topN0 chartsN0 complexN0 topN1 chartsN1 complexN1 q0 C b _ hb ih =>
        obtain ⟨W0, topW0, chartsW0, complexW0, compactW0, omegaW0, p0, S0, hS0,
          hp0, hS0c, hS0strict, hA0, e0, f0, he0, hf0, hfe0, hef0, hcomm0⟩ := ih
        let := topW0
        let := chartsW0
        let := complexW0
        let := compactW0
        let := SubmanifoldChartedSpace.chartedSpace hk hS0
        let := SubmanifoldChartedSpace.isComplexManifold_chartedSpace hk hS0
        have hb' : IsBlowupAlong k (f0 ⁻¹' C) (e0 ∘ b) :=
          MarkedIdealBiholomorphism.isBlowupAlong_comp_inverse hf0 he0
            (fun z => congrFun hfe0 z) (fun z => congrFun hef0 z) hb
        obtain ⟨W1, topW1, chartsW1, complexW1, compactW1, omegaW1, a, S1, hS1,
          ha, _haSequence, hS1c, _hS1geo, hS1strict, _hi1,
          e1, f1, he1, hf1, _hre1, _hqf1, hfe1, hef1, _himage1, hcomm1⟩ :=
          exists_ambientRealization_of_intrinsicBlowup omegaW0 hk hS0c hS0 (f0 ⁻¹' C) hb'
        let := topW1
        let := chartsW1
        let := complexW1
        let := compactW1
        let := SubmanifoldChartedSpace.chartedSpace hk hS1
        let := SubmanifoldChartedSpace.isComplexManifold_chartedSpace hk hS1
        have hp1 : IsBlowupSequence n X W1 (p0 ∘ a) :=
          IsBlowupSequence.step p0 (Subtype.val '' (f0 ⁻¹' C)) a hp0 ha
        have hstrict : S1 = strictTransform n (p0 ∘ a) N := by
          rw [StrictTransformComposition.strictTransform_comp hp0.contMDiff ha.contMDiff N,
            ← hS0strict]
          exact hS1strict
        have hA1 : ∀ i, ∀ y ∈ strictTransform n (p0 ∘ a) (A i),
            RegularAtDim (n := n) (strictTransform n (p0 ∘ a) (A i)) y (d i) := by
          intro i
          have hS0A : S0 ⊆ strictTransform n p0 (A i) := by
            rw [hS0strict]
            exact HironakaAdmissibleCalculus.strictTransform_mono p0 (hNA i)
          have hreg := (regularAtDim_strictTransform_ancestor hS0A isClosed_closure
            (hA0 i) (f0 ⁻¹' C) hb'.2.1 ha).2.1
          rw [StrictTransformComposition.strictTransform_comp hp0.contMDiff ha.contMDiff (A i)]
          exact hreg
        have hcomm : (p0 ∘ a) ∘ ((Subtype.val : S1 → W1) ∘ e1) =
            (Subtype.val : N → X) ∘ (q0 ∘ b) := by
          calc
            (p0 ∘ a) ∘ ((Subtype.val : S1 → W1) ∘ e1) =
                p0 ∘ (a ∘ ((Subtype.val : S1 → W1) ∘ e1)) := rfl
            _ = p0 ∘ ((Subtype.val : S0 → W0) ∘ (e0 ∘ b)) :=
              congrArg (fun F => p0 ∘ F) hcomm1
            _ = (p0 ∘ ((Subtype.val : S0 → W0) ∘ e0)) ∘ b := rfl
            _ = (Subtype.val : N → X) ∘ (q0 ∘ b) :=
              congrArg (fun F => F ∘ b) hcomm0
        exact ⟨W1, topW1, chartsW1, complexW1, compactW1, omegaW1, p0 ∘ a, S1, hS1,
          hp1, hS1c, hstrict, hA1, e1, f1, he1, hf1, hfe1, hef1, hcomm⟩
  obtain ⟨Y, topY, chartsY, complexY, compactY, omegaY, p, S, hS,
    hp, hSc, hSstrict, hA', hcompare⟩ := hcore
  let := topY
  let := chartsY
  let := complexY
  let := compactY
  refine ⟨Y, topY, chartsY, complexY, compactY, omegaY, p, S, hS,
    hp, hSc, hSstrict, hA', hcompare,
    fun i j hij => HironakaAdmissibleCalculus.strictTransform_mono p hij, ?_⟩
  intro i
  have hSA : S ⊆ strictTransform n p (A i) := by
    rw [hSstrict]
    exact HironakaAdmissibleCalculus.strictTransform_mono p (hNA i)
  have hi : ∀ y ∈ strictTransform n p (A i), p y ∈ A i :=
    fun _ hy => HironakaAdmissibleCalculus.strictTransform_subset_preimage
      hp.contMDiff.continuous (hAc i) hy
  refine ⟨isClosed_closure, hSA, hi, ?_⟩
  let := SubmanifoldChartedSpace.chartedSpace (hd i) (hA i)
  let := SubmanifoldChartedSpace.chartedSpace (hd i) (hA' i)
  let : CompactSpace (strictTransform n p (A i)) :=
    isCompact_iff_compactSpace.mp isClosed_closure.isCompact
  have hr := SubmanifoldCodRestrict.contMDiff_restrictPreimage
    (hd i) (hA i) (hd i) (hA' i) hp.contMDiff hi
  exact ⟨hr, hr.continuous.isProperMap⟩

end SGPT.Okounkov
