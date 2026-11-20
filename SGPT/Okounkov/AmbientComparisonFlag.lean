import SGPT.Okounkov.ResolvedDescendantTransport
import SGPT.Okounkov.FlagLiftingTail

set_option autoImplicit false

noncomputable section

universe u

namespace SGPT.Okounkov

open Set
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open SGPT.Foundations.Analysis.Pending

/-- Literal comparison-image component homeomorphism, using the actual
subtype topologies and the manufactured whole inverse comparisons. -/
def comparisonImageHomeomorph
    {Y Nt : Type u} [TopologicalSpace Y] [TopologicalSpace Nt]
    (S : Set Y) (e : Nt → S) (f : S → Nt) (he : Continuous e) (hf : Continuous f)
    (hfe : f ∘ e = id) (hef : e ∘ f = id) (T : Set Nt) :
    (((Subtype.val : S → Y) ∘ e) '' T : Set Y) ≃ₜ T := by
  let D := ((Subtype.val : S → Y) ∘ e) '' T
  have hDS : D ⊆ S := by
    rintro y ⟨t, _, rfl⟩
    exact (e t).2
  have hfT : ∀ d : D, f ⟨d.1, hDS d.2⟩ ∈ T := by
    intro d
    obtain ⟨t, ht, htd⟩ := d.2
    have hs : (⟨d.1, hDS d.2⟩ : S) = e t := Subtype.ext htd.symm
    rw [hs, show f (e t) = t from congrFun hfe t]
    exact ht
  exact {
    toFun := fun d => ⟨f ⟨d.1, hDS d.2⟩, hfT d⟩
    invFun := fun t => ⟨(e t.1).1, ⟨t.1, t.2, rfl⟩⟩
    left_inv := fun d => Subtype.ext
      (congrArg (fun s : S => s.1) (congrFun hef (⟨d.1, hDS d.2⟩ : S)))
    right_inv := fun t => Subtype.ext (congrFun hfe t.1)
    continuous_toFun := (hf.comp (continuous_subtype_val.subtype_mk _)).subtype_mk _
    continuous_invFun :=
      ((continuous_subtype_val.comp he).comp continuous_subtype_val).subtype_mk _ }

theorem contMDiff_comparisonImageHomeomorph
    {n k l : ℕ} {Y Nt : Type u}
    [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
    [TopologicalSpace Nt] [ChartedSpace (ComplexModel k) Nt] [IsComplexManifold k Nt]
    {S : Set Y} (hk : k ≤ n) (hS : ∀ y ∈ S, RegularAtDim (n := n) S y k)
    {e : Nt → S} {f : S → Nt}
    (he : letI := SubmanifoldChartedSpace.chartedSpace hk hS
      ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel k) ∞ e)
    (hf : letI := SubmanifoldChartedSpace.chartedSpace hk hS
      ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel k) ∞ f)
    (hfe : f ∘ e = id) (hef : e ∘ f = id) {T : Set Nt}
    (hT : IsClosedConnectedSubmanifold k T l)
    (hD : IsClosedConnectedSubmanifold n (((Subtype.val : S → Y) ∘ e) '' T) l) :
    letI := SubmanifoldChartedSpace.chartedSpace hk hS
    letI := SubmanifoldChartedSpace.chartedSpace
      (SubmanifoldChartedSpace.le_of_isClosedConnectedSubmanifold hT) hT.2.2
    letI := SubmanifoldChartedSpace.chartedSpace
      (SubmanifoldChartedSpace.le_of_isClosedConnectedSubmanifold hD) hD.2.2
    ContMDiff 𝓘(ℂ, ComplexModel l) 𝓘(ℂ, ComplexModel l) ∞
      (comparisonImageHomeomorph S e f he.continuous hf.continuous hfe hef T) := by
  let hTk := SubmanifoldChartedSpace.le_of_isClosedConnectedSubmanifold hT
  let hDn := SubmanifoldChartedSpace.le_of_isClosedConnectedSubmanifold hD
  let := SubmanifoldChartedSpace.chartedSpace hk hS
  let := SubmanifoldChartedSpace.isComplexManifold_chartedSpace hk hS
  let := SubmanifoldChartedSpace.chartedSpace hTk hT.2.2
  let := SubmanifoldChartedSpace.isComplexManifold_chartedSpace hTk hT.2.2
  let := SubmanifoldChartedSpace.chartedSpace hDn hD.2.2
  let := SubmanifoldChartedSpace.isComplexManifold_chartedSpace hDn hD.2.2
  let a := comparisonImageHomeomorph S e f he.continuous hf.continuous hfe hef T
  have hDS : (((Subtype.val : S → Y) ∘ e) '' T) ⊆ S := by
    rintro y ⟨t, _, rfl⟩
    exact (e t).2
  have hj : ContMDiff 𝓘(ℂ, ComplexModel l) 𝓘(ℂ, ComplexModel k) ∞
      (fun d : ((Subtype.val : S → Y) ∘ e) '' T => (⟨d.1, hDS d.2⟩ : S)) :=
    SubmanifoldCodRestrict.contMDiff_codRestrict hk hS
      (SubmanifoldChartedSpace.contMDiff_val hDn hD.2.2) fun d => hDS d.2
  exact SubmanifoldCodRestrict.contMDiff_codRestrict hTk hT.2.2 (hf.comp hj) (fun d => (a d).2)

theorem contMDiff_comparisonImageHomeomorph_symm
    {n k l : ℕ} {Y Nt : Type u}
    [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
    [TopologicalSpace Nt] [ChartedSpace (ComplexModel k) Nt] [IsComplexManifold k Nt]
    {S : Set Y} (hk : k ≤ n) (hS : ∀ y ∈ S, RegularAtDim (n := n) S y k)
    {e : Nt → S} {f : S → Nt}
    (he : letI := SubmanifoldChartedSpace.chartedSpace hk hS
      ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel k) ∞ e)
    (hf : letI := SubmanifoldChartedSpace.chartedSpace hk hS
      ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel k) ∞ f)
    (hfe : f ∘ e = id) (hef : e ∘ f = id) {T : Set Nt}
    (hT : IsClosedConnectedSubmanifold k T l)
    (hD : IsClosedConnectedSubmanifold n (((Subtype.val : S → Y) ∘ e) '' T) l) :
    letI := SubmanifoldChartedSpace.chartedSpace hk hS
    letI := SubmanifoldChartedSpace.chartedSpace
      (SubmanifoldChartedSpace.le_of_isClosedConnectedSubmanifold hT) hT.2.2
    letI := SubmanifoldChartedSpace.chartedSpace
      (SubmanifoldChartedSpace.le_of_isClosedConnectedSubmanifold hD) hD.2.2
    ContMDiff 𝓘(ℂ, ComplexModel l) 𝓘(ℂ, ComplexModel l) ∞
      (comparisonImageHomeomorph S e f he.continuous hf.continuous hfe hef T).symm := by
  let hTk := SubmanifoldChartedSpace.le_of_isClosedConnectedSubmanifold hT
  let hDn := SubmanifoldChartedSpace.le_of_isClosedConnectedSubmanifold hD
  let := SubmanifoldChartedSpace.chartedSpace hk hS
  let := SubmanifoldChartedSpace.isComplexManifold_chartedSpace hk hS
  let := SubmanifoldChartedSpace.chartedSpace hTk hT.2.2
  let := SubmanifoldChartedSpace.isComplexManifold_chartedSpace hTk hT.2.2
  let := SubmanifoldChartedSpace.chartedSpace hDn hD.2.2
  let := SubmanifoldChartedSpace.isComplexManifold_chartedSpace hDn hD.2.2
  have hje : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞
      ((Subtype.val : S → Y) ∘ e) := (SubmanifoldChartedSpace.contMDiff_val hk hS).comp he
  exact SubmanifoldCodRestrict.contMDiff_codRestrict hDn hD.2.2
    (hje.comp (SubmanifoldChartedSpace.contMDiff_val hTk hT.2.2)) (fun t => ⟨t.1, t.2, rfl⟩)

def comparisonImageFlag {m : ℕ} (G : OriginalFlagGeometry.{u} m)
    {Y : Type u} [TopologicalSpace Y] (S : Set Y) (e : G.carrier → S) :
    Fin (m + 2) → Set Y :=
  Fin.cons univ (fun i => ((Subtype.val : S → Y) ∘ e) '' G.flag i)

theorem isSmoothFlag_comparisonImageFlag
    {m : ℕ} (G : OriginalFlagGeometry.{u} m)
    {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel (m + 1)) Y]
    [IsComplexManifold (m + 1) Y] [ConnectedSpace Y]
    {S : Set Y} (hSc : IsClosed S) (hS : ∀ y ∈ S, RegularAtDim (n := m + 1) S y m)
    {e : G.carrier → S} {f : S → G.carrier}
    (he : letI := SubmanifoldChartedSpace.chartedSpace (Nat.le_succ m) hS
      ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel m) ∞ e)
    (hf : letI := SubmanifoldChartedSpace.chartedSpace (Nat.le_succ m) hS
      ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel m) ∞ f)
    (hfe : f ∘ e = id) (hef : e ∘ f = id) :
    IsSmoothFlag (comparisonImageFlag G S e) := by
  refine ⟨rfl, ?_, ?_⟩
  · intro i j hij
    cases i using Fin.cases with
    | zero => exact subset_univ _
    | succ i =>
      cases j using Fin.cases with
      | zero =>
        change (i : ℕ) + 1 ≤ 0 at hij
        exact False.elim (by omega)
      | succ j =>
        exact image_mono (G.smooth.2.1 (Fin.succ_le_succ_iff.mp hij))
  · intro i
    cases i using Fin.cases with
    | zero =>
      exact ⟨isClosed_univ, isConnected_univ,
        fun y _ => AnalyticIrreducibleComponents.regularAtDim_univ y⟩
    | succ i =>
      have hD := (isClosedConnectedSubmanifold_descendantComparisonImage
        (Nat.le_succ m) hSc hS he hf hfe hef (G.smooth.2.2 i)).1
      simpa [comparisonImageFlag] using hD

theorem comparisonImageFlag_first_eq
    {m : ℕ} (G : OriginalFlagGeometry.{u} m)
    {Y : Type u} [TopologicalSpace Y] (S : Set Y)
    (e : G.carrier → S) (f : S → G.carrier) (hef : e ∘ f = id) :
    comparisonImageFlag G S e (1 : Fin (m + 2)) = S := by
  change ((Subtype.val : S → Y) ∘ e) '' G.flag 0 = S
  rw [G.smooth.1]
  ext y
  constructor
  · rintro ⟨t, _, rfl⟩
    exact (e t).2
  · intro hy
    exact ⟨f ⟨y, hy⟩, mem_univ _,
      congrArg (fun s : S => s.1) (congrFun hef (⟨y, hy⟩ : S))⟩

end SGPT.Okounkov
