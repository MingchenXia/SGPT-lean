import SGPT.Okounkov.ResolvedStrictTransformModification

set_option autoImplicit false

noncomputable section

universe u v

namespace SGPT.Okounkov

open Set
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending
open AnalyticModificationLocalDiscrepancy

/-- Transport the genuine resolved intrinsic restriction to the literal
comparison image D, retaining the ORIGINAL next smooth flag member H.
The modification of D is manufactured, not an assumed restriction record. -/
theorem isAnalyticModification_resolved_nextFlagRestriction
    {n k : ℕ} {M N Nt Y : Type u}
    [TopologicalSpace M] [ChartedSpace (ComplexModel k) M] [IsComplexManifold k M]
    [TopologicalSpace N] [ChartedSpace (ComplexModel k) N] [IsComplexManifold k N]
    [CompactSpace N]
    [TopologicalSpace Nt] [ChartedSpace (ComplexModel k) Nt] [IsComplexManifold k Nt]
    [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
    [CompactSpace Y]
    {g : N → M} (hg : IsAnalyticModification (n := k) g)
    (H : ClosedIrreducibleAnalyticSubvariety k M)
    (hH : IsClosedConnectedSubmanifold k H.carrier H.dim) (hHdim : H.dim + 1 = k)
    (V : ClosedIrreducibleAnalyticSubvariety k N)
    (hV : V.carrier = strictTransform k g H.carrier) (hdim : V.dim = H.dim)
    {q : Nt → N} (hq : IsBlowupSequence k N Nt q)
    (hres : EmbeddedResolution.IsEmbeddedResolution V q)
    {S : Set Y} (hk : k ≤ n) (hS : ∀ y ∈ S, RegularAtDim (n := n) S y k)
    {e : Nt → S} {f : S → Nt}
    (he : letI := SubmanifoldChartedSpace.chartedSpace hk hS
      ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel k) ∞ e)
    (hf : letI := SubmanifoldChartedSpace.chartedSpace hk hS
      ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel k) ∞ f)
    (hfe : f ∘ e = id) (hef : e ∘ f = id)
    {D : Set Y} (hD : IsClosedConnectedSubmanifold n D H.dim)
    (hDeq : D = ((Subtype.val : S → Y) ∘ e) '' strictTransform k q V.carrier) :
    ∃ hDS : D ⊆ S,
      ∃ hi : ∀ d : D, g (q (f ⟨d.1, hDS d.2⟩)) ∈ H.carrier,
        letI := SubmanifoldChartedSpace.chartedSpace H.dim_le hH.2.2
        letI := SubmanifoldChartedSpace.isComplexManifold_chartedSpace H.dim_le hH.2.2
        letI := SubmanifoldChartedSpace.chartedSpace
          (SubmanifoldChartedSpace.le_of_isClosedConnectedSubmanifold hD) hD.2.2
        letI := SubmanifoldChartedSpace.isComplexManifold_chartedSpace
          (SubmanifoldChartedSpace.le_of_isClosedConnectedSubmanifold hD) hD.2.2
        IsAnalyticModification (n := H.dim)
          (fun d : D => (⟨g (q (f ⟨d.1, hDS d.2⟩)), hi d⟩ : H.carrier)) := by
  classical
  let T := strictTransform k q V.carrier
  obtain ⟨hT, hTi, hTmod⟩ :=
    isAnalyticModification_resolvedStrictTransformRestriction hg H hH hHdim V hV hdim hq hres
  let hDn := SubmanifoldChartedSpace.le_of_isClosedConnectedSubmanifold hD
  let := SubmanifoldChartedSpace.chartedSpace hk hS
  let := SubmanifoldChartedSpace.isComplexManifold_chartedSpace hk hS
  let := SubmanifoldChartedSpace.chartedSpace H.dim_le hT
  let := SubmanifoldChartedSpace.isComplexManifold_chartedSpace H.dim_le hT
  let := SubmanifoldChartedSpace.chartedSpace hDn hD.2.2
  let := SubmanifoldChartedSpace.isComplexManifold_chartedSpace hDn hD.2.2
  let := SubmanifoldChartedSpace.chartedSpace H.dim_le hH.2.2
  let := SubmanifoldChartedSpace.isComplexManifold_chartedSpace H.dim_le hH.2.2
  let : CompactSpace D := isCompact_iff_compactSpace.mp hD.1.isCompact
  have hDS : D ⊆ S := by
    rw [hDeq]
    rintro y ⟨t, _, rfl⟩
    exact (e t).2
  have hfT : ∀ d : D, f ⟨d.1, hDS d.2⟩ ∈ T := by
    intro d
    obtain ⟨t, ht, htd⟩ := (show d.1 ∈ ((Subtype.val : S → Y) ∘ e) '' T from hDeq ▸ d.2)
    have hs : (⟨d.1, hDS d.2⟩ : S) = e t := Subtype.ext htd.symm
    rw [hs, show f (e t) = t from congrFun hfe t]
    exact ht
  have heD : ∀ t : T, (e t.1).1 ∈ D := fun t => hDeq.symm ▸ ⟨t.1, t.2, rfl⟩
  let a : D → T := fun d => ⟨f ⟨d.1, hDS d.2⟩, hfT d⟩
  let b : T → D := fun t => ⟨(e t.1).1, heD t⟩
  have hjDS : ContMDiff 𝓘(ℂ, ComplexModel H.dim) 𝓘(ℂ, ComplexModel k) ∞
      (fun d : D => (⟨d.1, hDS d.2⟩ : S)) :=
    SubmanifoldCodRestrict.contMDiff_codRestrict hk hS
      (SubmanifoldChartedSpace.contMDiff_val hDn hD.2.2) fun d => hDS d.2
  have ha : ContMDiff 𝓘(ℂ, ComplexModel H.dim) 𝓘(ℂ, ComplexModel H.dim) ∞ a :=
    SubmanifoldCodRestrict.contMDiff_codRestrict H.dim_le hT (hf.comp hjDS) hfT
  have hje : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞
      ((Subtype.val : S → Y) ∘ e) :=
    (SubmanifoldChartedSpace.contMDiff_val hk hS).comp he
  have hb : ContMDiff 𝓘(ℂ, ComplexModel H.dim) 𝓘(ℂ, ComplexModel H.dim) ∞ b :=
    SubmanifoldCodRestrict.contMDiff_codRestrict hDn hD.2.2
      (hje.comp (SubmanifoldChartedSpace.contMDiff_val H.dim_le hT)) heD
  have hab : ∀ t, a (b t) = t := by
    intro t
    apply Subtype.ext
    have hbt : (⟨(b t).1, hDS (b t).2⟩ : S) = e t.1 := Subtype.ext rfl
    change f (⟨(b t).1, hDS (b t).2⟩ : S) = t.1
    rw [hbt]
    exact congrFun hfe t.1
  have hba : ∀ d, b (a d) = d := by
    intro d
    apply Subtype.ext
    exact congrArg (fun s : S => s.1) (congrFun hef (⟨d.1, hDS d.2⟩ : S))
  have haMod : IsAnalyticModification (n := H.dim) a := by
    refine ⟨ha, ha.continuous.isProperMap, ∅, ∅, b,
      isClosed_empty, isComplexAnalyticSubset_empty, by simp,
      isClosed_empty, isComplexAnalyticSubset_empty, by simp, by simp,
      ?_, fun t _ => hab t, fun d _ => hba d⟩
    simpa only [compl_empty] using hb.contMDiffOn
  have hR := AnalyticModificationComposition.isAnalyticModification_comp hTmod haMod
  refine ⟨hDS, fun d => hTi (a d).1 (a d).2, ?_⟩
  exact hR

/-- One internally manufactured refinement retains all earlier ancestor
modifications and supplies the actual resolved restriction to the ORIGINAL
next flag member, using the same intrinsic resolution and ambient tower. -/
theorem exists_ambientAncestorTower_resolving_nextFlagMember
    {n k : ℕ} {X M : Type u} [TopologicalSpace X]
    [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X] [CompactSpace X]
    [TopologicalSpace M] [ChartedSpace (ComplexModel k) M] [IsComplexManifold k M]
    (omegaX : KahlerBackground n X) {N : Set X} (hk : k ≤ n) (hNc : IsClosed N)
    (hN : ∀ x ∈ N, RegularAtDim (n := n) N x k)
    {I : Type v} (A : I → Set X) (d : I → ℕ) (hd : ∀ i, d i ≤ n)
    (hNA : ∀ i, N ⊆ A i) (hAc : ∀ i, IsClosed (A i))
    (hA : ∀ i, ∀ x ∈ A i, RegularAtDim (n := n) (A i) x (d i))
    (g : N → M)
    (hg : letI := SubmanifoldChartedSpace.chartedSpace hk hN
      letI := SubmanifoldChartedSpace.isComplexManifold_chartedSpace hk hN
      IsAnalyticModification (n := k) g)
    (H : ClosedIrreducibleAnalyticSubvariety k M)
    (hH : IsClosedConnectedSubmanifold k H.carrier H.dim) (hHdim : H.dim + 1 = k) :
    letI := SubmanifoldChartedSpace.chartedSpace hk hN
    letI := SubmanifoldChartedSpace.isComplexManifold_chartedSpace hk hN
    ∃ V : ClosedIrreducibleAnalyticSubvariety k N,
      V.carrier = strictTransform k g H.carrier ∧ V.dim = H.dim ∧
      ∃ (Nt : Type u) (_ : TopologicalSpace Nt) (_ : ChartedSpace (ComplexModel k) Nt)
        (_ : IsComplexManifold k Nt) (q : Nt → N),
        IsBlowupSequence k N Nt q ∧ EmbeddedResolution.IsEmbeddedResolution V q ∧
        ∃ (Y : Type u) (_ : TopologicalSpace Y) (_ : ChartedSpace (ComplexModel n) Y)
          (_ : IsComplexManifold n Y) (_ : CompactSpace Y) (_ : KahlerBackground n Y)
          (p : Y → X) (S : Set Y) (hS : ∀ y ∈ S, RegularAtDim (n := n) S y k),
          IsBlowupSequence n X Y p ∧ IsClosed S ∧ S = strictTransform n p N ∧
          ∃ hA' : ∀ i, ∀ y ∈ strictTransform n p (A i),
              RegularAtDim (n := n) (strictTransform n p (A i)) y (d i),
            ((∀ i j, A i ⊆ A j → strictTransform n p (A i) ⊆ strictTransform n p (A j)) ∧
             ∀ i, IsClosed (strictTransform n p (A i)) ∧
               S ⊆ strictTransform n p (A i) ∧
               ∃ hi : ∀ y ∈ strictTransform n p (A i), p y ∈ A i,
                 letI := SubmanifoldChartedSpace.chartedSpace (hd i) (hA i)
                 letI := SubmanifoldChartedSpace.isComplexManifold_chartedSpace (hd i) (hA i)
                 letI := SubmanifoldChartedSpace.chartedSpace (hd i) (hA' i)
                 letI := SubmanifoldChartedSpace.isComplexManifold_chartedSpace (hd i) (hA' i)
                 IsAnalyticModification (n := d i)
                   (fun y : strictTransform n p (A i) => (⟨p y.1, hi y.1 y.2⟩ : A i))) ∧
            letI := SubmanifoldChartedSpace.chartedSpace hk hS
            ∃ (e : Nt → S) (f : S → Nt),
              ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel k) ∞ e ∧
              ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel k) ∞ f ∧
              f ∘ e = id ∧ e ∘ f = id ∧
              p ∘ ((Subtype.val : S → Y) ∘ e) = (Subtype.val : N → X) ∘ q ∧
              ∃ (D : Set Y) (hD : IsClosedConnectedSubmanifold n D H.dim),
                D = ((Subtype.val : S → Y) ∘ e) '' strictTransform k q V.carrier ∧
                p '' D = (Subtype.val : N → X) '' V.carrier ∧
                ∃ _hDS : D ⊆ S,
                  ∃ hPN : ∀ z ∈ D, p z ∈ N,
                  ∃ hi : ∀ z : D, g ⟨p z.1, hPN z.1 z.2⟩ ∈ H.carrier,
                    letI := SubmanifoldChartedSpace.chartedSpace H.dim_le hH.2.2
                    letI := SubmanifoldChartedSpace.isComplexManifold_chartedSpace H.dim_le hH.2.2
                    letI := SubmanifoldChartedSpace.chartedSpace
                      (SubmanifoldChartedSpace.le_of_isClosedConnectedSubmanifold hD) hD.2.2
                    letI := SubmanifoldChartedSpace.isComplexManifold_chartedSpace
                      (SubmanifoldChartedSpace.le_of_isClosedConnectedSubmanifold hD) hD.2.2
                    IsAnalyticModification (n := H.dim)
                      (fun z : D => (⟨g ⟨p z.1, hPN z.1 z.2⟩, hi z⟩ : H.carrier)) := by
  let := SubmanifoldChartedSpace.chartedSpace hk hN
  let := SubmanifoldChartedSpace.isComplexManifold_chartedSpace hk hN
  let : CompactSpace N := isCompact_iff_compactSpace.mp hNc.isCompact
  obtain ⟨V, hV, hdim, _, _⟩ :=
    AnalyticModificationDivisorStrictTransform.exists_strictTransform_reader hg H hHdim
  obtain ⟨Nt, topNt, chartsNt, complexNt, q, hq, hres,
    Y, topY, chartsY, complexY, compactY, omegaY, p, S, hS,
    hp, hSc, hSstrict, hA', ⟨hNest, hMods⟩,
    e, f, he, hf, hfe, hef, hcomm, D, hDraw, hDeq, _hDS, hpD⟩ :=
    exists_ambientAncestorTower_resolving_intrinsicDescendant omegaX hk hNc hN A d hd hNA hAc hA V
  let := topNt
  let := chartsNt
  let := complexNt
  let := topY
  let := chartsY
  let := complexY
  let := compactY
  have hD : IsClosedConnectedSubmanifold n D H.dim := by simpa only [hdim] using hDraw
  obtain ⟨hDS, hi, hR⟩ := isAnalyticModification_resolved_nextFlagRestriction
    hg H hH hHdim V hV hdim hq hres hk hS he hf hfe hef hD hDeq
  have hpS : ∀ s : S, p s.1 = (q (f s)).1 := by
    intro s
    calc
      p s.1 = p (e (f s)).1 :=
        congrArg (fun w : S => p w.1) (congrFun hef s).symm
      _ = (q (f s)).1 := congrFun hcomm (f s)
  have hPN : ∀ z ∈ D, p z ∈ N := fun z hz =>
    (hpS (⟨z, hDS hz⟩ : S)).symm ▸ (q (f ⟨z, hDS hz⟩)).2
  have hpoint : ∀ z : D, (⟨p z.1, hPN z.1 z.2⟩ : N) = q (f ⟨z.1, hDS z.2⟩) :=
    fun z => Subtype.ext (hpS ⟨z.1, hDS z.2⟩)
  have hiP : ∀ z : D, g ⟨p z.1, hPN z.1 z.2⟩ ∈ H.carrier := by
    intro z
    rw [hpoint z]
    exact hi z
  have hMap : (fun z : D => (⟨g ⟨p z.1, hPN z.1 z.2⟩, hiP z⟩ : H.carrier)) =
      (fun z : D => (⟨g (q (f ⟨z.1, hDS z.2⟩)), hi z⟩ : H.carrier)) := by
    funext z
    exact Subtype.ext (congrArg g (hpoint z))
  exact ⟨V, hV, hdim, Nt, topNt, chartsNt, complexNt, q, hq, hres,
    Y, topY, chartsY, complexY, compactY, omegaY, p, S, hS,
    hp, hSc, hSstrict, hA', ⟨hNest, hMods⟩, e, f, he, hf, hfe, hef, hcomm,
    D, hD, hDeq, hpD, hDS, hPN, hiP, hMap.symm ▸ hR⟩

end SGPT.Okounkov
