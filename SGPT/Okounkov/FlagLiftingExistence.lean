import SGPT.Okounkov.NativeFlagBaseGeometry
import SGPT.Okounkov.AmbientComparisonFlag

set_option autoImplicit false

noncomputable section

universe u

namespace SGPT.Okounkov

open Set
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending
open AnalyticModificationLocalDiscrepancy

/-- Actual full original flag existence above a native compact Kähler model.
Dimension induction uses the original tail and extends its SAME intrinsic
sequence to one ambient tower. No partial flag or lifting certificate is input. -/
theorem exists_flagLifting_dominating_nativeModel :
    ∀ (n : ℕ) (F : OriginalFlagGeometry.{u} n) (Z : Type u)
      [TopologicalSpace Z] [ChartedSpace (ComplexModel n) Z] [IsComplexManifold n Z]
      [CompactSpace Z] (_omegaZ : KahlerBackground n Z) (pi : Z → F.carrier),
      IsAnalyticModification (n := n) pi →
      ∃ (W : OriginalFlagGeometry.{u} n) (p : W.carrier → Z),
        IsBlowupSequence n Z W.carrier p ∧ IsFlagLifting F W (pi ∘ p) := by
  intro n
  induction n with
  | zero =>
      intro F Z topZ chartsZ complexZ compactZ omegaZ pi hpi
      let : ConnectedSpace Z := connectedSpace_source_of_isAnalyticModification hpi
      have hflag : IsSmoothFlag (fun _ : Fin 1 => (univ : Set Z)) := by
        refine ⟨rfl, fun _ _ _ => Subset.rfl, fun _ => ?_⟩
        refine ⟨isClosed_univ, isConnected_univ, fun z _ => ?_⟩
        simpa only [Nat.zero_sub] using AnalyticIrreducibleComponents.regularAtDim_univ z
      let W := OriginalFlagGeometry.ofOriginal omegaZ (fun _ : Fin 1 => univ) hflag
      refine ⟨W, id, IsBlowupSequence.refl, hpi, ?_⟩
      intro i
      have hi0 : i = (0 : Fin 1) := by apply Fin.ext; omega
      subst i
      obtain ⟨hi, hmod⟩ := isAnalyticModification_wholeSetRestriction hpi
        F.smooth.1 W.smooth.1 (F.smooth.2.2 0).2.2 (W.smooth.2.2 0).2.2
      exact ⟨hi, hmod⟩
  | succ m ih =>
      intro F Z topZ chartsZ complexZ compactZ omegaZ pi hpi
      obtain ⟨Y1, topY1, chartsY1, complexY1, compactY1, omegaY1, p1, hp1,
        D, hD, hiD, hR⟩ := exists_resolvedFirstFlagMember F omegaZ pi hpi
      let := topY1
      let := chartsY1
      let := complexY1
      let := compactY1
      let : ChartedSpace (ComplexModel m) (F.flag (1 : Fin (m + 2))) := F.tail.charts
      let : IsComplexManifold m (F.flag (1 : Fin (m + 2))) := F.tail.complex
      let := SubmanifoldChartedSpace.chartedSpace (Nat.le_succ m) hD.2.2
      let := SubmanifoldChartedSpace.isComplexManifold_chartedSpace (Nat.le_succ m) hD.2.2
      let : CompactSpace D := isCompact_iff_compactSpace.mp hD.1.isCompact
      let omegaD := SubmanifoldKahlerRestriction.kahlerBackground (Nat.le_succ m) hD.2.2 omegaY1
      let R : D → F.tail.carrier := fun d => ⟨pi (p1 d.1), hiD d.1 d.2⟩
      obtain ⟨G, q, hq, hRq⟩ := ih F.tail D omegaD R hR
      obtain ⟨Y2, topY2, chartsY2, complexY2, compactY2, omegaY2, p2, S, hS,
        hp2, hSc, _hSstrict, e, f, he, hf, hfe, hef, hcomm⟩ :=
        exists_ambientRealization_of_intrinsicBlowupSequence omegaY1
          (Nat.le_succ m) hD.1 hD.2.2 hq
      let := topY2
      let := chartsY2
      let := complexY2
      let := compactY2
      let := SubmanifoldChartedSpace.chartedSpace (Nat.le_succ m) hS
      let := SubmanifoldChartedSpace.isComplexManifold_chartedSpace (Nat.le_succ m) hS
      let p := p1 ∘ p2
      have hp : IsBlowupSequence (m + 1) Z Y2 p := isBlowupSequence_comp_nativeFlag hp1 hp2
      let gamma := pi ∘ p
      have hgamma : IsAnalyticModification (n := m + 1) gamma :=
        AnalyticModificationComposition.isAnalyticModification_comp hpi
          (isAnalyticModification_of_finiteBlowupSequence hp)
      let : ConnectedSpace Y2 := connectedSpace_source_of_isAnalyticModification hgamma
      let W := OriginalFlagGeometry.ofOriginal omegaY2 (comparisonImageFlag G S e)
        (isSmoothFlag_comparisonImageFlag G hSc hS he hf hfe hef)
      refine ⟨W, p, hp, hgamma, ?_⟩
      intro i
      cases i using Fin.cases with
      | zero =>
        obtain ⟨hi, hmod⟩ := isAnalyticModification_wholeSetRestriction hgamma
          F.smooth.1 W.smooth.1 (F.smooth.2.2 0).2.2 (W.smooth.2.2 0).2.2
        exact ⟨hi, hmod⟩
      | succ i =>
        obtain ⟨hiG, hmodG⟩ := hRq.2 i
        have hCi : IsClosedConnectedSubmanifold (m + 1) (W.flag i.succ) (m - (i : ℕ)) :=
          by simpa only [Fin.val_succ, Nat.add_sub_add_right] using W.smooth.2.2 i.succ
        let := F.tail.componentCharts i
        let := F.tail.componentComplex i
        let := G.componentCharts i
        let := G.componentComplex i
        let := F.shiftedComponentCharts i
        let := F.shiftedComponentComplex i
        let := W.shiftedComponentCharts i
        let := W.shiftedComponentComplex i
        let : CompactSpace (W.flag i.succ) := isCompact_iff_compactSpace.mp hCi.1.isCompact
        let c : W.flag i.succ ≃ₜ G.flag i :=
          comparisonImageHomeomorph S e f he.continuous hf.continuous hfe hef (G.flag i)
        have hc : ContMDiff 𝓘(ℂ, ComplexModel (m - (i : ℕ)))
            𝓘(ℂ, ComplexModel (m - (i : ℕ))) ∞ c :=
          contMDiff_comparisonImageHomeomorph (Nat.le_succ m) hS he hf hfe hef
            (G.smooth.2.2 i) hCi
        have hci : ContMDiff 𝓘(ℂ, ComplexModel (m - (i : ℕ)))
            𝓘(ℂ, ComplexModel (m - (i : ℕ))) ∞ c.symm :=
          contMDiff_comparisonImageHomeomorph_symm (Nat.le_succ m) hS he hf hfe hef
            (G.smooth.2.2 i) hCi
        have htransport := isAnalyticModification_biholomorphic_transport
          (F.tailComponentHomeomorph i).symm c
          (F.contMDiff_tailComponentHomeomorph_symm i)
          (F.contMDiff_tailComponentHomeomorph i) hc hci hmodG
        have hpoint : ∀ z : W.flag i.succ,
            gamma z.1 = (R (q (c z).1)).1 := by
          intro z
          have hecz : (e (c z).1).1 = z.1 :=
            congrArg (fun w : W.flag i.succ => w.1) (c.symm_apply_apply z)
          calc
            gamma z.1 = pi (p1 (p2 (e (c z).1).1)) :=
              congrArg (fun y : Y2 => gamma y) hecz.symm
            _ = (R (q (c z).1)).1 :=
              congrArg (fun y : Y1 => pi (p1 y)) (congrFun hcomm (c z).1)
        have hi : MapsTo gamma (W.flag i.succ) (F.flag i.succ) := by
          intro z hz
          have h := hiG (c (⟨z, hz⟩ : W.flag i.succ)).2
          change (R (q (c (⟨z, hz⟩ : W.flag i.succ)).1)).1 ∈ F.flag i.succ at h
          exact (hpoint ⟨z, hz⟩).symm ▸ h
        refine ⟨hi, ?_⟩
        have hMap : flagComponentMap F W gamma i.succ hi =
            (F.tailComponentHomeomorph i) ∘
              flagComponentMap F.tail G (R ∘ q) i hiG ∘ c := by
          funext z
          exact Subtype.ext (hpoint z)
        have hmodShift : IsAnalyticModification (n := m - (i : ℕ))
            (flagComponentMap F W gamma i.succ hi) := hMap.symm ▸ htransport
        have hFe : ∀ x ∈ F.flag i.succ,
            RegularAtDim (n := m + 1) (F.flag i.succ) x (m - (i : ℕ)) :=
          by simpa only [Fin.val_succ, Nat.add_sub_add_right] using (F.smooth.2.2 i.succ).2.2
        have hWe : ∀ x ∈ W.flag i.succ,
            RegularAtDim (n := m + 1) (W.flag i.succ) x (m - (i : ℕ)) :=
          by simpa only [Fin.val_succ, Nat.add_sub_add_right] using (W.smooth.2.2 i.succ).2.2
        exact (isAnalyticModification_inherited_dimension_congr
          (show m + 1 - (i.succ : ℕ) = m - (i : ℕ) by simp)
          (Nat.sub_le (m + 1) (i.succ : ℕ)) ((Nat.sub_le m i).trans (Nat.le_succ m))
          (F.smooth.2.2 i.succ).2.2 (W.smooth.2.2 i.succ).2.2 hFe hWe
          (flagComponentMap F W gamma i.succ hi)).mpr hmodShift

/-- For the book's finite smooth-centre initial modification, the literal
composite is itself finite, with a full original flag lifting. Compactness
and a Kähler background on the SAME initial model are internally derived. -/
theorem exists_flagLifting_dominating_finiteNativeModification
    {n : ℕ} (F : OriginalFlagGeometry.{u} n) (Z : Type u)
    [TopologicalSpace Z] [ChartedSpace (ComplexModel n) Z] [IsComplexManifold n Z]
    (pi : Z → F.carrier) (hpi : IsBlowupSequence n F.carrier Z pi) :
    ∃ (W : OriginalFlagGeometry.{u} n) (p : W.carrier → Z),
      IsBlowupSequence n Z W.carrier p ∧
      IsBlowupSequence n F.carrier W.carrier (pi ∘ p) ∧ IsFlagLifting F W (pi ∘ p) := by
  obtain ⟨compactZ, ⟨omegaZ⟩⟩ :=
    LocusProperties.compactSpace_and_kahler_of_isBlowupSequence ⟨F.omega⟩ pi hpi
  let := compactZ
  obtain ⟨W, p, hp, hLift⟩ := exists_flagLifting_dominating_nativeModel n F Z omegaZ pi
    (isAnalyticModification_of_finiteBlowupSequence hpi)
  exact ⟨W, p, hp, isBlowupSequence_comp_nativeFlag hpi hp, hLift⟩

end SGPT.Okounkov
