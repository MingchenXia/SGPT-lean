import SGPT.Foundations.Analysis.Pending.FixedGermNormalOrder


set_option autoImplicit false
noncomputable section

open Set Filter
open scoped Topology Manifold ContDiff

namespace SGPT.Foundations.Analysis.Pending.UnramifiedNormalOrder

open Set Filter
open scoped Topology Manifold ContDiff
open FirstPass FirstPass.HolomorphicIdealSheaves FirstPass.BlowupSequences
  DemaillyApproximantDivisorialLelong HironakaHolomorphicJetRankLoci
  HironakaHolomorphicJetChartInvariance HironakaSmoothCentreNearbyStalks
  FixedGermNormalOrder

universe u

variable {m : ℕ} {Y Z : Type u}
  [TopologicalSpace Y] [ChartedSpace (ComplexModel (m + 1)) Y] [IsComplexManifold (m + 1) Y]
  [TopologicalSpace Z] [ChartedSpace (ComplexModel (m + 1)) Z] [IsComplexManifold (m + 1) Z]

/-- Actual IFT geometry and the SAME original local carriers manufacture the natural order covariance. -/
theorem functionNormalOrder_comp_eq_of_not_exceptional
    {g : Z → Y}
    (hg : ContMDiff 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel (m + 1)) ∞ g)
    {z : Z} (hz : z ∉ exceptionalLocus (m + 1) g)
    {E : Set Y} {E' : Set Z}
    (Φ : DivisorFlattening (m := m) E (g z)) (Ψ : DivisorFlattening (m := m) E' z)
    (hsets : ∀ᶠ z' in 𝓝 z, z' ∈ E' ↔ g z' ∈ E)
    (f : Y → ℂ) (hf : HolomorphicAt (m + 1) f (g z)) :
    functionNormalOrder Ψ (f ∘ g)
      (hf.comp_contMDiff (Eventually.of_forall fun _ => hg.contMDiffAt)) =
        functionNormalOrder Φ f hf := by
  classical
  obtain ⟨O, hAO, hO, hzO⟩ := eventually_nhds_iff.mp hsets
  let I := 𝓘(ℂ, ComplexModel (m + 1))
  have hrange : range I = univ := by simp [I]
  let e := (complexChartAt (n := m + 1) z).val
  let d := (complexChartAt (n := m + 1) (g z)).val
  let F : ComplexModel (m + 1) → ComplexModel (m + 1) := fun u => d (g (e.symm u))
  let N : Set (ComplexModel (m + 1)) := e.target ∩ e.symm ⁻¹' (O ∩ g ⁻¹' d.source)
  have hNo : IsOpen N :=
    e.continuousOn_symm.isOpen_inter_preimage e.open_target
      (hO.inter (hg.continuous.isOpen_preimage _ d.open_source))
  have hzN : e z ∈ N := ⟨e.map_source (mem_complexChartAt_source z), by
    rw [mem_preimage, e.left_inv (mem_complexChartAt_source z)]
    exact ⟨hzO, mem_complexChartAt_source (g z)⟩⟩
  have hFN : DifferentiableOn ℂ F N := by
    have h := (contMDiffOn_iff.mp (hg.contMDiffOn (s := univ))).2 z (g z)
    refine (h.differentiableOn (by simp)).mono ?_
    intro u hu
    exact ⟨⟨mem_univ _, hu.1⟩, mem_univ _, hu.2.2, mem_univ _⟩
  have hmd : MDifferentiableAt I I g z := (hg z).mdifferentiableAt (by simp)
  have hderiv : mfderiv I I g z = fderiv ℂ F (e z) := by
    rw [hmd.mfderiv, hrange, fderivWithin_univ]
    rfl
  have hinj : Function.Injective (fderiv ℂ F (e z)) := by
    have hbij := hz
    simp only [exceptionalLocus, mem_ofPred_eq, not_not] at hbij
    rw [hderiv] at hbij
    exact hbij.1
  obtain ⟨Ξ, hΞN, hΞF, _⟩ := exists_localHolomorphicEquivAt hNo hzN hFN hinj
  have hFz : F (e z) = d (g z) := by
    simp only [F, e.left_inv (mem_complexChartAt_source z)]
  have hΞp : Ξ.toFun (e z) = d (g z) := by
    rw [hΞF]
    exact hFz
  let Θ : DivisorFlattening (m := m) E' z := {
    Φ := RegularAtDimTransport.LocalHolomorphicEquivAt.comp Ξ Φ.Φ hΞp
    source_subset := fun u hu => (hΞN hu.1).1
    map_center := by
      change Φ.Φ.toFun (Ξ.toFun (e z)) = 0
      rw [hΞp]
      exact Φ.map_center
    mem_iff := by
      intro w hw hwΘ
      change e w ∈ Ξ.source ∩ Ξ.toFun ⁻¹' Φ.Φ.source at hwΘ
      have hwN := (hΞN hwΘ.1).2
      change e.symm (e w) ∈ O ∩ g ⁻¹' d.source at hwN
      rw [e.left_inv hw] at hwN
      have hFw : F (e w) = d (g w) := by
        simp only [F, e.left_inv hw]
      have hwΦ : d (g w) ∈ Φ.Φ.source := by
        have h := hwΘ.2
        rwa [mem_preimage, hΞF, hFw] at h
      change w ∈ E' ↔ Φ.Φ.toFun (Ξ.toFun (e w)) (Fin.last m) = 0
      rw [hΞF, hFw]
      exact (hAO w hwN.1).trans (Φ.mem_iff (g w) hwN.2 hwΦ) }
  have hqT : d (g z) ∈ Ξ.target := by
    rw [← hΞp]
    exact Ξ.mapsTo_toFun Ξ.center_mem_source
  have hΞinv : Ξ.invFun (d (g z)) = e z := by
    rw [← hΞp]
    exact Ξ.left_inv _ Ξ.center_mem_source
  let ξ := actualNearbyEquiv Ξ (d (g z)) hqT
  have hξ0 : ξ.toFun 0 = 0 := actualNearbyEquiv_zero Ξ (d (g z)) hqT
  let α := localGermAlgEquiv ξ hξ0
  have hequation : α (divisorEquationGerm Φ) = divisorEquationGerm Θ := by
    unfold divisorEquationGerm
    change localGermAlgEquiv ξ hξ0 (HolGerm.mk _ _) = HolGerm.mk _ _
    rw [localGermAlgEquiv_mk]
    apply HolGerm.mk_eq_mk_iff.mpr
    exact Eventually.of_forall fun w => by
      change Φ.Φ.toFun ((Ξ.toFun (w + Ξ.invFun (d (g z))) - d (g z)) + d (g z))
        (Fin.last m) = Φ.Φ.toFun (Ξ.toFun (w + e z)) (Fin.last m)
      rw [sub_add_cancel, hΞinv]
  have hfcomp : HolomorphicAt (m + 1) (f ∘ g) z :=
    hf.comp_contMDiff (Eventually.of_forall fun _ => hg.contMDiffAt)
  have hfunction :
      α (chartTranslatedGerm (g z) (g z) (mem_chart_source _ (g z)) f hf) =
        chartTranslatedGerm z z (mem_chart_source _ z) (f ∘ g) hfcomp := by
    unfold chartTranslatedGerm translatedGerm
    change localGermAlgEquiv ξ hξ0 (HolGerm.mk _ _) = HolGerm.mk _ _
    rw [localGermAlgEquiv_mk]
    apply HolGerm.mk_eq_mk_iff.mpr
    have ht : Tendsto (fun w : ComplexModel (m + 1) => w + e z) (𝓝 0) (𝓝 (e z)) := by
      simpa only [zero_add] using (continuous_add_const (e z)).tendsto 0
    filter_upwards [ht.eventually (Ξ.isOpen_source.mem_nhds Ξ.center_mem_source)] with w hw
    have hwN := hΞN hw
    change f (d.symm ((Ξ.toFun (w + Ξ.invFun (d (g z))) - d (g z)) + d (g z))) =
      f (g (e.symm (w + e z)))
    rw [sub_add_cancel, hΞinv, hΞF]
    exact congrArg f (d.left_inv hwN.2.2)
  calc
    functionNormalOrder Ψ (f ∘ g) hfcomp = functionNormalOrder Θ (f ∘ g) hfcomp :=
      normalOrder_independent Ψ Θ _
    _ = functionNormalOrder Φ f hf := by
      change emultiplicity (divisorEquationGerm Θ)
        (chartTranslatedGerm z z (mem_chart_source _ z) (f ∘ g) hfcomp) =
          emultiplicity (divisorEquationGerm Φ)
            (chartTranslatedGerm (g z) (g z) (mem_chart_source _ (g z)) f hf)
      rw [← hequation, ← hfunction]
      exact emultiplicity_map_eq α

end SGPT.Foundations.Analysis.Pending.UnramifiedNormalOrder
