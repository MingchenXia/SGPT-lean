import SGPT.Okounkov.ResolvedDescendantTransport
import SGPT.Foundations.Analysis.Pending.AnalyticModificationDivisorStrictTransform
import SGPT.Foundations.Analysis.FirstPass.AnalyticSubsetTopology

set_option autoImplicit false

noncomputable section

universe u

namespace SGPT.Okounkov

open Set Filter
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.Pending
open AnalyticModificationLocalDiscrepancy

/-- The actual inverse over a genuine open isomorphism locus is holomorphic:
the unramified local inverse and whole injectivity identify its local germs. -/
theorem contMDiffOn_invOver_of_isIsomorphismOver
    {k : ℕ} {M Z : Type u}
    [TopologicalSpace M] [ChartedSpace (ComplexModel k) M] [IsComplexManifold k M]
    [TopologicalSpace Z] [ChartedSpace (ComplexModel k) Z] [IsComplexManifold k Z]
    [Nonempty Z] {F : Z → M} {O : Set M}
    (hF : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel k) ∞ F)
    (hO : IsOpen O) (hiso : IsIsomorphismOver k F O) :
    ContMDiffOn 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel k) ∞
      (ModificationMassInvariance.invOver F O) O := by
  intro x hx
  obtain ⟨hzO, hzx⟩ := ModificationMassInvariance.invOver_mem hiso hx
  have hz : ModificationMassInvariance.invOver F O x ∉ exceptionalLocus k F :=
    fun h => disjoint_left.mp hiso.2 hzO h
  obtain ⟨U, s, hU, hxU, _, hFs, hs, _⟩ :=
    HolomorphicLocalInverse.exists_localInverse hF hz
  rw [hzx] at hxU
  have heq : s =ᶠ[𝓝 x] ModificationMassInvariance.invOver F O := by
    filter_upwards [hU.mem_nhds hxU, hO.mem_nhds hx] with y hyU hyO
    have hsy : s y ∈ F ⁻¹' O := by
      change F (s y) ∈ O
      rwa [hFs y hyU]
    calc
      s y = ModificationMassInvariance.invOver F O (F (s y)) :=
        (ModificationMassInvariance.invOver_apply hiso hsy).symm
      _ = ModificationMassInvariance.invOver F O y := by rw [hFs y hyU]
  exact ((hs x hxU).congr_of_eventuallyEq heq.symm).contMDiffWithinAt

/-- The intrinsic strict transform is regular wherever the actual preceding
modification is unramified; its singular locus projects into the canonical
intrinsic exceptional image, with the original target carrier retained. -/
theorem singularLocus_strictTransform_subset_preimage_exceptionalImage
    {k l : ℕ} {M N : Type u}
    [TopologicalSpace M] [ChartedSpace (ComplexModel k) M] [IsComplexManifold k M]
    [TopologicalSpace N] [ChartedSpace (ComplexModel k) N] [IsComplexManifold k N]
    {g : N → M} (hg : IsAnalyticModification (n := k) g)
    (H : ClosedIrreducibleAnalyticSubvariety k M)
    (hH : IsClosedConnectedSubmanifold k H.carrier l)
    (V : ClosedIrreducibleAnalyticSubvariety k N)
    (hV : V.carrier = strictTransform k g H.carrier) (hdim : V.dim = l) :
    singularLocus V ⊆ g ⁻¹' (g '' exceptionalLocus k g) := by
  have hsub : V.carrier ⊆ g ⁻¹' H.carrier := by
    rw [hV]
    exact closure_minimal sdiff_subset (hH.1.preimage hg.1.continuous)
  intro z hz
  by_contra hze
  have hz0 : z ∉ exceptionalLocus k g := fun h => hze ⟨z, h, rfl⟩
  have hO := StrictTransformComposition.isOpen_compl_exceptionalLocus hg.1
  have hEq : ∀ y ∈ (exceptionalLocus k g)ᶜ,
      y ∈ V.carrier ↔ g y ∈ H.carrier := by
    intro y hy
    refine ⟨fun h => hsub h, fun h => ?_⟩
    rw [hV]
    exact subset_closure ⟨h, hy⟩
  have hzV : z ∈ V.carrier := hz.1
  have hreg : RegularAtDim (n := k) V.carrier z V.dim := by
    rw [hdim]
    exact RegularAtDimTransport.regularAtDim_of_preimage hg.1 hz0 hO hz0 hEq
      (hH.2.2 (g z) (hsub hzV))
  exact hz.2 hreg

/-- The full original embedded-resolution record preserves the canonical
complement of the preceding modification, for the literal composite g ∘ q. -/
theorem isIsomorphismOver_resolvedStrictTransform_compl
    {k l : ℕ} {M N Nt : Type u}
    [TopologicalSpace M] [ChartedSpace (ComplexModel k) M] [IsComplexManifold k M]
    [TopologicalSpace N] [ChartedSpace (ComplexModel k) N] [IsComplexManifold k N]
    [TopologicalSpace Nt] [ChartedSpace (ComplexModel k) Nt] [IsComplexManifold k Nt]
    {g : N → M} (hg : IsAnalyticModification (n := k) g)
    (H : ClosedIrreducibleAnalyticSubvariety k M)
    (hH : IsClosedConnectedSubmanifold k H.carrier l)
    (V : ClosedIrreducibleAnalyticSubvariety k N)
    (hV : V.carrier = strictTransform k g H.carrier) (hdim : V.dim = l)
    {q : Nt → N} (hq : IsBlowupSequence k N Nt q)
    (hres : EmbeddedResolution.IsEmbeddedResolution V q) :
    IsIsomorphismOver k (g ∘ q) (g '' exceptionalLocus k g)ᶜ := by
  let E := g '' exceptionalLocus k g
  have hsing := singularLocus_strictTransform_subset_preimage_exceptionalImage
    hg H hH V hV hdim
  have hgi := AnalyticModificationExceptionalFibres.isIsomorphismOver_compl_image_exceptionalLocus hg
  have hqoff {t : Nt} (ht : g (q t) ∉ E) : q t ∉ singularLocus V :=
    fun hs => ht (hsing hs)
  refine ⟨⟨fun _ ht => ht, ?_, ?_⟩, ?_⟩
  · intro t ht t' ht' heq
    have hqeq : q t = q t' := hgi.1.injOn ht ht' heq
    exact hres.1.1.injOn (hqoff ht) (hqoff ht') hqeq
  · intro x hx
    obtain ⟨z, hz, hzx⟩ := hgi.1.surjOn hx
    have hzS : z ∉ singularLocus V := fun hs => hz (hsing hs)
    obtain ⟨t, _, htz⟩ := hres.1.1.surjOn hzS
    refine ⟨t, ?_, ?_⟩
    · change g (q t) ∉ E
      rwa [htz]
    · change g (q t) = x
      rw [htz, hzx]
  · refine disjoint_left.mpr fun t ht htE => ?_
    have htg : q t ∉ exceptionalLocus k g := disjoint_left.mp hgi.2 ht
    have htq : t ∉ exceptionalLocus k q := disjoint_left.mp hres.1.2 (hqoff ht)
    rw [exceptionalLocus_comp (hg.1.mdifferentiable (by simp))
      (hq.contMDiff.mdifferentiable (by simp))] at htE
    exact htE.elim htq htg

/-- The ACTUAL resolved intrinsic strict carrier restricts to the ORIGINAL
smooth divisor as an analytic modification. Both relative thin sets, whole
inverse holomorphy and equations, and properness are produced internally. -/
theorem isAnalyticModification_resolvedStrictTransformRestriction
    {k : ℕ} {M N Nt : Type u}
    [TopologicalSpace M] [ChartedSpace (ComplexModel k) M] [IsComplexManifold k M]
    [TopologicalSpace N] [ChartedSpace (ComplexModel k) N] [IsComplexManifold k N]
    [CompactSpace N]
    [TopologicalSpace Nt] [ChartedSpace (ComplexModel k) Nt] [IsComplexManifold k Nt]
    {g : N → M} (hg : IsAnalyticModification (n := k) g)
    (H : ClosedIrreducibleAnalyticSubvariety k M)
    (hH : IsClosedConnectedSubmanifold k H.carrier H.dim) (hHdim : H.dim + 1 = k)
    (V : ClosedIrreducibleAnalyticSubvariety k N)
    (hV : V.carrier = strictTransform k g H.carrier) (hdim : V.dim = H.dim)
    {q : Nt → N} (hq : IsBlowupSequence k N Nt q)
    (hres : EmbeddedResolution.IsEmbeddedResolution V q) :
    let T := strictTransform k q V.carrier
    ∃ hT : ∀ t ∈ T, RegularAtDim (n := k) T t H.dim,
      ∃ hi : ∀ t ∈ T, g (q t) ∈ H.carrier,
        letI := SubmanifoldChartedSpace.chartedSpace H.dim_le hH.2.2
        letI := SubmanifoldChartedSpace.isComplexManifold_chartedSpace H.dim_le hH.2.2
        letI := SubmanifoldChartedSpace.chartedSpace H.dim_le hT
        letI := SubmanifoldChartedSpace.isComplexManifold_chartedSpace H.dim_le hT
        IsAnalyticModification (n := H.dim)
          (fun t : T => (⟨g (q t.1), hi t.1 t.2⟩ : H.carrier)) := by
  classical
  let T := strictTransform k q V.carrier
  have hTc : IsClosedConnectedSubmanifold k T H.dim := by
    simpa only [hdim] using hres.2
  obtain ⟨compactNt, _⟩ := StrictTransformComposition.IsBlowupSequence.compactSpace_surjective hq
  let := compactNt
  let : CompactSpace T := isCompact_iff_compactSpace.mp hTc.1.isCompact
  let : Nonempty Nt := ⟨hTc.2.1.nonempty.choose⟩
  obtain ⟨VT, hVT, _⟩ := SourceGenericSubmanifoldMinimum.exists_subvariety_carrier_eq_of_submanifold hTc
  have hqimage : q '' T = V.carrier := by
    simpa only [hVT] using RawProperStrictTransformLelongReader.image_eq_of_strictTransform
      hq.contMDiff hq.contMDiff.continuous.isProperMap V VT hVT
  have hgimage : g '' V.carrier = H.carrier :=
    RawProperStrictTransformLelongReader.image_eq_of_strictTransform hg.1 hg.2.1 H V hV
  let F := g ∘ q
  have hF : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel k) ∞ F := hg.1.comp hq.contMDiff
  have himage : F '' T = H.carrier := by
    calc
      F '' T = g '' (q '' T) := (image_image g q T).symm
      _ = H.carrier := by rw [hqimage, hgimage]
  have hi : ∀ t ∈ T, g (q t) ∈ H.carrier := fun t ht =>
    himage ▸ (show F t ∈ F '' T from ⟨t, ht, rfl⟩)
  refine ⟨hTc.2.2, hi, ?_⟩
  let := SubmanifoldChartedSpace.chartedSpace H.dim_le hH.2.2
  let := SubmanifoldChartedSpace.isComplexManifold_chartedSpace H.dim_le hH.2.2
  let := SubmanifoldChartedSpace.chartedSpace H.dim_le hTc.2.2
  let := SubmanifoldChartedSpace.isComplexManifold_chartedSpace H.dim_le hTc.2.2
  let : ConnectedSpace H.carrier := isConnected_iff_connectedSpace.mp hH.2.1
  let : ConnectedSpace T := isConnected_iff_connectedSpace.mp hTc.2.1
  let rho : T → H.carrier := fun t => ⟨g (q t.1), hi t.1 t.2⟩
  have hrho : ContMDiff 𝓘(ℂ, ComplexModel H.dim) 𝓘(ℂ, ComplexModel H.dim) ∞ rho :=
    SubmanifoldCodRestrict.contMDiff_restrictPreimage H.dim_le hH.2.2
      H.dim_le hTc.2.2 hF hi
  have hsurj : Function.Surjective rho := by
    intro x
    obtain ⟨t, ht, htx⟩ := (show x.1 ∈ F '' T from himage.symm ▸ x.2)
    exact ⟨⟨t, ht⟩, Subtype.ext htx⟩
  let E := g '' exceptionalLocus k g
  have hEc : IsClosed E := AnalyticModificationExceptionalFibres.isClosed_image_exceptionalLocus hg
  have hEa : IsComplexAnalyticSubset (n := k) E :=
    AnalyticModificationExceptionalImageCodimension.isComplexAnalyticSubset_image_exceptionalLocus hg
  let B : Set H.carrier := Subtype.val ⁻¹' E
  let A : Set T := rho ⁻¹' B
  have hBa : IsComplexAnalyticSubset (n := H.dim) B :=
    AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage
      (SubmanifoldChartedSpace.contMDiff_val H.dim_le hH.2.2) hEa
  have hBc : IsClosed B := hEc.preimage continuous_subtype_val
  have hAa : IsComplexAnalyticSubset (n := H.dim) A :=
    AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage hrho hBa
  have hAc : IsClosed A := hBc.preimage hrho.continuous
  obtain ⟨x, hxH, hxE⟩ := not_subset.mp
    (AnalyticModificationExceptionalImageCodimension.not_subset_image_exceptionalLocus_of_codim_one
      hg H hHdim)
  have hBproper : B ≠ univ := fun heq => hxE
    (show (⟨x, hxH⟩ : H.carrier) ∈ B from heq.symm ▸ mem_univ _)
  obtain ⟨t, htx⟩ := hsurj ⟨x, hxH⟩
  have htA : t ∉ A := by
    change rho t ∉ B
    rw [htx]
    exact hxE
  have hAproper : A ≠ univ := fun heq => htA (heq.symm ▸ mem_univ t)
  have hBi : interior B = ∅ := by
    rw [← not_nonempty_iff_eq_empty]
    exact fun hint => hBproper (hBa.eq_univ_of_interior_nonempty hint)
  have hAi : interior A = ∅ := by
    rw [← not_nonempty_iff_eq_empty]
    exact fun hint => hAproper (hAa.eq_univ_of_interior_nonempty hint)
  have hiso : IsIsomorphismOver k F Eᶜ :=
    isIsomorphismOver_resolvedStrictTransform_compl hg H hH V hV hdim hq hres
  have hinv := contMDiffOn_invOver_of_isIsomorphismOver hF hEc.isOpen_compl hiso
  let O : TopologicalSpace.Opens M := ⟨Eᶜ, hEc.isOpen_compl⟩
  let U : TopologicalSpace.Opens H.carrier := ⟨Bᶜ, hBc.isOpen_compl⟩
  let j : U → O := fun x => ⟨x.1.1, x.2⟩
  have hj : ContMDiff 𝓘(ℂ, ComplexModel H.dim) 𝓘(ℂ, ComplexModel k) ∞ j :=
    BlowupRestrictOpen.contMDiff_opens_mk
      ((SubmanifoldChartedSpace.contMDiff_val H.dim_le hH.2.2).comp contMDiff_subtype_val)
      (fun x => x.2)
  have hinvO : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel k) ∞
      (fun x : O => ModificationMassInvariance.invOver F Eᶜ x.1) := by
    intro x
    exact (hinv.contMDiffAt (hEc.isOpen_compl.mem_nhds x.2)).comp x (contMDiff_subtype_val x)
  have hland : ∀ x : U, ModificationMassInvariance.invOver F Eᶜ x.1.1 ∈ T := by
    intro x
    obtain ⟨htoff, hproj⟩ := ModificationMassInvariance.invOver_mem hiso x.2
    have htF : ModificationMassInvariance.invOver F Eᶜ x.1.1 ∉ exceptionalLocus k F :=
      fun h => disjoint_left.mp hiso.2 htoff h
    have htq : ModificationMassInvariance.invOver F Eᶜ x.1.1 ∉ exceptionalLocus k q := by
      intro h
      apply htF
      rw [show F = g ∘ q from rfl, exceptionalLocus_comp
        (hg.1.mdifferentiable (by simp)) (hq.contMDiff.mdifferentiable (by simp))]
      exact Or.inl h
    have htg : q (ModificationMassInvariance.invOver F Eᶜ x.1.1) ∉ exceptionalLocus k g :=
      fun h => x.2 (show x.1.1 ∈ E from hproj ▸ ⟨_, h, rfl⟩)
    have htV : q (ModificationMassInvariance.invOver F Eᶜ x.1.1) ∈ V.carrier := by
      rw [hV]
      have hHpoint : g (q (ModificationMassInvariance.invOver F Eᶜ x.1.1)) ∈ H.carrier := by
        change F (ModificationMassInvariance.invOver F Eᶜ x.1.1) ∈ H.carrier
        rw [hproj]
        exact x.1.2
      exact subset_closure ⟨hHpoint, htg⟩
    exact subset_closure ⟨htV, htq⟩
  let sigma : U → T := fun x => ⟨ModificationMassInvariance.invOver F Eᶜ x.1.1, hland x⟩
  have hsigma : ContMDiff 𝓘(ℂ, ComplexModel H.dim) 𝓘(ℂ, ComplexModel H.dim) ∞ sigma :=
    SubmanifoldCodRestrict.contMDiff_codRestrict H.dim_le hTc.2.2 (hinvO.comp hj) hland
  let s : H.carrier → T := fun x => Classical.choose (hsurj x)
  have hrs : ∀ x, rho (s x) = x := fun x => Classical.choose_spec (hsurj x)
  have hsame : (fun x : U => s x.1) = sigma := by
    funext x
    apply Subtype.ext
    have hproj : F (s x.1).1 = x.1.1 := congrArg Subtype.val (hrs x.1)
    have hoff : F (s x.1).1 ∈ Eᶜ := hproj.symm ▸ x.2
    have hleft := ModificationMassInvariance.invOver_apply hiso hoff
    rw [hproj] at hleft
    exact hleft.symm
  have hs : ContMDiffOn 𝓘(ℂ, ComplexModel H.dim) 𝓘(ℂ, ComplexModel H.dim) ∞ s Bᶜ := by
    have hrest : ContMDiff 𝓘(ℂ, ComplexModel H.dim) 𝓘(ℂ, ComplexModel H.dim) ∞
        (fun x : U => s x.1) := hsame.symm ▸ hsigma
    intro x hx
    exact (contMDiffAt_subtype_iff.mp (hrest (⟨x, hx⟩ : U))).contMDiffWithinAt
  refine ⟨hrho, hrho.continuous.isProperMap, A, B, s, hAc, hAa, hAi,
    hBc, hBa, hBi, rfl, hs, fun x _ => hrs x, ?_⟩
  intro t ht
  apply Subtype.ext
  have hproj : F (s (rho t)).1 = F t.1 := congrArg Subtype.val (hrs (rho t))
  have hoff : F t.1 ∈ Eᶜ := ht
  have hoff' : (s (rho t)).1 ∈ F ⁻¹' Eᶜ := by
    change F (s (rho t)).1 ∈ Eᶜ
    rw [hproj]
    exact hoff
  exact hiso.1.injOn hoff' hoff hproj

end SGPT.Okounkov
