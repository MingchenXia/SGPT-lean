import SGPT.Foundations.Analysis.Pending.GermIdealTotalTransform
import SGPT.Foundations.Analysis.Pending.MarkedIdealOperationsAlong
import SGPT.Foundations.Analysis.Pending.MarkedIdealOpenBiholomorphism
import SGPT.Foundations.Analysis.Pending.SubmanifoldCodRestrict
import SGPT.Foundations.Analysis.Pending.SubmanifoldIdealRestriction
import SGPT.Foundations.Analysis.Pending.StokesSingularLocusAnalytic
import SGPT.Foundations.Analysis.Pending.BlowupExistence
import SGPT.Foundations.Analysis.Pending.BlowupUniqueness
import SGPT.Foundations.Analysis.Pending.LocusProperties

set_option autoImplicit false

noncomputable section

universe u

namespace SGPT.Okounkov

open Set Filter
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.RegularLocusDense
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.GermIdealPullbackCalculus
open SGPT.Foundations.Analysis.Pending.RelativePrincipalizationSpan
open SGPT.Foundations.Analysis.Pending.InvertibleIdealQuotient

/-- Literal ideal pullback composition with three independent model dimensions. -/
theorem pullback_comp_mixedDimensions
    {n m l : ℕ} {X Y Z : Type u}
    [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
    [TopologicalSpace Y] [ChartedSpace (ComplexModel m) Y] [IsComplexManifold m Y]
    [TopologicalSpace Z] [ChartedSpace (ComplexModel l) Z] [IsComplexManifold l Z]
    {f : Y → X} {g : Z → Y}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (hg : ContMDiff 𝓘(ℂ, ComplexModel l) 𝓘(ℂ, ComplexModel m) ∞ g)
    {a : GermIdeal n X} (ha : a.IsCoherent) :
    GermIdeal.pullback (m := l) (f ∘ g) a =
      GermIdeal.pullback (m := l) g (GermIdeal.pullback (m := m) f a) := by
  refine GermIdeal.ext (funext fun z => funext fun v => propext ⟨fun hv => ?_, fun hv => ?_⟩)
  · have hfat : ∀ᶠ y in 𝓝 (g z),
        ContMDiffAt 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f y :=
      Eventually.of_forall fun y => hf.contMDiffAt
    refine GermIdeal.mem_pullback_iff.mpr
      (IsInSpanAt.mono ?_ (GermIdeal.mem_pullback_iff.mp hv))
    rintro s ⟨c, hc, rfl⟩
    have hchol : HolomorphicAt n c (f (g z)) :=
      GermIdeal.IsCoherent.holomorphicAt_mem ha hc
    have hcfhol : HolomorphicAt m (c ∘ f) (g z) :=
      hchol.comp_contMDiff hfat
    have hcf : (GermIdeal.pullback (m := m) f a).mem (g z) (c ∘ f) :=
      GermIdeal.mem_pullback_iff.mpr (isInSpanAt_self ⟨c, hc, rfl⟩ hcfhol)
    exact ⟨c ∘ f, hcf, rfl⟩
  · refine GermIdeal.mem_pullback_iff.mpr
      (IsInSpanAt.trans ?_ (GermIdeal.mem_pullback_iff.mp hv))
    rintro s ⟨c, hc, rfl⟩
    refine IsInSpanAt.mono ?_ (isInSpanAt_comp hg (GermIdeal.mem_pullback_iff.mp hc))
    rintro t ⟨d, ⟨a', ha', rfl⟩, rfl⟩
    exact ⟨a', ha', rfl⟩

private theorem regularAtDim_image_submanifold
    {n k : ℕ} {X : Type u} [TopologicalSpace X]
    [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
    {N : Set X} (hk : k ≤ n) (hN : ∀ x ∈ N, RegularAtDim (n := n) N x k)
    {C : Set N} {p : N} {d : ℕ}
    (hC : letI := SubmanifoldChartedSpace.chartedSpace hk hN
      RegularAtDim (n := k) C p d) :
    RegularAtDim (n := n) (Subtype.val '' C) p.1 d := by
  let := SubmanifoldChartedSpace.chartedSpace hk hN
  let := SubmanifoldChartedSpace.isComplexManifold_chartedSpace hk hN
  obtain ⟨_, _, Φ, hΦt, hΦ0, hΦN⟩ := hN p.1 p.2
  let F : SubmanifoldChartedSpace.FlatData n k X N :=
    { amb := complexChartAt (n := n) p.1
      flat := LocalHolomorphicEquivAt.toOpenPartialHomeomorph Φ
      differentiableOn_flat := Φ.toFun_holomorphic
      differentiableOn_flat_symm := Φ.invFun_holomorphic
      flat_source_subset := hΦt
      mem_iff := fun y hy hyΦ => hΦN hy hyΦ
      base := p.1
      base_mem := p.2 }
  let e : ComplexChart k N :=
    ⟨F.chart hk, SubmanifoldChartedSpace.chart_mem_atlas hk hN F⟩
  have hpF : p ∈ e.val.source := ⟨mem_complexChartAt_source p.1, Φ.center_mem_source⟩
  obtain ⟨χ, hχt, hχ0, hχC⟩ :=
    StokesSingularLocusAnalytic.exists_chartFlattening hC e hpF
  have hep : e.val p = 0 := by
    change coordinateProjection n k (Φ.toFun ((complexChartAt (n := n) p.1).val p.1)) = 0
    rw [hΦ0, map_zero]
  let E := StokesSingularLocusAnalytic.extendLHE (n := n) hk χ
  have hcentre : Φ.toFun ((complexChartAt (n := n) p.1).val p.1) =
      coordinateInclusion n k (e.val p) := by rw [hΦ0, hep, map_zero]
  let Ψ := RegularAtDimChart.precomp Φ.toOpenPartialHomeomorph
    Φ.toFun_holomorphic Φ.invFun_holomorphic Φ.center_mem_source hcentre E
  refine ⟨le_trans hC.1 hk, ⟨p, hC.2.1, rfl⟩, Ψ, ?_, ?_, ?_⟩
  · exact fun z hz => hΦt hz.1
  · change StokesSingularLocusAnalytic.extendFirst k χ.toFun
        (Φ.toFun ((complexChartAt (n := n) p.1).val p.1)) = 0
    have hχzero : χ.toFun 0 = 0 := by simpa only [hep] using hχ0
    rw [hΦ0]
    simp only [StokesSingularLocusAnalytic.extendFirst, map_zero, hχzero, sub_self, add_zero]
  · intro y hy hyΨ
    have hχsrc : coordinateProjection n k
        (Φ.toFun ((complexChartAt (n := n) p.1).val y)) ∈ χ.source := hyΨ.2
    change y ∈ Subtype.val '' C ↔
      StokesSingularLocusAnalytic.extendFirst k χ.toFun
        (Φ.toFun ((complexChartAt (n := n) p.1).val y)) ∈ complexCoordinatePlane n d
    rw [StokesSingularLocusAnalytic.extendFirst_mem_plane_iff hk hC.1]
    constructor
    · rintro ⟨q, hqC, rfl⟩
      have hqF : q ∈ e.val.source := ⟨hy, hyΨ.1⟩
      have hqchart : e.val q ∈ χ.source := hχsrc
      refine ⟨?_, (hΦN hy hyΨ.1).mp q.2⟩
      have h := (hχC (e.val q) hqchart).mp (by rw [e.val.left_inv hqF]; exact hqC)
      exact h
    · rintro ⟨hc, hn⟩
      have hyN : y ∈ N := (hΦN hy hyΨ.1).mpr hn
      let q : N := ⟨y, hyN⟩
      have hqF : q ∈ e.val.source := ⟨hy, hyΨ.1⟩
      have hqC : q ∈ C := by
        have h := (hχC (e.val q) hχsrc).mpr hc
        rwa [e.val.left_inv hqF] at h
      exact ⟨q, hqC, rfl⟩

private theorem exists_extended_vanishing_germ
    {n k : ℕ} {X : Type u} [TopologicalSpace X]
    [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
    {N : Set X} (hk : k ≤ n) (hN : ∀ x ∈ N, RegularAtDim (n := n) N x k)
    {C : Set N} {p : N} {h : N → ℂ}
    (hh : letI := SubmanifoldChartedSpace.chartedSpace hk hN
      (vanishingIdeal (n := k) C).mem p h) :
    letI := SubmanifoldChartedSpace.chartedSpace hk hN
    ∃ H : X → ℂ, (vanishingIdeal (n := n) (Subtype.val '' C)).mem p.1 H ∧
      H ∘ Subtype.val =ᶠ[𝓝 p] h := by
  classical
  let := SubmanifoldChartedSpace.chartedSpace hk hN
  let := SubmanifoldChartedSpace.isComplexManifold_chartedSpace hk hN
  obtain ⟨r0, hr0p, hrd, hrN, hrid⟩ :=
    MarkedIdealOperationsAlong.exists_localRetraction (hN p.1 p.2)
  obtain ⟨U, hUsub, hUo, hpU⟩ := mem_nhds_iff.mp ((hrd.and hrN).and hrid)
  let O : TopologicalSpace.Opens X := ⟨U, hUo⟩
  let pU : O := ⟨p.1, hpU⟩
  have hr0 : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞
      (fun x : O => r0 x.1) := by
    intro x
    have hx : ∀ᶠ y in 𝓝 x.1,
        MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) r0 y :=
      eventually_of_mem (hUo.mem_nhds x.2) fun y hy => (hUsub hy).1.1
    exact (MarkedIdealOpenBiholomorphism.contMDiffAt_of_eventually_mdifferentiableAt' hx).comp x
      (contMDiff_subtype_val (n := ∞) x)
  let r : O → N := fun x => ⟨r0 x.1, (hUsub x.2).1.2⟩
  have hr : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel k) ∞ r :=
    SubmanifoldCodRestrict.contMDiff_codRestrict hk hN hr0 fun x => (hUsub x.2).1.2
  have hrp : r pU = p := Subtype.ext hr0p
  let H : X → ℂ := extendOpens O (h ∘ r)
  have hHhol : HolomorphicAt n H p.1 := by
    apply (holomorphicAt_iff_extendOpens O (m := n) (x := pU) (g := h ∘ r)).mp
    have hh' : HolomorphicAt k h (r pU) := by rw [hrp]; exact hh.1
    exact hh'.comp_contMDiff (Eventually.of_forall fun y => hr y)
  have hzeroO : ∀ᶠ x in 𝓝 pU,
      x.1 ∈ Subtype.val '' C → H x.1 = 0 := by
    have hzero : ∀ᶠ x in 𝓝 pU, r x ∈ C → h (r x) = 0 :=
      hr.continuous.continuousAt.eventually (by rw [hrp]; exact hh.2)
    filter_upwards [hzero] with x hx hxC
    obtain ⟨c, hc, hcx⟩ := hxC
    have hrc : r x = c := by
      apply Subtype.ext
      change r0 x.1 = c.1
      rw [(hUsub x.2).2 (hcx ▸ c.2), ← hcx]
    change extendOpens O (h ∘ r) x.1 = 0
    rw [extendOpens_val]
    exact hx (hrc ▸ hc)
  refine ⟨H, ⟨hHhol, (eventually_nhds_val_iff O (x := pU)
    (P := fun y => y ∈ Subtype.val '' C → H y = 0)).mpr hzeroO⟩, ?_⟩
  have hUp : ∀ᶠ q in 𝓝 p, q.1 ∈ U :=
    continuous_subtype_val.continuousAt.eventually (hUo.mem_nhds hpU)
  filter_upwards [hUp] with q hq
  have hrq : r (⟨q.1, hq⟩ : O) = q := Subtype.ext ((hUsub hq).2 q.2)
  change extendOpens O (h ∘ r) q.1 = h q
  rw [show q.1 = ((⟨q.1, hq⟩ : O) : X) from rfl, extendOpens_val]
  exact congrArg h hrq

/-- A real nested intrinsic centre gives the ambient centre and the entire ideal identity. -/
theorem closedSubmanifoldCentre_ambient_and_restrictedIdeal
    {n k : ℕ} {X : Type u} [TopologicalSpace X]
    [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
    {N : Set X} (hk : k ≤ n) (hNc : IsClosed N)
    (hN : ∀ x ∈ N, RegularAtDim (n := n) N x k)
    (C : Set N)
    (hC : letI := SubmanifoldChartedSpace.chartedSpace hk hN
      IsClosedSubmanifold k C)
    (hCi : interior C = ∅) :
    IsClosedSubmanifold n (Subtype.val '' C) ∧ interior (Subtype.val '' C) = ∅ ∧
      letI := SubmanifoldChartedSpace.chartedSpace hk hN
      GermIdeal.pullback (m := k) Subtype.val
        (vanishingIdeal (n := n) (Subtype.val '' C)) = vanishingIdeal (n := k) C := by
  let := SubmanifoldChartedSpace.chartedSpace hk hN
  let := SubmanifoldChartedSpace.isComplexManifold_chartedSpace hk hN
  have hc : IsClosed (Subtype.val '' C) := hNc.isClosedEmbedding_subtypeVal.isClosedMap _ hC.1
  have hreg : IsClosedSubmanifold n (Subtype.val '' C) := by
    refine ⟨hc, ?_⟩
    rintro x ⟨p, hp, rfl⟩
    obtain ⟨d, hd⟩ := hC.2 p hp
    exact ⟨d, regularAtDim_image_submanifold hk hN hd⟩
  have hthin : interior (Subtype.val '' C) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    obtain ⟨p, hpC, hpx⟩ := interior_subset hx
    have hO : IsOpen (Subtype.val ⁻¹' interior (Subtype.val '' C) : Set N) :=
      isOpen_interior.preimage continuous_subtype_val
    have hOC : Subtype.val ⁻¹' interior (Subtype.val '' C) ⊆ C := by
      intro q hq
      obtain ⟨c, hc, hcw⟩ := interior_subset hq
      exact Subtype.val_injective hcw ▸ hc
    have hpO : p ∈ Subtype.val ⁻¹' interior (Subtype.val '' C) := by
      change p.1 ∈ interior (Subtype.val '' C)
      rw [hpx]
      exact hx
    have hpint : p ∈ interior C := interior_mono hOC
      (by rw [IsOpen.interior_eq hO]; exact hpO)
    rw [hCi] at hpint
    exact hpint
  refine ⟨hreg, hthin, ?_⟩
  have hval := SubmanifoldChartedSpace.contMDiff_val hk hN
  refine GermIdeal.ext (funext fun p => funext fun h => propext ⟨fun hh => ?_, fun hh => ?_⟩)
  · refine BlowupStrictIdeal.mem_vanishingIdeal_of_isInSpanAt' ?_
      (GermIdeal.mem_pullback_iff.mp hh)
    rintro a ⟨H, hH, rfl⟩
    refine ⟨hH.1.comp_contMDiff (Eventually.of_forall fun q => hval q), ?_⟩
    have hz := continuous_subtype_val.continuousAt.eventually hH.2
    filter_upwards [hz] with q hq hqC
    exact hq ⟨q, hqC, rfl⟩
  · obtain ⟨H, hH, heq⟩ := exists_extended_vanishing_germ hk hN hh
    exact GermIdeal.mem_pullback_iff.mpr
      (InvertibleIdealQuotient.IsInSpanAt.congr'
        (isInSpanAt_self ⟨H, hH, rfl⟩
          (hH.1.comp_contMDiff (Eventually.of_forall fun q => hval q))) heq)

private theorem interior_preimage_eq_empty_of_invertible
    {n m : ℕ} {X Y : Type u}
    [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
    [TopologicalSpace Y] [ChartedSpace (ComplexModel m) Y] [IsComplexManifold m Y]
    {C : Set X} (hC : IsClosedSubmanifold n C) {g : Y → X}
    (hg : ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ g)
    (hi : (GermIdeal.pullback (m := m) g (vanishingIdeal (n := n) C)).IsInvertible) :
    interior (g ⁻¹' C) = ∅ := by
  have hz : (GermIdeal.pullback (m := m) g (vanishingIdeal (n := n) C)).zeroLocus =
      g ⁻¹' C := by
    rw [BlowupExceptionalDivisor.zeroLocus_pullback hg
      (VanishingIdealCoherent.isCoherent_vanishingIdeal hC),
      BlowupExceptionalDivisor.zeroLocus_vanishingIdeal hC.1]
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  obtain ⟨U, hUo, hxU, h, hh, hnon, hgen⟩ := hi x
  obtain ⟨y, ⟨hyB, hyU⟩, hny⟩ := hnon (interior (g ⁻¹' C) ∩ U)
    (isOpen_interior.inter hUo) inter_subset_right ⟨x, hx, hxU⟩
  have hmem : (GermIdeal.pullback (m := m) g (vanishingIdeal (n := n) C)).mem y h :=
    (hgen y hyU h).mpr (isInSpanAt_self rfl
      (InvertibleIdealQuotient.holomorphicAt_of_mdifferentiableOn hUo hh hyU))
  have hyz : y ∈ (GermIdeal.pullback (m := m) g (vanishingIdeal (n := n) C)).zeroLocus := by
    rw [hz]; exact interior_subset hyB
  exact hny (hyz h hmem)

/-- The actual strict restriction is the full intrinsic blowup, with arbitrary-dimensional tests. -/
theorem isBlowupAlong_closedSubmanifold_corestriction
    {n k : ℕ} {X Y : Type u}
    [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
    [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
    {N : Set X} (hk : k ≤ n) (hNc : IsClosed N)
    (hN : ∀ x ∈ N, RegularAtDim (n := n) N x k)
    (C : Set N)
    (hC : letI := SubmanifoldChartedSpace.chartedSpace hk hN
      IsClosedSubmanifold k C)
    (hCi : interior C = ∅) {π : Y → X}
    (hπ : IsBlowupAlong n (Subtype.val '' C) π) :
    let S := BlowupStrictSubmanifold.geoStrictTransform π (Subtype.val '' C) N
    ∃ hS : ∀ y ∈ S, RegularAtDim (n := n) S y k,
      ∃ hi : ∀ y ∈ S, π y ∈ N,
        letI := SubmanifoldChartedSpace.chartedSpace hk hN
        letI := SubmanifoldChartedSpace.chartedSpace hk hS
        IsBlowupAlong k C (fun y : S => (⟨π y.1, hi y.1 y.2⟩ : N)) := by
  classical
  let := SubmanifoldChartedSpace.chartedSpace hk hN
  let := SubmanifoldChartedSpace.isComplexManifold_chartedSpace hk hN
  let S := BlowupStrictSubmanifold.geoStrictTransform π (Subtype.val '' C) N
  have hCN : Subtype.val '' C ⊆ N := fun _ hx => by
    obtain ⟨p, _, rfl⟩ := hx; exact p.2
  have hS : ∀ y ∈ S, RegularAtDim (n := n) S y k :=
    fun _ hy => BlowupStrictSubmanifold.regularAtDim_geoStrictTransform hπ hNc hN hCN hy
  have hi : ∀ y ∈ S, π y ∈ N :=
    fun _ hy => BlowupStrictSubmanifold.geoStrictTransform_subset_preimage
      hπ.contMDiff.continuous hNc hy
  let := SubmanifoldChartedSpace.chartedSpace hk hS
  let := SubmanifoldChartedSpace.isComplexManifold_chartedSpace hk hS
  let r : S → N := fun y => ⟨π y.1, hi y.1 y.2⟩
  have hvalN := SubmanifoldChartedSpace.contMDiff_val hk hN
  have hvalS := SubmanifoldChartedSpace.contMDiff_val hk hS
  have hr : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel k) ∞ r :=
    SubmanifoldCodRestrict.contMDiff_restrictPreimage hk hN hk hS hπ.contMDiff hi
  obtain ⟨_, _, hid⟩ := closedSubmanifoldCentre_ambient_and_restrictedIdeal hk hNc hN C hC hCi
  have hcoh := BlowupExceptionalDivisor.isCoherent_vanishingIdeal_centre hπ
  have halong : SGPT.Foundations.Analysis.Pending.RestrictedIdealQuotient.IsInvertibleAlong n S
      (GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) (Subtype.val '' C))) := by
    have ha := MarkedIdeals.MarkedIdeal.isInvertibleAlong_geoStrictTransform hπ N 1
    change SGPT.Foundations.Analysis.Pending.RestrictedIdealQuotient.IsInvertibleAlong n S
      (IdealWeightPowers.idealPow (BlowupExceptionalDivisor.exceptionalDivisor hπ).ideal 1) at ha
    rw [BlowupStrictIdeal.idealPow_one_exceptionalDivisor hπ] at ha
    exact ha
  have hidr : GermIdeal.pullback (m := k) (Subtype.val : S → Y)
      (GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) (Subtype.val '' C))) =
      GermIdeal.pullback (m := k) r (vanishingIdeal (n := k) C) := by
    rw [← pullback_comp_mixedDimensions hπ.contMDiff hvalS hcoh]
    change GermIdeal.pullback (m := k) ((Subtype.val : N → X) ∘ r)
      (vanishingIdeal (n := n) (Subtype.val '' C)) = _
    rw [pullback_comp_mixedDimensions hvalN hr hcoh, hid]
  have hrinv : (GermIdeal.pullback (m := k) r (vanishingIdeal (n := k) C)).IsInvertible := by
    rw [← hidr]
    exact SubmanifoldIdealRestriction.isInvertible_restrictIdeal hvalS halong
  refine ⟨hS, hi, hC, hCi, hr, hrinv, ?_⟩
  intro l Z _ _ _ g hg hginv
  have hig : (GermIdeal.pullback (m := l) ((Subtype.val : N → X) ∘ g)
      (vanishingIdeal (n := n) (Subtype.val '' C))).IsInvertible := by
    rw [pullback_comp_mixedDimensions hvalN hg hcoh, hid]
    exact hginv
  obtain ⟨L, ⟨hL, hπL⟩, huniq⟩ :=
    hπ.2.2.2.2 l Z (Subtype.val ∘ g) (hvalN.comp hg) hig
  have hthin : interior (g ⁻¹' C) = ∅ :=
    interior_preimage_eq_empty_of_invertible hC hg hginv
  have hLs : ∀ z, L z ∈ S := by
    have hclosed : IsClosed (L ⁻¹' S) := isClosed_closure.preimage hL.continuous
    have hsub : (g ⁻¹' C)ᶜ ⊆ L ⁻¹' S := by
      intro z hz
      apply subset_closure
      have hπz : π (L z) = (g z).1 := congrFun hπL z
      refine ⟨?_, ?_⟩
      · rw [hπz]; exact (g z).2
      · rw [hπz]
        rintro ⟨c, hc, heq⟩
        apply hz
        change g z ∈ C
        exact Subtype.val_injective heq ▸ hc
    have huniv : univ ⊆ L ⁻¹' S := by
      rw [← (interior_eq_empty_iff_dense_compl.mp hthin).closure_eq]
      exact closure_minimal hsub hclosed
    exact fun z => huniv (mem_univ z)
  let h : Z → S := fun z => ⟨L z, hLs z⟩
  have hh : ContMDiff 𝓘(ℂ, ComplexModel l) 𝓘(ℂ, ComplexModel k) ∞ h :=
    SubmanifoldCodRestrict.contMDiff_codRestrict hk hS hL hLs
  have hrh : r ∘ h = g := by
    funext z; exact Subtype.ext (congrFun hπL z)
  refine ⟨h, ⟨hh, hrh⟩, ?_⟩
  intro h' hh'
  have hp' : π ∘ ((Subtype.val : S → Y) ∘ h') = Subtype.val ∘ g := by
    funext z
    exact congrArg Subtype.val (congrFun hh'.2 z)
  have heq : (Subtype.val : S → Y) ∘ h' = L :=
    huniq _ ⟨hvalS.comp hh'.1, hp'⟩
  funext z
  exact Subtype.ext (congrFun heq z)

/-- Actual existence, compact Kähler geometry, and whole inverse maps for one intrinsic blowup. -/
theorem exists_ambientRealization_of_intrinsicBlowup
    {n k : ℕ} {X : Type u} [TopologicalSpace X]
    [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X] [CompactSpace X]
    (omegaX : KahlerBackground n X) {N : Set X} (hk : k ≤ n) (hNc : IsClosed N)
    (hN : ∀ x ∈ N, RegularAtDim (n := n) N x k)
    (C : Set N) {N1 : Type u} [TopologicalSpace N1]
    [ChartedSpace (ComplexModel k) N1] [IsComplexManifold k N1]
    {q : N1 → N}
    (hq : letI := SubmanifoldChartedSpace.chartedSpace hk hN
      IsBlowupAlong k C q) :
    ∃ (Y : Type u) (_ : TopologicalSpace Y) (_ : ChartedSpace (ComplexModel n) Y)
      (_ : IsComplexManifold n Y) (_ : CompactSpace Y) (_ : KahlerBackground n Y)
      (π : Y → X) (S : Set Y) (hS : ∀ y ∈ S, RegularAtDim (n := n) S y k),
      IsBlowupAlong n (Subtype.val '' C) π ∧ IsBlowupSequence n X Y π ∧
      IsClosed S ∧ S = BlowupStrictSubmanifold.geoStrictTransform π (Subtype.val '' C) N ∧
      S = strictTransform n π N ∧
      ∃ hi : ∀ y ∈ S, π y ∈ N,
        letI := SubmanifoldChartedSpace.chartedSpace hk hN
        letI := SubmanifoldChartedSpace.chartedSpace hk hS
        let r : S → N := fun y => ⟨π y.1, hi y.1 y.2⟩
        ∃ (e : N1 → S) (f : S → N1),
          ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel k) ∞ e ∧
          ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel k) ∞ f ∧
          r ∘ e = q ∧ q ∘ f = r ∧ f ∘ e = id ∧ e ∘ f = id ∧
          ((Subtype.val : S → Y) ∘ e) '' univ = S ∧
          π ∘ ((Subtype.val : S → Y) ∘ e) = (Subtype.val : N → X) ∘ q := by
  classical
  let := SubmanifoldChartedSpace.chartedSpace hk hN
  let := SubmanifoldChartedSpace.isComplexManifold_chartedSpace hk hN
  obtain ⟨hC, hCi, _⟩ :=
    closedSubmanifoldCentre_ambient_and_restrictedIdeal hk hNc hN C hq.1 hq.2.1
  obtain ⟨Y, topY, chartsY, complexY, π, hπ⟩ :=
    BlowupExistence.exists_isBlowupAlong (Subtype.val '' C) hC hCi
  let := topY
  let := chartsY
  let := complexY
  have hseq : IsBlowupSequence n X Y π :=
    IsBlowupSequence.step id (Subtype.val '' C) π IsBlowupSequence.refl hπ
  obtain ⟨compactY, ⟨omegaY⟩⟩ :=
    LocusProperties.compactSpace_and_kahler_of_isBlowupSequence ⟨omegaX⟩ π hseq
  let := compactY
  let S := BlowupStrictSubmanifold.geoStrictTransform π (Subtype.val '' C) N
  obtain ⟨hS, hi, hr⟩ :=
    isBlowupAlong_closedSubmanifold_corestriction hk hNc hN C hq.1 hq.2.1 hπ
  let := SubmanifoldChartedSpace.chartedSpace hk hS
  let := SubmanifoldChartedSpace.isComplexManifold_chartedSpace hk hS
  let r : S → N := fun y => ⟨π y.1, hi y.1 y.2⟩
  obtain ⟨e, f, he, hf, hre, hqf, hfe, hef⟩ :=
    BlowupUniqueness.exists_biholomorphism_over hq hr
  have hclosure : N ⊆ closure (N \ Subtype.val '' C) := by
    intro x hx
    let p : N := ⟨x, hx⟩
    have hp : p ∈ closure Cᶜ := (interior_eq_empty_iff_dense_compl.mp hq.2.1).closure_eq ▸ mem_univ p
    have himg : Subtype.val '' closure Cᶜ ⊆ closure (Subtype.val '' Cᶜ) :=
      image_closure_subset_closure_image continuous_subtype_val
    apply closure_mono ?_ (himg ⟨p, hp, rfl⟩)
    rintro y ⟨z, hz, rfl⟩
    refine ⟨z.2, ?_⟩
    rintro ⟨c, hc, hcz⟩
    exact hz (Subtype.val_injective hcz ▸ hc)
  have hstrict : S = strictTransform n π N :=
    BlowupStrictIdeal.geoStrictTransform_eq_strictTransform hπ hclosure
  have himage : ((Subtype.val : S → Y) ∘ e) '' univ = S := by
    apply Subset.antisymm
    · rintro y ⟨z, _, rfl⟩; exact (e z).2
    · intro y hy
      refine ⟨f ⟨y, hy⟩, mem_univ _, ?_⟩
      exact congrArg Subtype.val (congrFun hef ⟨y, hy⟩)
  have hcomm : π ∘ ((Subtype.val : S → Y) ∘ e) = (Subtype.val : N → X) ∘ q := by
    funext z; exact congrArg Subtype.val (congrFun hre z)
  exact ⟨Y, topY, chartsY, complexY, compactY, omegaY, π, S, hS,
    hπ, hseq, isClosed_closure, rfl, hstrict, hi, e, f,
    he, hf, hre, hqf, hfe, hef, himage, hcomm⟩

/-- The exact-dimensional whole ambient image of a nested closed connected submanifold. -/
theorem isClosedConnectedSubmanifold_ambientImage
    {n k : ℕ} {X : Type u} [TopologicalSpace X]
    [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
    {N : Set X} (hk : k ≤ n) (hNclosed : IsClosed N)
    (hN : ∀ x ∈ N, RegularAtDim (n := n) N x k)
    {C : Set N} {d : ℕ}
    (hC : letI := SubmanifoldChartedSpace.chartedSpace hk hN
      IsClosedConnectedSubmanifold k C d) :
    IsClosedConnectedSubmanifold n (Subtype.val '' C) d := by
  let := SubmanifoldChartedSpace.chartedSpace hk hN
  let := SubmanifoldChartedSpace.isComplexManifold_chartedSpace hk hN
  refine ⟨hNclosed.isClosedMap_subtype_val C hC.1,
    hC.2.1.image Subtype.val continuous_subtype_val.continuousOn, ?_⟩
  rintro x ⟨p, hpC, rfl⟩
  exact regularAtDim_image_submanifold hk hN (hC.2.2 p hpC)

end SGPT.Okounkov
