import SGPT.PSH.SubharmonicStrip
import SGPT.Foundations.Analysis.FirstPass.PshDiscLocalGlobal
import SGPT.Foundations.Analysis.FirstPass.SubgeodesicChord
import SGPT.Foundations.Analysis.FirstPass.SubgeodesicInteriorL1
import SGPT.PSH.SourceMixedPOrderMonotonicity
import SGPT.PSH.SourceGlobalPSubgeodesicExistence

/-! The whole original invariant-strip slice-mass corollary `cor:comp:L653`.
Genuine slice nondegeneracy is produced from the original product hypothesis.
No original positive-mass hypothesis is imposed. -/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.VariableComplexAtlas

open Set Filter
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending
open scoped Topology ProductComplexManifold

/-- The actual point of the original complex strip at real time `t`. -/
def sourceStripRealTime (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) : sourceRayTimeStrip :=
  sourceRayTimeEquiv.symm ⟨(t : ℂ), by simpa [complexTimeStrip] using ht⟩

private theorem sourceStripRealTime_time (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
    sourceRayTime (sourceStripRealTime t ht) = (t : ℂ) :=
  congrArg Subtype.val (sourceRayTimeEquiv.apply_symm_apply _)

/-- Translation by the original imaginary time `i c`, in the unchanged strip. -/
def sourceStripImaginaryTranslate (c : ℝ) (z : sourceRayTimeStrip) : sourceRayTimeStrip :=
  sourceRayTimeEquiv.symm ⟨sourceRayTime z + (c : ℂ) * Complex.I, by
    change (sourceRayTime z + (c : ℂ) * Complex.I).re ∈ Ioo (0 : ℝ) 1
    simpa only [Complex.add_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
      mul_zero, zero_mul, sub_self, add_zero] using
      (show (sourceRayTime z).re ∈ Ioo (0 : ℝ) 1 from z.2)⟩

private theorem sourceStripImaginaryTranslate_time (c : ℝ) (z : sourceRayTimeStrip) :
    sourceRayTime (sourceStripImaginaryTranslate c z) =
      sourceRayTime z + (c : ℂ) * Complex.I :=
  congrArg Subtype.val (sourceRayTimeEquiv.apply_symm_apply _)

/-- The original real-time slices, extended by bottom outside the open interval. -/
def sourceInvariantStripCurve {X : Type*} (Φ : X × sourceRayTimeStrip → EReal)
    (t : ℝ) (x : X) : EReal :=
  if ht : t ∈ Ioo (0 : ℝ) 1 then Φ (x, sourceStripRealTime t ht) else ⊥

private theorem invariantStrip_readback {X : Type*}
    {Φ : X × sourceRayTimeStrip → EReal}
    (hinv : ∀ (c : ℝ) (x : X) (z : sourceRayTimeStrip),
      Φ (x, z) = Φ (x, sourceStripImaginaryTranslate c z))
    (x : X) (z : sourceRayTimeStrip) :
    Φ (x, z) = sourceInvariantStripCurve Φ (sourceRayTime z).re x := by
  have hz : (sourceRayTime z).re ∈ Ioo (0 : ℝ) 1 := z.2
  have heq : sourceStripImaginaryTranslate (-(sourceRayTime z).im) z =
      sourceStripRealTime (sourceRayTime z).re hz := by
    apply sourceRayTimeEquiv.injective
    apply Subtype.ext
    change sourceRayTime _ = sourceRayTime _
    rw [sourceStripImaginaryTranslate_time, sourceStripRealTime_time]
    apply Complex.ext <;> simp
  rw [sourceInvariantStripCurve, dif_pos hz]
  simpa only [heq] using hinv (-(sourceRayTime z).im) x z

/-- Actual invariant PSH time lines propagate a single nonpole to every time. -/
theorem invariantPshLine_ne_bot_of_ne_bot {v : ℝ → EReal}
    (hv : PlurisubharmonicOn (fun z : ℂ ↦ v z.re) complexTimeStrip)
    {c : ℝ} (hc : c ∈ Ioo (0 : ℝ) 1) (hvc : v c ≠ ⊥) :
    ∀ t ∈ Ioo (0 : ℝ) 1, v t ≠ ⊥ := by
  have hs : SGPT.PSH.SubharmonicOn (fun z : ℂ ↦ v z.re) complexTimeStrip :=
    SGPT.PSH.subharmonicOn_of_disc hv.discPshOn
      ⟨(c : ℂ), by simpa [complexTimeStrip] using hc, by simpa using hvc⟩
  exact hs.comp_re_ne_bot

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)}
  {Φ : M × sourceRayTimeStrip → EReal}

/-- Full original product PSH and imaginary invariance produce every genuine
slice, including its local nondegeneracy, before the interior predicate is used. -/
theorem sourceInvariantStrip_interior
    (hΦ : (ofFixedModel (n + 1) (M × sourceRayTimeStrip)).IsThetaPSH
      (sourceRayProductBackground θ) Φ)
    (hinv : ∀ (c : ℝ) (x : M) (z : sourceRayTimeStrip),
      Φ (x, z) = Φ (x, sourceStripImaginaryTranslate c z)) :
    SourceSubgeodesicInterior θ (sourceInvariantStripCurve Φ) := by
  have hread := invariantStrip_readback hinv
  have hjoint : SourceJointThetaPSH θ (sourceInvariantStripCurve Φ) := by
    have heq : Φ = fun p : M × sourceRayTimeStrip ↦
        sourceInvariantStripCurve Φ (sourceRayTime p.2).re p.1 := by
      funext p
      exact hread p.1 p.2
    change (ofFixedModel (n + 1) (M × sourceRayTimeStrip)).IsThetaPSH
      (sourceRayProductBackground θ) _
    rw [← heq]
    exact hΦ
  have hnonpole := ((isThetaPSH_iff_nativeThetaPotential
    (sourceRayProductBackground θ) Φ).mp hΦ).2
  refine ⟨?_, hjoint⟩
  intro t ht
  apply (isThetaPSH_iff_nativeThetaPotential θ (sourceInvariantStripCurve Φ t)).mpr
  refine ⟨?_, ?_⟩
  · intro e z hz
    obtain ⟨W, ρ, hzW, hW, hWe, hρ, heq⟩ := exists_chart_local_potential θ e hz
    have hpotential : IsSmoothLocalPotential (atlasClosedFormToNative θ).val e W ρ :=
      ⟨hW, hWe, hρ, heq⟩
    exact ⟨W, ρ, hzW, hpotential,
      SGPT.Foundations.Analysis.FirstPass.PlurisubharmonicOn.subgeodesic_spatial_slice
        (sourceJointThetaPSH_corrected hjoint e hpotential) ht⟩
  · intro x O hO hx
    obtain ⟨p, hp, hpne⟩ := hnonpole (x, sourceRayTimePoint) (O ×ˢ univ)
      (hO.prod isOpen_univ) ⟨hx, mem_univ _⟩
    have hc : (sourceRayTime p.2).re ∈ Ioo (0 : ℝ) 1 := p.2.2
    have hcp : sourceInvariantStripCurve Φ (sourceRayTime p.2).re p.1 ≠ ⊥ := by
      rwa [← hread p.1 p.2]
    let e : ComplexChart n M := complexChartAt p.1
    have hsource : p.1 ∈ e.val.source := mem_complexChartAt_source p.1
    have htarget : e.val p.1 ∈ e.val.target := e.val.map_source hsource
    obtain ⟨W, ρ, hzW, hW, hWe, hρ, heq⟩ := exists_chart_local_potential θ e htarget
    have hpotential : IsSmoothLocalPotential (atlasClosedFormToNative θ).val e W ρ :=
      ⟨hW, hWe, hρ, heq⟩
    have htime : PlurisubharmonicOn
        (fun ζ : ℂ ↦ sourceInvariantStripCurve Φ ζ.re p.1 + (ρ (e.val p.1) : EReal))
        complexTimeStrip := by
      simpa only [chartFunction, e.val.left_inv hsource] using
        SGPT.Foundations.Analysis.FirstPass.PlurisubharmonicOn.subgeodesic_time_line
          (sourceJointThetaPSH_corrected hjoint e hpotential) hzW
    have hfinite : sourceInvariantStripCurve Φ (sourceRayTime p.2).re p.1 +
        (ρ (e.val p.1) : EReal) ≠ ⊥ :=
      EReal.add_ne_bot_iff.mpr ⟨hcp, EReal.coe_ne_bot _⟩
    have htargetFinite := invariantPshLine_ne_bot_of_ne_bot
      (v := fun s ↦ sourceInvariantStripCurve Φ s p.1 + (ρ (e.val p.1) : EReal))
      htime hc hfinite t ht
    refine ⟨p.1, hp.1, ?_⟩
    intro hbot
    apply htargetFinite
    simp only [hbot, EReal.bot_add]

/-- Every original complex-time slice is genuinely theta-PSH; no caller slice
membership or mass witness is needed. -/
theorem sourceInvariantStrip_slice_isThetaPSH
    (hΦ : (ofFixedModel (n + 1) (M × sourceRayTimeStrip)).IsThetaPSH
      (sourceRayProductBackground θ) Φ)
    (hinv : ∀ (c : ℝ) (x : M) (z : sourceRayTimeStrip),
      Φ (x, z) = Φ (x, sourceStripImaginaryTranslate c z))
    (z : sourceRayTimeStrip) :
    (ofFixedModel n M).IsThetaPSH θ (fun x ↦ Φ (x, z)) := by
  have heq : (fun x ↦ Φ (x, z)) = sourceInvariantStripCurve Φ (sourceRayTime z).re :=
    funext fun x ↦ invariantStrip_readback hinv x z
  rw [heq]
  exact (sourceInvariantStrip_interior hΦ hinv).1 _ z.2

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

/-- Every interior closed subsegment has both actual global L¹ endpoints,
obtained from proved interior continuity in the original Kähler volume. -/
theorem sourceInvariantStrip_subgeodesicFrom (omega : KahlerBackground n M)
    (hΦ : (ofFixedModel (n + 1) (M × sourceRayTimeStrip)).IsThetaPSH
      (sourceRayProductBackground θ) Φ)
    (hinv : ∀ (c : ℝ) (x : M) (z : sourceRayTimeStrip),
      Φ (x, z) = Φ (x, sourceStripImaginaryTranslate c z))
    {a b : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo (0 : ℝ) 1) (hab : a < b) :
    SourceSubgeodesicFrom omega θ
      (affineReparametrizedCurve (sourceInvariantStripCurve Φ) a b)
      (sourceInvariantStripCurve Φ a) (sourceInvariantStripCurve Φ b) := by
  have hn := (sourceInterior_iff_native θ _).mp (sourceInvariantStrip_interior hΦ hinv)
  apply (sourceSubgeodesicFrom_iff_native omega θ _ _ _).mpr
  exact hn.affineReparametrized_isSubgeodesicFrom ha hb hab
    ((hn.manifoldL1LocallyContinuousAt ha).mono_left nhdsWithin_le_nhds)
    ((hn.manifoldL1LocallyContinuousAt hb).mono_left nhdsWithin_le_nhds)

variable [ConnectedSpace M]

/-- All original slices are equivalent for the genuine global P relation,
including when their original non-pluripolar masses vanish. -/
theorem sourceInvariantStrip_slices_sourcePEquivalent (omega : KahlerBackground n M)
    (hΦ : (ofFixedModel (n + 1) (M × sourceRayTimeStrip)).IsThetaPSH
      (sourceRayProductBackground θ) Φ)
    (hinv : ∀ (c : ℝ) (x : M) (z : sourceRayTimeStrip),
      Φ (x, z) = Φ (x, sourceStripImaginaryTranslate c z))
    (z w : sourceRayTimeStrip) :
    GlobalPComparison.sourcePEquivalent (n := n) (fun x ↦ Φ (x, z)) (fun x ↦ Φ (x, w)) := by
  have hz : (sourceRayTime z).re ∈ Ioo (0 : ℝ) 1 := z.2
  have hw : (sourceRayTime w).re ∈ Ioo (0 : ℝ) 1 := w.2
  have heq (q : sourceRayTimeStrip) : (fun x ↦ Φ (x, q)) =
      sourceInvariantStripCurve Φ (sourceRayTime q).re :=
    funext fun x ↦ invariantStrip_readback hinv x q
  rw [heq z, heq w]
  rcases lt_trichotomy (sourceRayTime z).re (sourceRayTime w).re with hzw | hzw | hwz
  · exact (sourceInvariantStrip_subgeodesicFrom omega hΦ hinv hz hw hzw).sourcePEquivalent_endpoints
  · rw [hzw]
    have hu := (isThetaPSH_iff_nativeThetaPotential θ _).mp
      ((sourceInvariantStrip_interior hΦ hinv).1 _ hw)
    have hrefl := SingularGlobalPOrder.sourcePOrder_refl_of_isThetaPshPotential omega hu
    exact ⟨hrefl, hrefl⟩
  · have h := (sourceInvariantStrip_subgeodesicFrom omega hΦ hinv hw hz hwz).sourcePEquivalent_endpoints
    exact ⟨h.2, h.1⟩

/-- Whole original `cor:comp:L653`, on the unchanged actual source measures.
Both slice witnesses are produced internally, and zero masses and n=0 remain. -/
theorem sourceInvariantStrip_diagonalMass_eq (omega : KahlerBackground n M)
    (hΦ : (ofFixedModel (n + 1) (M × sourceRayTimeStrip)).IsThetaPSH
      (sourceRayProductBackground θ) Φ)
    (hinv : ∀ (c : ℝ) (x : M) (z : sourceRayTimeStrip),
      Φ (x, z) = Φ (x, sourceStripImaginaryTranslate c z))
    (z w : sourceRayTimeStrip) :
    sourcePotentialNonPluripolarMeasure θ (fun x ↦ Φ (x, z))
        (sourceInvariantStrip_slice_isThetaPSH hΦ hinv z) univ =
      sourcePotentialNonPluripolarMeasure θ (fun x ↦ Φ (x, w))
        (sourceInvariantStrip_slice_isThetaPSH hΦ hinv w) univ := by
  simpa only [sourceMixedNonPluripolarMass_diagonal] using
    sourceMixedNonPluripolarMass_eq_of_sourcePEquivalent omega
      (fun _ : Fin n ↦ sourceInvariantStrip_slice_isThetaPSH hΦ hinv z)
      (fun _ : Fin n ↦ sourceInvariantStrip_slice_isThetaPSH hΦ hinv w)
      (fun _ ↦ sourceInvariantStrip_slices_sourcePEquivalent omega hΦ hinv z w)

end SGPT.PSH.VariableComplexAtlas
