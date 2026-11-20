import SGPT.PSH.SourceTestCurveJoinInverse
import SGPT.Convex.Subgradient

/-! # The literal binary upper-concave-envelope identity

The raw envelope is exactly negative lowerConvexEnvelope of negative max.
No closedness, PSH, mass or model output certificate is assumed for it.
-/
set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.VariableComplexAtlas
open Set Filter Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)}

/-- The actual convex envelope underlying the ORIGINAL concave maximum. -/
def sourceTestCurveJoinConvexEnvelope (Γ Δ : SourceTestCurvePredata θ) (x : M) : ℝ → EReal :=
  SGPT.Convex.lowerConvexEnvelope (fun s =>
    -max (sourceTestCurveAt Γ s x) (sourceTestCurveAt Δ s x))

/-- The literal raw upper concave envelope, before any ordinary P-envelope. -/
def sourceTestCurveRawConcaveMaximum (Γ Δ : SourceTestCurvePredata θ) (τ : ℝ) : M → EReal :=
  fun x => -sourceTestCurveJoinConvexEnvelope Γ Δ x τ

/-- Actual convexity comes directly from the existing envelope definition. -/
theorem sourceTestCurveJoinConvexEnvelope_convex (Γ Δ : SourceTestCurvePredata θ) (x : M) :
    SGPT.Convex.IsConvex (sourceTestCurveJoinConvexEnvelope Γ Δ x) :=
  SGPT.Convex.isConvex_lowerConvexEnvelope _

/-- The zero affine minorant excludes every bottom value of the actual envelope. -/
theorem sourceTestCurveJoinConvexEnvelope_nonneg (Γ Δ : SourceTestCurvePredata θ) (x : M) :
    (0 : ℝ → EReal) ≤ sourceTestCurveJoinConvexEnvelope Γ Δ x := by
  intro r
  change (0 : EReal) ≤ SGPT.Convex.lowerConvexEnvelope
    (fun s => -max (sourceTestCurveAt Γ s x) (sourceTestCurveAt Δ s x)) r
  exact SGPT.Convex.le_lowerConvexEnvelope
    (g := fun _ : ℝ => (0 : EReal))
    (by simpa only [EReal.coe_zero] using SGPT.Convex.isConvex_const (V := ℝ) 0)
    (fun s => EReal.neg_nonneg.mpr (max_le (Γ.at_le_zero s x) (Δ.at_le_zero s x))) r

/-- The real convex envelope lies below the first whole negative trace. -/
theorem sourceTestCurveJoinConvexEnvelope_le_left (Γ Δ : SourceTestCurvePredata θ) (x : M) :
    sourceTestCurveJoinConvexEnvelope Γ Δ x ≤ fun s => -sourceTestCurveAt Γ s x := by
  intro s
  exact (SGPT.Convex.lowerConvexEnvelope_le _ s).trans
    (EReal.neg_le_neg_iff.mpr (le_max_left _ _))

/-- The same entire-envelope bound for the second input. -/
theorem sourceTestCurveJoinConvexEnvelope_le_right (Γ Δ : SourceTestCurvePredata θ) (x : M) :
    sourceTestCurveJoinConvexEnvelope Γ Δ x ≤ fun s => -sourceTestCurveAt Δ s x := by
  intro s
  exact (SGPT.Convex.lowerConvexEnvelope_le _ s).trans
    (EReal.neg_le_neg_iff.mpr (le_max_right _ _))

/-- The literal raw concave maximum dominates the two whole original inputs. -/
theorem sourceTestCurveRawConcaveMaximum_ge (Γ Δ : SourceTestCurvePredata θ) (τ : ℝ) :
    (fun x => max (sourceTestCurveAt Γ τ x) (sourceTestCurveAt Δ τ x)) ≤
      sourceTestCurveRawConcaveMaximum Γ Δ τ := by
  intro x
  have h := EReal.neg_le_neg_iff.mpr (SGPT.Convex.lowerConvexEnvelope_le
    (fun s => -max (sourceTestCurveAt Γ s x) (sourceTestCurveAt Δ s x)) τ)
  change max (sourceTestCurveAt Γ τ x) (sourceTestCurveAt Δ τ x) ≤
    -SGPT.Convex.lowerConvexEnvelope
      (fun s => -max (sourceTestCurveAt Γ s x) (sourceTestCurveAt Δ s x)) τ
  simpa only [neg_neg] using h

/-- Move the actual finite time correction through the literal ALL-real
raw supremum, keeping every pole and every original branch. -/
theorem SourceTestCurvePredata.rawLegendre_sub_linear (Γ : SourceTestCurvePredata θ)
    (t τ : ℝ) (x : M) :
    sourceTestCurveRawLegendre Γ t x - ((t*τ : ℝ) : EReal) =
      ⨆ s : ℝ, sourceTestCurveAt Γ s x + ((t*(s-τ) : ℝ) : EReal) := by
  change (⨆ s : ℝ, ((t*s : ℝ) : EReal) + sourceTestCurveAt Γ s x) - _ = _
  rw [sub_eq_add_neg, ← EReal.coe_neg, ← iSup_add_coe]
  apply iSup_congr
  intro s
  rw [add_comm ((t*s : ℝ) : EReal), add_assoc, ← EReal.coe_add]
  congr 2
  ring

/-- A genuine terminal support condition manufactures antitonicity of the
corrected transform; no properness or nonpole input is needed. -/
theorem SourceTestCurvePredata.rawLegendre_corrected_antitone_of_support
    (Γ : SourceTestCurvePredata θ) (x : M) (τ : ℝ)
    (hsupport : ∀ s : ℝ, τ < s → sourceTestCurveAt Γ s x = ⊥) :
    Antitone (fun t : Ioi (0 : ℝ) =>
      sourceTestCurveRawLegendre Γ t.1 x - ((t.1*τ : ℝ) : EReal)) := by
  intro a b hab
  change sourceTestCurveRawLegendre Γ b.1 x - ((b.1*τ : ℝ) : EReal) ≤
    sourceTestCurveRawLegendre Γ a.1 x - ((a.1*τ : ℝ) : EReal)
  rw [Γ.rawLegendre_sub_linear, Γ.rawLegendre_sub_linear]
  apply iSup_mono
  intro s
  by_cases hs : s ≤ τ
  · exact add_le_add le_rfl (EReal.coe_le_coe
      (mul_le_mul_of_nonpos_right (show a.1 ≤ b.1 from hab) (sub_nonpos.mpr hs)))
  · simp only [hsupport s (lt_of_not_ge hs), EReal.bot_add, le_refl]

variable [CompactSpace M] [ConnectedSpace M]

/-- The negative actual inverse is an actual convex minorant of the raw
obstacle. This proves the envelope bound without any closedness assumption. -/
theorem sourceTestCurveRawConcaveMaximum_le_inverse (Γ Δ : SourceTestCurvePredata θ)
    (τ : ℝ) : sourceTestCurveRawConcaveMaximum Γ Δ τ ≤
      sourcePositiveRayInverse (sourceTestCurveMaxLegendreRay Γ Δ) τ := by
  intro x
  let L := sourceTestCurveMaxLegendreRay Γ Δ
  have hc : SGPT.Convex.IsConvex (fun s => -sourcePositiveRayInverse L s x) := by
    convert SGPT.Convex.isConvex_halfLineConjugate (fun t => sourceRayExtension L t x) using 1
    funext s
    exact (sourcePositiveRayInverse_conjugate L s x).symm
  have hm : (fun s => -sourcePositiveRayInverse L s x) ≤
      fun s => -max (sourceTestCurveAt Γ s x) (sourceTestCurveAt Δ s x) := by
    intro s
    apply EReal.neg_le_neg_iff.mpr
    exact max_le (sourceTestCurveMaxLegendreInverse_ge_left Γ Δ s x)
      (sourceTestCurveMaxLegendreInverse_ge_right Γ Δ s x)
  have h := EReal.neg_le_neg_iff.mpr (SGPT.Convex.le_lowerConvexEnvelope hc hm τ)
  change -SGPT.Convex.lowerConvexEnvelope
    (fun s => -max (sourceTestCurveAt Γ s x) (sourceTestCurveAt Δ s x)) τ ≤
      sourcePositiveRayInverse L τ x
  simpa only [neg_neg] using h

/-- At a terminal support point, diagonal infimum commutes with the
finite maximum, by the manufactured antitonicity and exact original inversions.
Both-all-pole and literal cutoff cases remain included. -/
theorem sourceTestCurveMaxLegendreInverse_eq_at_of_support (Γ Δ : SourceTestCurvePredata θ)
    (τ : ℝ) (x : M)
    (hΓ : ∀ s : ℝ, τ < s → sourceTestCurveAt Γ s x = ⊥)
    (hΔ : ∀ s : ℝ, τ < s → sourceTestCurveAt Δ s x = ⊥) :
    sourcePositiveRayInverse (sourceTestCurveMaxLegendreRay Γ Δ) τ x =
      max (sourceTestCurveAt Γ τ x) (sourceTestCurveAt Δ τ x) := by
  let F : Ioi (0 : ℝ) → EReal := fun t =>
    sourceTestCurveRawLegendre Γ t.1 x - ((t.1*τ : ℝ) : EReal)
  let G : Ioi (0 : ℝ) → EReal := fun t =>
    sourceTestCurveRawLegendre Δ t.1 x - ((t.1*τ : ℝ) : EReal)
  have hF : Antitone F := Γ.rawLegendre_corrected_antitone_of_support x τ hΓ
  have hG : Antitone G := Δ.rawLegendre_corrected_antitone_of_support x τ hΔ
  have hraw : sourcePositiveRayInverse (sourceTestCurveMaxLegendreRay Γ Δ) τ x =
      ⨅ t : Ioi (0 : ℝ), max (F t) (G t) := by
    apply iInf_congr
    intro t
    rw [sourceTestCurveMaxLegendreRay_positive Γ Δ t.2]
    change max (sourceTestCurveRawLegendre Γ t.1 x) (sourceTestCurveRawLegendre Δ t.1 x) -
      ((t.1*τ : ℝ) : EReal) =
      max (sourceTestCurveRawLegendre Γ t.1 x - ((t.1*τ : ℝ) : EReal))
        (sourceTestCurveRawLegendre Δ t.1 x - ((t.1*τ : ℝ) : EReal))
    rcases le_total (sourceTestCurveRawLegendre Γ t.1 x)
      (sourceTestCurveRawLegendre Δ t.1 x) with h | h
    · rw [max_eq_right h, max_eq_right (EReal.sub_le_sub h le_rfl)]
    · rw [max_eq_left h, max_eq_left (EReal.sub_le_sub h le_rfl)]
  have hd : (⨅ t : Ioi (0 : ℝ), max (F t) (G t)) = max (⨅ t, F t) (⨅ t, G t) := by
    apply le_antisymm
    · calc
        _ ≤ ⨅ p : Ioi (0 : ℝ) × Ioi (0 : ℝ), F p.1 ⊔ G p.2 := by
          apply le_iInf
          intro p
          let k : Ioi (0 : ℝ) := ⟨max p.1.1 p.2.1,
            lt_of_lt_of_le p.1.2 (le_max_left p.1.1 p.2.1)⟩
          exact (iInf_le (fun t : Ioi (0 : ℝ) => max (F t) (G t)) k).trans
            (max_le_max (hF (show p.1 ≤ k from le_max_left _ _))
              (hG (show p.2 ≤ k from le_max_right _ _)))
        _ = _ := iInf_sup_iInf.symm
    · exact le_iInf fun t => max_le_max (iInf_le F t) (iInf_le G t)
  rw [hraw, hd, ← Γ.at_eq_iInf_positive_rawLegendre τ x,
    ← Δ.at_eq_iInf_positive_rawLegendre τ x]

/-- The literal upper concave envelope is already identified at every
terminal support point, with no pole or endpoint exception. -/
theorem sourceTestCurveRawConcaveMaximum_eq_at_of_support (Γ Δ : SourceTestCurvePredata θ)
    (τ : ℝ) (x : M)
    (hΓ : ∀ s : ℝ, τ < s → sourceTestCurveAt Γ s x = ⊥)
    (hΔ : ∀ s : ℝ, τ < s → sourceTestCurveAt Δ s x = ⊥) :
    sourceTestCurveRawConcaveMaximum Γ Δ τ x =
      sourcePositiveRayInverse (sourceTestCurveMaxLegendreRay Γ Δ) τ x := by
  apply le_antisymm
  · exact sourceTestCurveRawConcaveMaximum_le_inverse Γ Δ τ x
  · rw [sourceTestCurveMaxLegendreInverse_eq_at_of_support Γ Δ τ x hΓ hΔ]
    exact sourceTestCurveRawConcaveMaximum_ge Γ Δ τ x

omit [CompactSpace M] [ConnectedSpace M] in
/-- An actual common affine minorant with positive slope bounds the actual
positive-time inverse, by evaluating its real raw transforms at that slope. -/
theorem sourceTestCurveMaxLegendreInverse_le_of_common_affine
    (Γ Δ : SourceTestCurvePredata θ) (τ : ℝ) (x : M) {p c : ℝ} (hp : 0 < p)
    (hminor : ∀ s, ((p*s+c : ℝ) : EReal) ≤
      -max (sourceTestCurveAt Γ s x) (sourceTestCurveAt Δ s x)) :
    sourcePositiveRayInverse (sourceTestCurveMaxLegendreRay Γ Δ) τ x ≤
      -((p*τ+c : ℝ) : EReal) := by
  have hF (A : SourceTestCurvePredata θ)
      (hA : ∀ s, ((p*s+c : ℝ) : EReal) ≤ -sourceTestCurveAt A s x) :
      sourceTestCurveRawLegendre A p x ≤ ((-c : ℝ) : EReal) := by
    apply iSup_le
    intro s
    have hh := (SGPT.Convex.real_sub_le_iff_comm (p*s) (-sourceTestCurveAt A s x)
      ((-c : ℝ) : EReal)).mpr (by
        simpa only [← EReal.coe_sub, sub_neg_eq_add] using hA s)
    simpa only [sub_eq_add_neg, neg_neg] using hh
  have hG := hF Γ (fun s => (hminor s).trans (EReal.neg_le_neg_iff.mpr (le_max_left _ _)))
  have hH := hF Δ (fun s => (hminor s).trans (EReal.neg_le_neg_iff.mpr (le_max_right _ _)))
  have hi := iInf_le (fun t : Ioi (0 : ℝ) =>
    sourceRayExtension (sourceTestCurveMaxLegendreRay Γ Δ) t.1 x -
      ((t.1*τ : ℝ) : EReal)) ⟨p,hp⟩
  rw [sourceTestCurveMaxLegendreRay_positive Γ Δ hp] at hi
  apply hi.trans
  have hh := EReal.sub_le_sub (max_le hG hH) (le_refl ((p*τ : ℝ) : EReal))
  rw [← EReal.coe_sub] at hh
  rw [← EReal.coe_neg]
  convert hh using 1
  congr 1
  ring

omit [CompactSpace M] [ConnectedSpace M] in
/-- A finite input above the parameter manufactures properness and an
actual interior touching affine minorant of the literal convex envelope.
The existing support theorem needs NO global lower-semicontinuity premise. -/
theorem sourceTestCurveJoinConvexEnvelope_exists_touching_affine
    (Γ Δ : SourceTestCurvePredata θ) (x : M) {τ a : ℝ} (ha : τ < a)
    (hfinite : sourceTestCurveAt Γ a x ≠ ⊥ ∨ sourceTestCurveAt Δ a x ≠ ⊥) :
    ∃ (m : ℝ →L[ℝ] ℝ) (c : ℝ),
      (∀ z, ((m z+c : ℝ) : EReal) ≤ sourceTestCurveJoinConvexEnvelope Γ Δ x z) ∧
      ((m τ+c : ℝ) : EReal) = sourceTestCurveJoinConvexEnvelope Γ Δ x τ := by
  let k := sourceTestCurveJoinConvexEnvelope Γ Δ x
  have hchoose : ∃ A : SourceTestCurvePredata θ,
      k ≤ (fun s => -sourceTestCurveAt A s x) ∧ sourceTestCurveAt A a x ≠ ⊥ := by
    rcases hfinite with hG | hH
    · exact ⟨Γ,sourceTestCurveJoinConvexEnvelope_le_left Γ Δ x,hG⟩
    · exact ⟨Δ,sourceTestCurveJoinConvexEnvelope_le_right Γ Δ x,hH⟩
  obtain ⟨A,hkA,hAa⟩ := hchoose
  have htop : -sourceTestCurveAt A a x ≠ ⊤ := by simpa using hAa
  have hproper : SGPT.Convex.IsProper k := by
    refine ⟨sourceTestCurveJoinConvexEnvelope_convex Γ Δ x,
      ⟨a,(hkA a).trans_lt (lt_top_iff_ne_top.mpr htop)⟩,?_⟩
    intro s
    exact ne_bot_of_le_ne_bot (by norm_num : (0 : EReal) ≠ ⊥)
      (sourceTestCurveJoinConvexEnvelope_nonneg Γ Δ x s)
  have hsub : Iio a ⊆ SGPT.Convex.effectiveDomain k := by
    intro z hz
    exact ((hkA z).trans (EReal.neg_le_neg_iff.mpr
      (A.at_antitone x hz.le))).trans_lt (lt_top_iff_ne_top.mpr htop)
  have hI : τ ∈ intrinsicInterior ℝ (SGPT.Convex.effectiveDomain k) := by
    apply interior_subset_intrinsicInterior
    exact mem_interior_iff_mem_nhds.mpr (Filter.mem_of_superset (Iio_mem_nhds ha) hsub)
  exact SGPT.Convex.exists_touching_continuous_affine_minorant hproper hI

omit [CompactSpace M] [ConnectedSpace M] in
/-- Interior properness and the EXISTING actual touching-affine mother
manufacture strictly positive common minorants. No LSC/closedness of the
convex envelope is assumed, and its entire original cutoff is retained. -/
theorem sourceTestCurveJoinConvexEnvelope_exists_positive_affine
    (Γ Δ : SourceTestCurvePredata θ) (x : M) {τ a : ℝ} (ha : τ < a)
    (hfinite : sourceTestCurveAt Γ a x ≠ ⊥ ∨ sourceTestCurveAt Δ a x ≠ ⊥)
    (r : ℝ) (hr : (r : EReal) < sourceTestCurveJoinConvexEnvelope Γ Δ x τ) :
    ∃ p c : ℝ, 0 < p ∧ r < p*τ+c ∧ ∀ s, ((p*s+c : ℝ) : EReal) ≤
      -max (sourceTestCurveAt Γ s x) (sourceTestCurveAt Δ s x) := by
  let k := sourceTestCurveJoinConvexEnvelope Γ Δ x
  have hchoose : ∃ A : SourceTestCurvePredata θ,
      k ≤ (fun s => -sourceTestCurveAt A s x) ∧ sourceTestCurveAt A a x ≠ ⊥ := by
    rcases hfinite with hG | hH
    · exact ⟨Γ,sourceTestCurveJoinConvexEnvelope_le_left Γ Δ x,hG⟩
    · exact ⟨Δ,sourceTestCurveJoinConvexEnvelope_le_right Γ Δ x,hH⟩
  obtain ⟨A,hkA,hAa⟩ := hchoose
  have htop : -sourceTestCurveAt A a x ≠ ⊤ := by simpa using hAa
  have hbot : -sourceTestCurveAt A a x ≠ ⊥ :=
    ne_bot_of_le_ne_bot (by norm_num : (0 : EReal) ≠ ⊥)
      (EReal.neg_nonneg.mpr (A.at_le_zero a x))
  obtain ⟨m,c,hminor,htouch⟩ :=
    sourceTestCurveJoinConvexEnvelope_exists_touching_affine Γ Δ x ha hfinite
  change ∀ z, ((m z+c : ℝ) : EReal) ≤ k z at hminor
  change ((m τ+c : ℝ) : EReal) = k τ at htouch
  have hmval (z : ℝ) : m z = z*m 1 := by
    simpa only [smul_eq_mul,mul_one] using m.map_smul z (1 : ℝ)
  have habove : r < m τ+c := by
    have hh := hr
    change (r : EReal) < k τ at hh
    rw [← htouch,EReal.coe_lt_coe_iff] at hh
    exact hh
  have hm : 0 ≤ m 1 := by
    let H := (-sourceTestCurveAt A a x).toReal
    have hH : -sourceTestCurveAt A a x = (H : EReal) :=
      (EReal.coe_toReal htop hbot).symm
    by_contra hn
    have hn : m 1 < 0 := lt_of_not_ge hn
    let z : ℝ := min a ((H-c+1)/m 1)
    have hz : z ≤ a := min_le_left _ _
    have hlo : H-c+1 ≤ z*m 1 := by
      have hh := mul_le_mul_of_nonpos_right (min_le_right a ((H-c+1)/m 1)) hn.le
      simpa only [div_mul_cancel₀ _ (ne_of_lt hn)] using hh
    have hup : ((m z+c : ℝ) : EReal) ≤ (H : EReal) := by
      rw [← hH]
      exact ((hminor z).trans (hkA z)).trans (EReal.neg_le_neg_iff.mpr (A.at_antitone x hz))
    rw [EReal.coe_le_coe_iff,hmval] at hup
    linarith
  let C := max Γ.max Δ.max
  obtain ⟨ε,hε,hsmall⟩ := exists_pos_mul_lt (sub_pos.mpr habove) |τ-C|
  refine ⟨m 1+ε,c-ε*C,by linarith,?_,?_⟩
  · have habs := mul_le_mul_of_nonneg_left (neg_abs_le (τ-C)) hε.le
    rw [hmval τ] at habove hsmall
    nlinarith
  · intro z
    by_cases hz : z ≤ C
    · apply le_trans (EReal.coe_le_coe (show
          (m 1+ε)*z+(c-ε*C) ≤ m z+c from ?_))
        ((hminor z).trans (SGPT.Convex.lowerConvexEnvelope_le _ z))
      rw [hmval z]
      nlinarith [mul_le_mul_of_nonneg_left hz hε.le]
    · have hG : Γ.max < z := (le_max_left Γ.max Δ.max).trans_lt (lt_of_not_ge hz)
      have hH : Δ.max < z := (le_max_right Γ.max Δ.max).trans_lt (lt_of_not_ge hz)
      simp only [sourceTestCurveAt_of_gt Γ hG,sourceTestCurveAt_of_gt Δ hH,
        Pi.bot_apply,max_self,EReal.neg_bot,le_top]

/-- The EVERY-POINT literal negative-LCE equals the actual positive-time
inverse. Interior touching support and terminal-support diagonal infima
supply the two cases, including all poles, cutoffs and super-cutoff values. -/
theorem sourceTestCurveRawConcaveMaximum_eq_inverse (Γ Δ : SourceTestCurvePredata θ)
    (τ : ℝ) : sourceTestCurveRawConcaveMaximum Γ Δ τ =
      sourcePositiveRayInverse (sourceTestCurveMaxLegendreRay Γ Δ) τ := by
  funext x
  classical
  by_cases h : ∃ a : ℝ, τ < a ∧
      (sourceTestCurveAt Γ a x ≠ ⊥ ∨ sourceTestCurveAt Δ a x ≠ ⊥)
  · obtain ⟨a,ha,hfin⟩ := h
    have hk : sourceTestCurveJoinConvexEnvelope Γ Δ x τ ≤
        -sourcePositiveRayInverse (sourceTestCurveMaxLegendreRay Γ Δ) τ x := by
      by_contra hn
      obtain ⟨r,hir,hrk⟩ := EReal.exists_between_coe_real (lt_of_not_ge hn)
      obtain ⟨p,c,hp,hrp,hminor⟩ :=
        sourceTestCurveJoinConvexEnvelope_exists_positive_affine Γ Δ x ha hfin r hrk
      have hi := sourceTestCurveMaxLegendreInverse_le_of_common_affine Γ Δ τ x hp hminor
      have hterm : ((p*τ+c : ℝ) : EReal) ≤
          -sourcePositiveRayInverse (sourceTestCurveMaxLegendreRay Γ Δ) τ x := by
        simpa only [neg_neg] using EReal.neg_le_neg_iff.mpr hi
      exact lt_asymm hir ((EReal.coe_lt_coe hrp).trans_le hterm)
    apply le_antisymm (sourceTestCurveRawConcaveMaximum_le_inverse Γ Δ τ x)
    have hh := EReal.neg_le_neg_iff.mpr hk
    simpa only [neg_neg,sourceTestCurveRawConcaveMaximum] using hh
  · apply sourceTestCurveRawConcaveMaximum_eq_at_of_support Γ Δ τ x
    · intro s hs
      by_contra hn
      exact h ⟨s,hs,Or.inl hn⟩
    · intro s hs
      by_contra hn
      exact h ⟨s,hs,Or.inr hn⟩

variable [MeasurableSpace M] [BorelSpace M]

/-- The literal raw upper-concave-envelope slice is genuinely PSH through
the actual cutoff, by the proved EVERY-POINT identity, not QE alone. -/
theorem sourceTestCurveRawConcaveMaximum_thetaPSH (omega : KahlerBackground n M)
    (Γ Δ : SourceTestCurvePredata θ) {τ : ℝ} (hτ : τ ≤ max Γ.max Δ.max) :
    (ofFixedModel n M).IsThetaPSH θ (sourceTestCurveRawConcaveMaximum Γ Δ τ) := by
  rw [sourceTestCurveRawConcaveMaximum_eq_inverse]
  exact sourceTestCurveMaxLegendreInverse_thetaPSH omega Γ Δ hτ

/-- Strictly below the actual maximum cutoff, the LITERAL raw concave
envelope has positive ACTUAL mass, with genuine PSH already manufactured. -/
theorem sourceTestCurveRawConcaveMaximum_mass_positive (omega : KahlerBackground n M)
    (Γ Δ : SourceTestCurve θ) {τ : ℝ} (hτ : τ < max Γ.max Δ.max) :
    0 < sourcePotentialNonPluripolarMeasure θ
      (sourceTestCurveRawConcaveMaximum Γ.toSourceTestCurvePredata Δ.toSourceTestCurvePredata τ)
      (sourceTestCurveRawConcaveMaximum_thetaPSH omega Γ.toSourceTestCurvePredata
        Δ.toSourceTestCurvePredata hτ.le) univ := by
  have hmeasure (u v : M → EReal) (hu : (ofFixedModel n M).IsThetaPSH θ u)
      (hv : (ofFixedModel n M).IsThetaPSH θ v) (heq : u = v) :
      sourcePotentialNonPluripolarMeasure θ u hu univ =
        sourcePotentialNonPluripolarMeasure θ v hv univ := by
    cases heq
    rfl
  rw [hmeasure _ _
    (sourceTestCurveRawConcaveMaximum_thetaPSH omega Γ.toSourceTestCurvePredata
      Δ.toSourceTestCurvePredata hτ.le)
    (sourceTestCurveMaxLegendreInverse_thetaPSH omega Γ.toSourceTestCurvePredata
      Δ.toSourceTestCurvePredata hτ.le)
    (sourceTestCurveRawConcaveMaximum_eq_inverse Γ.toSourceTestCurvePredata
      Δ.toSourceTestCurvePredata τ)]
  exact sourceTestCurveMaxLegendreInverse_mass_positive omega Γ Δ hτ

end SGPT.PSH.VariableComplexAtlas
