import SGPT.NAPotential.SemipositiveIndex

/-! The actual arbitrary-S NA projective limit. S contains all genuine
Kähler indices, but is not assumed closed under addition or directed in the
source reverse order. All recovery and family-independence laws are proved. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.VariableComplexAtlas.WholeClosureNA.SemipositiveProjective

open Set
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]
  {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)}

abbrev Member (S : Set (Index n M)) := {η // η ∈ S}

def ContainsKahler (S : Set (Index n M)) : Prop := ∀ κ : SourceKahlerForm n M, ofKahler κ ∈ S

def kahlerMember {S : Set (Index n M)} (hS : ContainsKahler S) (κ : SourceKahlerForm n M) : Member S :=
  ⟨ofKahler κ, hS κ⟩

/-- The entire actual source compatible family, not a certificate or an
intrinsic-type replacement of the projective limit. -/
structure NALimit (θ : AtlasClosedRealOneOneForm (ofFixedModel n M)) (S : Set (Index n M)) where
  family : ∀ η : Member S, SourceNAPotential (background θ η.val)
  compatible : ∀ (η ζ : Member S) (h : IndexLE η.val ζ.val),
    (family η).transition (background_difference θ h) = family ζ

@[ext] theorem NALimit.ext {S : Set (Index n M)} {P Q : NALimit θ S}
    (h : ∀ η, P.family η = Q.family η) : P = Q := by
  cases P with
  | mk p hp =>
    cases Q with
    | mk q hq =>
      have he : p = q := funext h
      subst q
      rfl

/-- All-family intrinsic independence is manufactured from an actual Kähler
upper bound, even if the ambient subset S is not closed under addition. -/
theorem NALimit.family_POrder_equivalent {S : Set (Index n M)}
    (omega : KahlerBackground n M) (hS : ContainsKahler S) (P : NALimit θ S)
    (η ζ : Member S) :
    SourceNAPOrder (P.family η) (P.family ζ) ∧ SourceNAPOrder (P.family ζ) (P.family η) := by
  obtain ⟨κ, hη, hζ⟩ := exists_kahler_commonUpper omega η.val ζ.val
  let ν := kahlerMember hS κ
  have he := (P.family η).transition_POrder_equivalent (β := background θ ν.val) omega (background_difference θ hη)
  have hz := (P.family ζ).transition_POrder_equivalent (β := background θ ν.val) omega (background_difference θ hζ)
  rw [P.compatible η ν hη] at he
  rw [P.compatible ζ ν hζ] at hz
  exact ⟨he.1.trans hz.2, hz.1.trans he.2⟩

/-- Actual restriction to the existing geometric Kähler inverse system,
with whole-background equality transported explicitly. -/
def NALimit.restrictKahler {S : Set (Index n M)} (omega : KahlerBackground n M)
    (hS : ContainsKahler S) (P : NALimit θ S) : SourceNAProjectiveLimit θ where
  family κ := (P.family (kahlerMember hS κ)).castBackground (background_ofKahler θ κ)
  compatible κ ζ h := by
    have he := P.family_POrder_equivalent omega hS (kahlerMember hS κ) (kahlerMember hS ζ)
    have hκ := (P.family (kahlerMember hS κ)).castBackground_POrder_equivalent omega
      (background_ofKahler θ κ)
    have hζ := (P.family (kahlerMember hS ζ)).castBackground_POrder_equivalent omega
      (background_ofKahler θ ζ)
    have ht := ((P.family (kahlerMember hS κ)).castBackground (background_ofKahler θ κ)).transition_POrder_equivalent (β := sourceNAComponentBackground θ ζ) omega (sourceNAComponentBackground_difference θ h)
    exact SourceNAPOrder.antisymm
      (ht.2.trans (hκ.2.trans (he.1.trans hζ.1)))
      (hζ.2.trans (he.2.trans (hκ.1.trans ht.1)))

/-- The inverse system itself is produced by the genuine existing Kähler
projective-limit inverse. Nothing like a recovered system is caller data. -/
def NALimit.recover {S : Set (Index n M)} (omega : KahlerBackground n M)
    (hS : ContainsKahler S) (P : NALimit θ S) : SourceNAPotential θ :=
  (P.restrictKahler omega hS).preimage

/-- Recovery has the intrinsic type of EVERY independently chosen member,
not merely those in the Kähler restriction. -/
theorem NALimit.recover_POrder_equivalent {S : Set (Index n M)}
    (omega : KahlerBackground n M) (hS : ContainsKahler S) (P : NALimit θ S) (η : Member S) :
    SourceNAPOrder (P.recover omega hS) (P.family η) ∧
      SourceNAPOrder (P.family η) (P.recover omega hS) := by
  let κ := sourceKahlerFormOfBackground omega
  let Γ := P.recover omega hS
  have hb := Γ.backgroundChange_POrder_equivalent omega (sourceNAKahlerAtlasForm κ)
    (sourceNAKahlerAtlasForm_semipositive κ)
  change SourceNAPOrder Γ (Γ.kahlerProjection κ) ∧ SourceNAPOrder (Γ.kahlerProjection κ) Γ at hb
  have he : Γ.kahlerProjection κ = (P.restrictKahler omega hS).family κ :=
    congrArg (fun Q : SourceNAProjectiveLimit θ => Q.family κ)
      (P.restrictKahler omega hS).toProjectiveLimit_preimage
  rw [he] at hb
  have hc := (P.family (kahlerMember hS κ)).castBackground_POrder_equivalent omega
    (background_ofKahler θ κ)
  have hf := P.family_POrder_equivalent omega hS (kahlerMember hS κ) η
  exact ⟨hb.1.trans (hc.2.trans hf.1), hf.2.trans (hc.1.trans hb.2)⟩

/-- Original semipositive augmentation at an arbitrary genuine source index. -/
def toNALimit (omega : KahlerBackground n M) (S : Set (Index n M))
    (Γ : SourceNAPotential θ) : NALimit θ S where
  family η := Γ.backgroundChange (nativeClosedFormToAtlas (representative η.val))
    (by simpa only [sourceNativeAtlasForm_roundTrip] using representative_semipositive η.val)
  compatible η ζ h := by
    have hη := Γ.backgroundChange_POrder_equivalent omega
      (nativeClosedFormToAtlas (representative η.val))
      (by simpa only [sourceNativeAtlasForm_roundTrip] using representative_semipositive η.val)
    have hζ := Γ.backgroundChange_POrder_equivalent omega
      (nativeClosedFormToAtlas (representative ζ.val))
      (by simpa only [sourceNativeAtlasForm_roundTrip] using representative_semipositive ζ.val)
    have ht := (Γ.backgroundChange (nativeClosedFormToAtlas (representative η.val))
      (by simpa only [sourceNativeAtlasForm_roundTrip] using representative_semipositive η.val)).transition_POrder_equivalent (β := background θ ζ.val) omega (background_difference θ h)
    exact SourceNAPOrder.antisymm
      (ht.2.trans (hη.2.trans hζ.1)) (hζ.2.trans (hη.1.trans ht.1))

/-- Both intrinsic comparisons with the actual original Γ. -/
theorem toNALimit_family_POrder_equivalent (omega : KahlerBackground n M)
    {S : Set (Index n M)} (Γ : SourceNAPotential θ) (η : Member S) :
    SourceNAPOrder Γ ((toNALimit omega S Γ).family η) ∧
      SourceNAPOrder ((toNALimit omega S Γ).family η) Γ :=
  Γ.backgroundChange_POrder_equivalent omega
    (nativeClosedFormToAtlas (representative η.val))
    (by simpa only [sourceNativeAtlasForm_roundTrip] using representative_semipositive η.val)

/-- The manufactured recovery extends back to the WHOLE supplied family. -/
theorem NALimit.toNALimit_recover {S : Set (Index n M)}
    (omega : KahlerBackground n M) (hS : ContainsKahler S) (P : NALimit θ S) :
    toNALimit omega S (P.recover omega hS) = P := by
  apply NALimit.ext
  intro η
  have hb := toNALimit_family_POrder_equivalent omega (P.recover omega hS) η
  have hr := P.recover_POrder_equivalent omega hS η
  exact SourceNAPOrder.antisymm (hb.2.trans hr.1) (hr.2.trans hb.1)

theorem toNALimit_injective {S : Set (Index n M)}
    (omega : KahlerBackground n M) (hS : ContainsKahler S) :
    Function.Injective (toNALimit (θ := θ) omega S) := by
  intro Γ Δ h
  let η := kahlerMember hS (sourceKahlerFormOfBackground omega)
  have he := congrArg (fun P : NALimit θ S => P.family η) h
  have hΓ := toNALimit_family_POrder_equivalent omega Γ η
  have hΔ := toNALimit_family_POrder_equivalent omega Δ η
  rw [he] at hΓ
  exact SourceNAPOrder.antisymm (hΓ.1.trans hΔ.2) (hΔ.1.trans hΓ.2)

/-- All-dimensional full non-positive family bijection, for any actual S
containing the Kähler indices. Both index restriction and inverse are produced. -/
theorem toNALimit_bijective {S : Set (Index n M)}
    (omega : KahlerBackground n M) (hS : ContainsKahler S) :
    Function.Bijective (toNALimit (θ := θ) omega S) :=
  ⟨toNALimit_injective omega hS, fun P => ⟨P.recover omega hS, P.toNALimit_recover omega hS⟩⟩

/-- Actual NA order is preserved and reflected componentwise, even across
independently specified original backgrounds. -/
theorem toNALimit_order_iff (omega : KahlerBackground n M) {S : Set (Index n M)}
    (hS : ContainsKahler S) {σ : AtlasClosedRealOneOneForm (ofFixedModel n M)}
    (Γ : SourceNAPotential θ) (Δ : SourceNAPotential σ) :
    SourceNAPOrder Γ Δ ↔ ∀ η : Member S,
      SourceNAPOrder ((toNALimit omega S Γ).family η) ((toNALimit omega S Δ).family η) := by
  constructor
  · intro h η
    have hg := toNALimit_family_POrder_equivalent omega Γ η
    have hd := toNALimit_family_POrder_equivalent omega Δ η
    exact hg.2.trans (h.trans hd.1)
  · intro h
    let η := kahlerMember hS (sourceKahlerFormOfBackground omega)
    have hg := toNALimit_family_POrder_equivalent omega Γ η
    have hd := toNALimit_family_POrder_equivalent omega Δ η
    exact hg.1.trans ((h η).trans hd.2)

/-- The actual recovered system is independent of the auxiliary Kähler
presentation used for restriction and its inverse. -/
theorem NALimit.recover_independent {S : Set (Index n M)}
    (omega omega' : KahlerBackground n M) (hS : ContainsKahler S) (P : NALimit θ S) :
    P.recover omega hS = P.recover omega' hS := by
  let η := kahlerMember hS (sourceKahlerFormOfBackground omega)
  have h := P.recover_POrder_equivalent omega hS η
  have h' := P.recover_POrder_equivalent omega' hS η
  exact SourceNAPOrder.antisymm (h.1.trans h'.2) (h'.1.trans h.2)

def naLimitEquiv {S : Set (Index n M)} (omega : KahlerBackground n M)
    (hS : ContainsKahler S) : SourceNAPotential θ ≃ NALimit θ S where
  toFun := toNALimit omega S
  invFun := NALimit.recover omega hS
  left_inv Γ := toNALimit_injective omega hS ((toNALimit omega S Γ).toNALimit_recover omega hS)
  right_inv := NALimit.toNALimit_recover omega hS

end SGPT.PSH.VariableComplexAtlas.WholeClosureNA.SemipositiveProjective
