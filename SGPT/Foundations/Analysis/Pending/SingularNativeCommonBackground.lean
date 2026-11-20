import SGPT.Foundations.Analysis.Pending.SingularNativeBackgroundIndependence
import SGPT.Foundations.Analysis.Pending.KahlerDomination
import SGPT.Foundations.Analysis.Pending.PluripolarCapacityDichotomy

set_option autoImplicit false

/-! # Actual common-background native singularity convergence

SGPT PDF0237--0238 Corollary 6.2.9, final background-independence
consequence: genuine compact domination constructs the common smooth
background; native auxiliary choices are transported through actual
defining distances. No enlarged convergence certificate is an input.
-/

open Set Filter
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.SingularNativeCommonBackground

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus
  ThetaPshL1Topology SingularCanonicalSingularityDistance
  SingularNativeBackgroundIndependence

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M]

private theorem tendsto_native_change_auxiliary (omega κ : KahlerBackground n M)
    (θ : ClosedRealOneOneForm n M) (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    {I : Type*} (F : Filter I) (w : I → ThetaPshL1 θ.val) (v : ThetaPshL1 θ.val)
    (hlim : Tendsto w F (@nhds (ThetaPshL1 θ.val)
      (singularityPseudoMetricSpace omega θ hbig).toUniformSpace.toTopologicalSpace v)) :
    Tendsto w F (@nhds (ThetaPshL1 θ.val)
      (singularityPseudoMetricSpace κ θ hbig).toUniformSpace.toTopologicalSpace v) := by
  let := singularityPseudoMetricSpace omega θ hbig
  let : TopologicalSpace (ThetaPshL1 θ.val) :=
    (singularityPseudoMetricSpace omega θ hbig).toUniformSpace.toTopologicalSpace
  have hd : Tendsto (fun i => (singularityDistance omega θ hbig (w i).val v.val).toReal)
      F (𝓝 0) := by
    simpa only [dist_eq_singularityDistance_toReal omega θ hbig] using
      (tendsto_iff_dist_tendsto_zero.mp hlim)
  let := singularityPseudoMetricSpace κ θ hbig
  let : TopologicalSpace (ThetaPshL1 θ.val) :=
    (singularityPseudoMetricSpace κ θ hbig).toUniformSpace.toTopologicalSpace
  apply tendsto_iff_dist_tendsto_zero.mpr
  simpa only [dist_eq_singularityDistance_toReal κ θ hbig, singularityDistance] using hd

private theorem tendsto_native_iff_of_form_eq (omega : KahlerBackground n M)
    (θ σ : ClosedRealOneOneForm n M) (heq : θ = σ)
    (hθ : IsBigClass (RealBottChern.ofRepresentative θ))
    (hσ : IsBigClass (RealBottChern.ofRepresentative σ))
    {I : Type*} (F : Filter I) {u : I → M → EReal} {v : M → EReal}
    (huθ : ∀ i, IsThetaPshPotential θ.val (u i))
    (hvθ : IsThetaPshPotential θ.val v)
    (huσ : ∀ i, IsThetaPshPotential σ.val (u i))
    (hvσ : IsThetaPshPotential σ.val v) :
    Tendsto (fun i => (⟨u i, huθ i⟩ : ThetaPshL1 θ.val)) F
      (@nhds (ThetaPshL1 θ.val)
        (singularityPseudoMetricSpace omega θ hθ).toUniformSpace.toTopologicalSpace ⟨v, hvθ⟩) ↔
    Tendsto (fun i => (⟨u i, huσ i⟩ : ThetaPshL1 σ.val)) F
      (@nhds (ThetaPshL1 σ.val)
        (singularityPseudoMetricSpace omega σ hσ).toUniformSpace.toTopologicalSpace ⟨v, hvσ⟩) := by
  subst σ
  rfl

private theorem tendsto_native_of_common_backgrounds (omega : KahlerBackground n M)
    (θ σ : ClosedRealOneOneForm n M)
    (hθ : IsBigClass (RealBottChern.ofRepresentative θ))
    (hσ : IsBigClass (RealBottChern.ofRepresentative σ))
    {I : Type*} (F : Filter I) {u : I → M → EReal} {v : M → EReal}
    (huθ : ∀ i, IsThetaPshPotential θ.val (u i))
    (hvθ : IsThetaPshPotential θ.val v)
    (huσ : ∀ i, IsThetaPshPotential σ.val (u i))
    (hvσ : IsThetaPshPotential σ.val v)
    (hlim : Tendsto (fun i => (⟨u i, huθ i⟩ : ThetaPshL1 θ.val)) F
      (@nhds (ThetaPshL1 θ.val)
        (singularityPseudoMetricSpace omega θ hθ).toUniformSpace.toTopologicalSpace ⟨v, hvθ⟩)) :
    Tendsto (fun i => (⟨u i, huσ i⟩ : ThetaPshL1 σ.val)) F
      (@nhds (ThetaPshL1 σ.val)
        (singularityPseudoMetricSpace omega σ hσ).toUniformSpace.toTopologicalSpace ⟨v, hvσ⟩) := by
  obtain ⟨C, hC, hK⟩ :=
    KahlerDomination.exists_pos_isKahler_add_smul omega (σ - θ)
  let κ : KahlerBackground n M := ⟨σ - θ + C • omega.form, hK⟩
  let κC := KahlerBackground.smul hC omega
  let Wθ : I → ThetaPshL1 θ.val := fun i => ⟨u i, huθ i⟩
  let Vθ : ThetaPshL1 θ.val := ⟨v, hvθ⟩
  let Wσ : I → ThetaPshL1 σ.val := fun i => ⟨u i, huσ i⟩
  let Vσ : ThetaPshL1 σ.val := ⟨v, hvσ⟩
  have hκ := tendsto_native_change_auxiliary omega κ θ hθ F Wθ Vθ hlim
  have hlarge := (tendsto_native_iff_add_kahler κ θ hθ F Wθ Vθ).mp hκ
  have hbigLarge : IsBigClass (RealBottChern.ofRepresentative (θ + κ.form)) := by
    simpa only [one_smul] using
      PositiveCurrentAssembly.isBigClass_add_smul_of_isThetaPshPotential κ θ hvθ zero_lt_one
  let WL : I → ThetaPshL1 (θ + κ.form).val := fun i =>
    ⟨u i, LocalPotentials.isThetaPshPotential_add_of_semipositive (huθ i) κ.isSemipositive⟩
  let VL : ThetaPshL1 (θ + κ.form).val :=
    ⟨v, LocalPotentials.isThetaPshPotential_add_of_semipositive hvθ κ.isSemipositive⟩
  have hlargeC := tendsto_native_change_auxiliary κ κC (θ + κ.form) hbigLarge F WL VL hlarge
  have hforms : θ + κ.form = σ + κC.form := by
    dsimp only [κ, κC, KahlerBackground.smul_form]
    module
  have hbigOther : IsBigClass (RealBottChern.ofRepresentative (σ + κC.form)) := by
    simpa only [one_smul] using
      PositiveCurrentAssembly.isBigClass_add_smul_of_isThetaPshPotential κC σ hvσ zero_lt_one
  have hOther := (tendsto_native_iff_of_form_eq κC (θ + κ.form) (σ + κC.form)
    hforms hbigLarge hbigOther F
    (fun i => LocalPotentials.isThetaPshPotential_add_of_semipositive (huθ i) κ.isSemipositive)
    (LocalPotentials.isThetaPshPotential_add_of_semipositive hvθ κ.isSemipositive)
    (fun i => LocalPotentials.isThetaPshPotential_add_of_semipositive (huσ i) κC.isSemipositive)
    (LocalPotentials.isThetaPshPotential_add_of_semipositive hvσ κC.isSemipositive)).mp hlargeC
  have hσC : Tendsto Wσ F (@nhds (ThetaPshL1 σ.val)
      (singularityPseudoMetricSpace κC σ hσ).toUniformSpace.toTopologicalSpace Vσ) := by
    apply (tendsto_native_iff_add_kahler κC σ hσ F Wσ Vσ).mpr
    exact hOther
  exact tendsto_native_change_auxiliary κC omega σ hσ F Wσ Vσ hσC

/-- Actual compact domination internally produces a common enlarged form;
actual defining distances transport every auxiliary native choice. -/
theorem tendsto_native_iff_common_backgrounds (omega : KahlerBackground n M)
    (θ σ : ClosedRealOneOneForm n M)
    (hθ : IsBigClass (RealBottChern.ofRepresentative θ))
    (hσ : IsBigClass (RealBottChern.ofRepresentative σ))
    {I : Type*} (F : Filter I) {u : I → M → EReal} {v : M → EReal}
    (huθ : ∀ i, IsThetaPshPotential θ.val (u i))
    (hvθ : IsThetaPshPotential θ.val v)
    (huσ : ∀ i, IsThetaPshPotential σ.val (u i))
    (hvσ : IsThetaPshPotential σ.val v) :
    Tendsto (fun i => (⟨u i, huθ i⟩ : ThetaPshL1 θ.val)) F
      (@nhds (ThetaPshL1 θ.val)
        (singularityPseudoMetricSpace omega θ hθ).toUniformSpace.toTopologicalSpace ⟨v, hvθ⟩) ↔
    Tendsto (fun i => (⟨u i, huσ i⟩ : ThetaPshL1 σ.val)) F
      (@nhds (ThetaPshL1 σ.val)
        (singularityPseudoMetricSpace omega σ hσ).toUniformSpace.toTopologicalSpace ⟨v, hvσ⟩) :=
  ⟨tendsto_native_of_common_backgrounds omega θ σ hθ hσ F huθ hvθ huσ hvσ,
    tendsto_native_of_common_backgrounds omega σ θ hσ hθ F huσ hvσ huθ hvθ⟩

/-- Genuine Kähler targets internally supply both big classes. This compares
all admissible target choices once the same potentials are genuine for both. -/
theorem tendsto_native_iff_kahler_targets (omega β γ : KahlerBackground n M)
    {I : Type*} (F : Filter I) {u : I → M → EReal} {v : M → EReal}
    (huβ : ∀ i, IsThetaPshPotential β.form.val (u i))
    (hvβ : IsThetaPshPotential β.form.val v)
    (huγ : ∀ i, IsThetaPshPotential γ.form.val (u i))
    (hvγ : IsThetaPshPotential γ.form.val v) :
    Tendsto (fun i => (⟨u i, huβ i⟩ : ThetaPshL1 β.form.val)) F
      (@nhds (ThetaPshL1 β.form.val)
        (singularityPseudoMetricSpace omega β.form
          (PluripolarCapacityDichotomy.isBigClass_kahler β)).toUniformSpace.toTopologicalSpace ⟨v, hvβ⟩) ↔
    Tendsto (fun i => (⟨u i, huγ i⟩ : ThetaPshL1 γ.form.val)) F
      (@nhds (ThetaPshL1 γ.form.val)
        (singularityPseudoMetricSpace omega γ.form
          (PluripolarCapacityDichotomy.isBigClass_kahler γ)).toUniformSpace.toTopologicalSpace ⟨v, hvγ⟩) :=
  tendsto_native_iff_common_backgrounds omega β.form γ.form
    (PluripolarCapacityDichotomy.isBigClass_kahler β)
    (PluripolarCapacityDichotomy.isBigClass_kahler γ) F huβ hvβ huγ hvγ

end
end SGPT.Foundations.Analysis.Pending.SingularNativeCommonBackground
