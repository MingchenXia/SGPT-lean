import SGPT.Foundations.Analysis.Pending.SingularModelEnergyExtendedDiamond
import SGPT.Foundations.Analysis.Pending.SingularModelDarvasBasic

set_option autoImplicit false

/-!
# Actual Darvas rooftop contraction and triangle inequality for singular models

Xia SGPT PDF0160--0161, Proposition 4.3.1 and Lemma 4.3.1, Step 2.
Actual genuine finite-energy rooftop closure and the actual singular energy
diamond produce the rooftop contraction, hence the triangle inequality.
No boundedness of the model or target contraction/triangle premise is used.
-/

open Set Filter MeasureTheory
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.SingularModelDarvasContraction

open FirstPass FirstPass.PositiveClasses RelativeEnergy RelativeDarvasDistance
  RelativePreceqClasses

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M]
  {θ : ClosedRealOneOneForm n M} {φ u v w : M → EReal} {hφ : IsModelPotential θ φ}

/-- The actual rooftop contraction for ordered genuine finite-energy endpoints
and an arbitrary singular model reference. -/
theorem relativeD1_rooftop_le_of_le (omega : KahlerBackground n M)
    (hu : RelativeFiniteEnergyPreceq θ φ u hφ) (hv : RelativeFiniteEnergyPreceq θ φ v hφ)
    (hw : RelativeFiniteEnergyPreceq θ φ w hφ) (hvu : v ≤ u) :
    relativeD1 θ φ hφ (rooftop θ u w) (rooftop θ v w) ≤ relativeD1 θ φ hφ u v := by
  have huw := relativeFiniteEnergyPreceq_rooftop omega hu hw
  have hvw := relativeFiniteEnergyPreceq_rooftop omega hv hw
  have hpu := hu.1.plurisubharmonic
  have hpv := hv.1.plurisubharmonic
  have hpw := hw.1.plurisubharmonic
  have hle : rooftop θ v w ≤ rooftop θ u w := rooftop_mono hvu le_rfl
  rw [relativeD1_comm, relativeD1_eq_sub_of_le hvw.1.plurisubharmonic hle,
    relativeD1_comm, relativeD1_eq_sub_of_le hpv hvu]
  set a := rooftop θ u w with ha
  have hav : rooftop θ a v = rooftop θ v w :=
    rooftop_rooftop_of_le hpu hpv hpw huw.1.plurisubharmonic
      (relativeFiniteEnergyPreceq_rooftop omega huw hv).1.plurisubharmonic
      hvw.1.plurisubharmonic hvu
  have hd := SingularModelEnergyExtendedDiamond.toReal_energy_add_le_max_add_rooftop
    omega θ hφ huw hv
  rw [hav] at hd
  have hma : (fun x => max (a x) (v x)) ≤ u := fun x =>
    max_le (rooftop_le_left hpu hpw x) (hvu x)
  have hmbot : ⊥ < energy θ φ hφ (fun x => max (a x) (v x)) :=
    (SingularModelFiniteEnergyPreceq.bot_lt_energy omega huw).trans_le
      (energy_mono_of_le fun x => le_max_left _ _)
  have hmu : (energy θ φ hφ (fun x => max (a x) (v x))).toReal ≤
      (energy θ φ hφ u).toReal :=
    EReal.toReal_le_toReal (energy_mono_of_le hma) hmbot.ne'
      (energy_ne_top_of_preceq hu.1.relativePSHPreceq)
  linarith

/-- The actual Darvas functional contracts under a common genuine rooftop
on the finite-energy singularity-order class of every model potential. -/
theorem relativeD1_rooftop_le (omega : KahlerBackground n M)
    (hu : RelativeFiniteEnergyPreceq θ φ u hφ) (hv : RelativeFiniteEnergyPreceq θ φ v hφ)
    (hw : RelativeFiniteEnergyPreceq θ φ w hφ) :
    relativeD1 θ φ hφ (rooftop θ u w) (rooftop θ v w) ≤ relativeD1 θ φ hφ u v := by
  have huv := relativeFiniteEnergyPreceq_rooftop omega hu hv
  have huw := relativeFiniteEnergyPreceq_rooftop omega hu hw
  have hvw := relativeFiniteEnergyPreceq_rooftop omega hv hw
  have huvw := relativeFiniteEnergyPreceq_rooftop omega huv hw
  have h1 := relativeFiniteEnergyPreceq_rooftop omega huw hvw
  have hpu := hu.1.plurisubharmonic
  have hpv := hv.1.plurisubharmonic
  have hpw := hw.1.plurisubharmonic
  have e : rooftop θ (rooftop θ u w) (rooftop θ v w) = rooftop θ (rooftop θ u v) w :=
    rooftop_rooftop_rooftop hpu hpv hpw huw.1.plurisubharmonic hvw.1.plurisubharmonic
      huv.1.plurisubharmonic h1.1.plurisubharmonic huvw.1.plurisubharmonic
  rw [relativeD1_eq_add_rooftop huw.1.plurisubharmonic hvw.1.plurisubharmonic h1.1.plurisubharmonic,
    e, relativeD1_eq_add_rooftop hpu hpv huv.1.plurisubharmonic]
  exact add_le_add
    (relativeD1_rooftop_le_of_le omega hu huv hw (rooftop_le_left hpu hpv))
    (relativeD1_rooftop_le_of_le omega hv huv hw (rooftop_le_right hpu hpv))

/-- The actual Darvas triangle inequality for genuine finite-energy
potentials over every singular model reference. -/
theorem relativeD1_triangle (omega : KahlerBackground n M)
    (hu : RelativeFiniteEnergyPreceq θ φ u hφ) (hv : RelativeFiniteEnergyPreceq θ φ v hφ)
    (hw : RelativeFiniteEnergyPreceq θ φ w hφ) :
    relativeD1 θ φ hφ u v ≤ relativeD1 θ φ hφ u w + relativeD1 θ φ hφ w v := by
  have hpu := hu.1.plurisubharmonic
  have hpv := hv.1.plurisubharmonic
  have hpw := hw.1.plurisubharmonic
  have huv := relativeFiniteEnergyPreceq_rooftop omega hu hv
  have huw := relativeFiniteEnergyPreceq_rooftop omega hu hw
  have hvw := relativeFiniteEnergyPreceq_rooftop omega hv hw
  have hwu := relativeFiniteEnergyPreceq_rooftop omega hw hu
  have hvwu := relativeFiniteEnergyPreceq_rooftop omega hvw hu
  have hc := relativeD1_rooftop_le omega hw hvw hu
  have hle1 : rooftop θ v w ≤ w := rooftop_le_right hpv hpw
  have hle2 : rooftop θ (rooftop θ v w) u ≤ rooftop θ w u := rooftop_mono hle1 le_rfl
  rw [relativeD1_comm θ φ hφ (rooftop θ w u),
    relativeD1_eq_sub_of_le hvwu.1.plurisubharmonic hle2, relativeD1_comm θ φ hφ w,
    relativeD1_eq_sub_of_le hvw.1.plurisubharmonic hle1] at hc
  have hle3 : rooftop θ (rooftop θ v w) u ≤ rooftop θ u v :=
    (le_rooftop_iff hpu hpv hvwu.1.plurisubharmonic).2
      ⟨rooftop_le_right hvw.1.plurisubharmonic hpu,
        (rooftop_le_left hvw.1.plurisubharmonic hpu).trans (rooftop_le_left hpv hpw)⟩
  have hm := SingularModelFiniteRealEnergy.toReal_energy_mono omega hvwu huv hle3
  rw [relativeD1, relativeD1, relativeD1, rooftop_comm θ w v, rooftop_comm θ w u] at *
  linarith

end

end SGPT.Foundations.Analysis.Pending.SingularModelDarvasContraction
