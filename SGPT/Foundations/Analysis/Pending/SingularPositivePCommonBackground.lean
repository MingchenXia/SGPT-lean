import SGPT.Foundations.Analysis.Pending.SingularPositivePBackgroundIndependence
import SGPT.Foundations.Analysis.FirstPass.KahlerCurrentPerturbation

set_option autoImplicit false

/-! # Actual P-order comparison between two positive-mass backgrounds -/

namespace SGPT.Foundations.Analysis.Pending.SingularPositivePCommonBackground

open FirstPass FirstPass.PositiveClasses FirstPass.POrder DiagonalMass
  SingularPositivePBackgroundTransport SingularPositivePBackgroundIndependence

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M]

private theorem pOrderWith_of_positive_backgrounds (omega : KahlerBackground n M)
    (θ σ : ClosedRealOneOneForm n M) {u v : M → EReal}
    (huθ : IsThetaPshPotential θ.val u) (hvθ : IsThetaPshPotential θ.val v)
    (huσ : IsThetaPshPotential σ.val u) (hvσ : IsThetaPshPotential σ.val v)
    (huposθ : HasPositivePotentialMass θ u huθ)
    (hvposθ : HasPositivePotentialMass θ v hvθ)
    (huposσ : HasPositivePotentialMass σ u huσ)
    (hvposσ : HasPositivePotentialMass σ v hvσ)
    (huv : POrderWith θ u v) : POrderWith σ u v := by
  obtain ⟨C, hC, hsemi⟩ :=
    KahlerDomination.exists_pos_isSemipositive_add_smul omega (σ - θ)
  let η := σ - θ + C • omega.form
  have hη : η.val.IsSemipositive := hsemi
  have hlarge := pOrderWith_add_semipositive omega θ η hη huθ hvθ
    huposθ hvposθ huv
  have hforms : θ + η = σ + C • omega.form := by
    dsimp only [η]
    abel
  have hlarge' : POrderWith (σ + (KahlerBackground.smul hC omega).form) u v := by
    simpa only [hforms, KahlerBackground.smul_form] using hlarge
  exact (pOrderWith_add_kahler_iff (KahlerBackground.smul hC omega) σ
    huσ hvσ huposσ hvposσ).mp hlarge'

/-- Actual compact Kähler domination and the genuine scaled-background factory internally connect any two positive admissible backgrounds. -/
theorem pOrderWith_iff_of_positive_backgrounds (omega : KahlerBackground n M)
    (θ σ : ClosedRealOneOneForm n M) {u v : M → EReal}
    (huθ : IsThetaPshPotential θ.val u) (hvθ : IsThetaPshPotential θ.val v)
    (huσ : IsThetaPshPotential σ.val u) (hvσ : IsThetaPshPotential σ.val v)
    (huposθ : HasPositivePotentialMass θ u huθ)
    (hvposθ : HasPositivePotentialMass θ v hvθ)
    (huposσ : HasPositivePotentialMass σ u huσ)
    (hvposσ : HasPositivePotentialMass σ v hvσ) :
    POrderWith θ u v ↔ POrderWith σ u v :=
  ⟨pOrderWith_of_positive_backgrounds omega θ σ huθ hvθ huσ hvσ
      huposθ hvposθ huposσ hvposσ,
    pOrderWith_of_positive_backgrounds omega σ θ huσ hvσ huθ hvθ
      huposσ hvposσ huposθ hvposθ⟩

end

end SGPT.Foundations.Analysis.Pending.SingularPositivePCommonBackground
