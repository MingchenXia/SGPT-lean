import SGPT.Okounkov.TranscendentalSkodaSurjective
import SGPT.Okounkov.TranscendentalSkodaRegularization

/-!
# Skoda's theorem for analytic singularities: the reduction to the kernel-bundle estimate

Blueprint `claude-tok-skoda`, node `skoda:main` (= `tok:ext-skoda`).

`skodaStatement_of_twistedHormander` proves `SkodaStatement` (`𝓘((k + m)φ)_x = J^k 𝓘(mφ)_x`
for `m ≥ n`) from `TwistedHormanderStatement` (Hörmander's `L²` estimate for `∂̄` in the kernel
bundle of a surjective holomorphic tuple, `skoda:twisted-hormander`):

`TwistedHormanderStatement → SurjectiveSkodaStatement → SkodaDivisionStatement → SkodaStatement`

(`surjectiveSkodaStatement_of_twisted`, `skodaDivisionStatement_of_surjective`,
`skodaStatement_of_division`). The theorem here is the reduction (it takes
`TwistedHormanderStatement` as a hypothesis); the hypothesis is discharged in
`TranscendentalSkodaTwisted.lean` (`twistedHormanderStatement`), and the unconditional theorem is
`multiplierIdeal_add_eq_pow_mul` in `TranscendentalSkodaTheorem.lean`.
-/

set_option autoImplicit false

namespace SGPT.Okounkov.TranscendentalSkoda

/-- **Skoda's theorem, conditional on the kernel-bundle `L²` estimate.** -/
theorem skodaStatement_of_twistedHormander (hVH : TwistedHormanderStatement) :
    SkodaStatement :=
  skodaStatement_of_division
    (skodaDivisionStatement_of_surjective (surjectiveSkodaStatement_of_twisted hVH))

end SGPT.Okounkov.TranscendentalSkoda
