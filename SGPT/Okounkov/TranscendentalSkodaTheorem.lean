import SGPT.Okounkov.TranscendentalSkodaMain
import SGPT.Okounkov.TranscendentalSkodaTwisted

/-!
# Skoda's theorem for analytic singularities

Blueprint node `tok:ext-skoda` (= `skoda:main` of `claude-tok-skoda`), unconditional:
for holomorphic `g₁, …, g_r` near `x ∈ ℂⁿ` (`n > 0`), `φ = log ∑ᵢ |gᵢ|²`, `J = (g₁, …, g_r)` and
integers `m ≥ n`, `k ≥ 0`, `𝓘((k + m)φ)_x = J^k · 𝓘(mφ)_x`.

`skodaStatement_of_twistedHormander` (`TranscendentalSkodaMain.lean`) reduces `SkodaStatement` to
the kernel-bundle `L²` estimate `TwistedHormanderStatement`, proved in
`TranscendentalSkodaTwisted.lean` (`twistedHormanderStatement`).
-/

set_option autoImplicit false

namespace SGPT.Okounkov.TranscendentalSkoda

/-- **Skoda's `L²` division for surjective tuples** (`skoda:surjective-division`). -/
theorem surjectiveSkodaStatement : SurjectiveSkodaStatement :=
  surjectiveSkodaStatement_of_twisted twistedHormanderStatement

/-- **One division step** (`skoda:division-step`): `𝓘((ℓ + 1)φ)_x ⊆ J · 𝓘(ℓφ)_x` for `ℓ ≥ n`. -/
theorem skodaDivisionStatement : SkodaDivisionStatement :=
  skodaDivisionStatement_of_surjective surjectiveSkodaStatement

/-- **Skoda's theorem for analytic singularities** (`tok:ext-skoda`; Demailly, *Analytic methods
in algebraic geometry*, Theorem 12.17, for every `m ≥ n`):
`𝓘((k + m)φ)_x = J^k · 𝓘(mφ)_x`. -/
theorem multiplierIdeal_add_eq_pow_mul : SkodaStatement :=
  skodaStatement_of_twistedHormander twistedHormanderStatement

end SGPT.Okounkov.TranscendentalSkoda
