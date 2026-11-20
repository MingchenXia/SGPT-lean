import SGPT.NPP.DN9Assembly
import SGPT.NPP.DN5Psh
import SGPT.NPP.DN6Bridge

/-!
# The joint smoothing lemma, unconditionally

Lane DN9 (`thm:DNT23_C11bar`; FPT `lem:chern-joint-smoothing`, used in the proof of FPT
`thm:big-metric-laplacian-rooftop`).

`SGPT.NPP.DN9.jointSmoothingStatement : SGPT.NPP.DN2.JointSmoothingStatement`: every compact
complex manifold with a Kähler form carries a joint smoothing (`SGPT.NPP.DN2.IsJointSmoothing`).
It combines the reduction `SGPT.NPP.DN5.jointSmoothingStatement_of_local` with the
chart-level estimate `SGPT.NPP.DN9.localJointEstimate` (lanes DN4, DN9, DN10, DN11) and the
generator `SGPT.NPP.DN6.generatorEstimate`.
-/

set_option autoImplicit false

namespace SGPT.NPP.DN9

universe v

/-- **FPT `lem:chern-joint-smoothing`** in the form `SGPT.NPP.DN2.JointSmoothingStatement`. -/
theorem jointSmoothingStatement : SGPT.NPP.DN2.JointSmoothingStatement.{v} :=
  SGPT.NPP.DN5.jointSmoothingStatement_of_local (fun _ => localJointEstimate)
    SGPT.NPP.DN6.generatorEstimate

end SGPT.NPP.DN9
