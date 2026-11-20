import SGPT.Checks.LiteratureBridge.BJPrintedDefinition

/-! Actual nonempty directed simultaneous tails of two ORIGINAL input nets.
All three coordinate cofinalities are constructed internally. -/
set_option autoImplicit false
universe u v
namespace SGPT.NAPotential.BJ.MaxClosure
open Filter
open scoped Topology
variable {I : Type u} {J : Type v} [Preorder I] [Preorder J]
  (iN : ℕ → I) (jN : ℕ → J)

abbrev SimultaneousTails := {t : (I×J)×ℕ // iN t.2 ≤ t.1.1 ∧ jN t.2 ≤ t.1.2}

instance simultaneousTails_nonempty : Nonempty (SimultaneousTails iN jN) :=
  ⟨⟨((iN 0,jN 0),0),le_rfl,le_rfl⟩⟩

instance simultaneousTails_directed [IsDirectedOrder I] [IsDirectedOrder J] :
    IsDirectedOrder (SimultaneousTails iN jN) := by
  constructor
  intro x y
  let N := max x.val.2 y.val.2
  obtain ⟨i1,hxi1,hyi1⟩ := exists_ge_ge x.val.1.1 y.val.1.1
  obtain ⟨i2,hi12,hNi2⟩ := exists_ge_ge i1 (iN N)
  obtain ⟨j1,hxj1,hyj1⟩ := exists_ge_ge x.val.1.2 y.val.1.2
  obtain ⟨j2,hj12,hNj2⟩ := exists_ge_ge j1 (jN N)
  refine ⟨⟨((i2,j2),N),hNi2,hNj2⟩,?_,?_⟩
  · exact Prod.le_def.mpr ⟨Prod.le_def.mpr ⟨hxi1.trans hi12,hxj1.trans hj12⟩,le_max_left _ _⟩
  · exact Prod.le_def.mpr ⟨Prod.le_def.mpr ⟨hyi1.trans hi12,hyj1.trans hj12⟩,le_max_right _ _⟩

def first (t : SimultaneousTails iN jN) : I := t.val.1.1
def second (t : SimultaneousTails iN jN) : J := t.val.1.2
def level (t : SimultaneousTails iN jN) : ℕ := t.val.2

theorem first_monotone : Monotone (first iN jN) := by
  intro x y h
  exact (Prod.le_def.mp (Prod.le_def.mp h).1).1

theorem second_monotone : Monotone (second iN jN) := by
  intro x y h
  exact (Prod.le_def.mp (Prod.le_def.mp h).1).2

theorem level_monotone : Monotone (level iN jN) := by
  intro x y h
  exact (Prod.le_def.mp h).2

theorem first_ge_threshold (t : SimultaneousTails iN jN) : iN (level iN jN t) ≤ first iN jN t :=
  t.property.1

theorem second_ge_threshold (t : SimultaneousTails iN jN) : jN (level iN jN t) ≤ second iN jN t :=
  t.property.2

/-- No common upper indices are supplied: original directedness produces them. -/
theorem first_tendsto [IsDirectedOrder I] [IsDirectedOrder J] : Tendsto (first iN jN) atTop atTop := by
  apply tendsto_atTop_atTop.mpr
  intro i0
  obtain ⟨i,hi0,hiN⟩ := exists_ge_ge i0 (iN 0)
  refine ⟨⟨((i,jN 0),0),hiN,le_rfl⟩,fun t ht => ?_⟩
  exact hi0.trans ((Prod.le_def.mp (Prod.le_def.mp ht).1).1)

theorem second_tendsto [IsDirectedOrder I] [IsDirectedOrder J] : Tendsto (second iN jN) atTop atTop := by
  apply tendsto_atTop_atTop.mpr
  intro j0
  obtain ⟨j,hj0,hjN⟩ := exists_ge_ge j0 (jN 0)
  refine ⟨⟨((iN 0,j),0),le_rfl,hjN⟩,fun t ht => ?_⟩
  exact hj0.trans ((Prod.le_def.mp (Prod.le_def.mp ht).1).2)

theorem level_tendsto [IsDirectedOrder I] [IsDirectedOrder J] : Tendsto (level iN jN) atTop atTop := by
  apply tendsto_atTop_atTop.mpr
  intro N
  refine ⟨⟨((iN N,jN N),N),le_rfl,le_rfl⟩,fun t ht => ?_⟩
  exact (Prod.le_def.mp ht).2

end SGPT.NAPotential.BJ.MaxClosure
