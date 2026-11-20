import SGPT.NAPotential.BerkovichPiecewiseLinear
import SGPT.NAPotential.HullParameterUSCHelpers
import SGPT.Foundations.Analysis.FirstPass.ERealChordUSC

/-! Actual original curve parameter upper semicontinuity. All-polar endpoint
jumps are treated as upper semicontinuous, without an invalid continuity
assumption. This is the opening assertion of the revised whole remark. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.NAPotential.Berkovich.PiecewiseLinearData.SimplexRevision.WholeHull
open Set Filter
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.PSH.VariableComplexAtlas
variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)}

/-- Original interpolation holds on the closed original interval, with
literal zero times bottom at its endpoints. -/
theorem curve_on_closed_adjacent (D : PiecewiseLinearData θ)
    (i : Fin (D.N+1)) (hi : i.val<D.N) {s : ℝ}
    (hlo : D.τ (D.nextIdx i hi) ≤ s) (hhi : s ≤ D.τ i) :
    D.curve s=affineComb (D.param i hi s) (D.A i) (D.A (D.nextIdx i hi)) := by
  let j := D.nextIdx i hi
  have htime : D.τ j<D.τ i := D.strictAnti (D.lt_nextIdx i hi)
  have hd : 0<D.τ i-D.τ j := sub_pos.mpr htime
  by_cases hei : s=D.τ i
  · subst s
    rw [D.curve_tau]
    have hp : D.param i hi (D.τ i)=0 := by simp only [param,sub_self,zero_div]
    rw [hp]
    funext x
    simp only [affineComb,sub_zero,EReal.coe_one,one_mul,EReal.coe_zero,zero_mul,add_zero]
  by_cases hej : s=D.τ j
  · subst s
    rw [D.curve_tau]
    have hp : D.param i hi (D.τ j)=1 := div_self hd.ne'
    rw [hp]
    funext x
    simp only [affineComb,sub_self,EReal.coe_zero,zero_mul,EReal.coe_one,one_mul,zero_add]
    rfl
  have hslo : D.τ j<s := lt_of_le_of_ne hlo (Ne.symm hej)
  have hshi : s<D.τ i := lt_of_le_of_ne hhi hei
  let t := D.param i hi s
  have ht0 : 0<t := div_pos (sub_pos.mpr hshi) hd
  have ht1 : t<1 := (div_lt_one hd).mpr (by linarith)
  have hrep : (1-t)*D.τ i+t*D.τ j=s := by
    dsimp [t,param]
    change (1-(D.τ i-s)/(D.τ i-D.τ j))*D.τ i+
      ((D.τ i-s)/(D.τ i-D.τ j))*D.τ j=s
    field_simp [hd.ne']
    ring
  have he := D.curve_affine i hi ht0 ht1
  rw [hrep] at he
  exact he

/-- Exactly the finite original closed segment pieces plus the original
left tail. The option none is the tail, so N=0 remains nonempty. -/
def ParameterPieceIndex (D : PiecewiseLinearData θ) :=
  Option {i : Fin (D.N+1) // i.val<D.N}

instance parameterPieceIndex_finite (D : PiecewiseLinearData θ) : Finite (ParameterPieceIndex D) := by
  unfold ParameterPieceIndex
  infer_instance

/-- Closed original pieces extended by bottom outside their own domains. -/
def parameterPiece (D : PiecewiseLinearData θ) (x : M) : ParameterPieceIndex D → ℝ → EReal
  | none => fun s => if s ≤ D.τ (Fin.last D.N) then D.A (Fin.last D.N) x else ⊥
  | some p => fun s => if D.τ (D.nextIdx p.val p.property) ≤ s ∧ s ≤ D.τ p.val then
      affineComb (D.param p.val p.property s) (D.A p.val) (D.A (D.nextIdx p.val p.property)) x
    else ⊥

/-- Every literal closed piece is bounded above by the original curve. -/
theorem parameterPiece_le_curve (D : PiecewiseLinearData θ) (x : M)
    (q : ParameterPieceIndex D) (s : ℝ) : parameterPiece D x q s ≤ D.curve s x := by
  cases q with
  | none =>
    change (if s ≤ D.τ (Fin.last D.N) then D.A (Fin.last D.N) x else ⊥) ≤ _
    split_ifs with hs
    · rw [D.curve_of_le_last hs]
    · exact bot_le
  | some p =>
    change (if D.τ (D.nextIdx p.val p.property) ≤ s ∧ s ≤ D.τ p.val then
      affineComb (D.param p.val p.property s) (D.A p.val) (D.A (D.nextIdx p.val p.property)) x
      else ⊥) ≤ _
    split_ifs with hs
    · rw [curve_on_closed_adjacent D p.val p.property hs.1 hs.2]
    · exact bot_le

/-- A genuine finite closed-piece decomposition of the unchanged original
curve, at every parameter and every nodal pole. -/
theorem curve_eq_iSup_parameterPiece (D : PiecewiseLinearData θ) (x : M) :
    (fun s => D.curve s x)=fun s => ⨆ q : ParameterPieceIndex D,parameterPiece D x q s := by
  funext s
  apply le_antisymm
  · by_cases h : D.τ 0<s
    · rw [D.curve_of_lt h]
      exact bot_le
    let i := D.segIndex s (not_lt.mp h)
    have his : s ≤ D.τ i := D.le_tau_segIndex s _
    by_cases hi : i.val<D.N
    · have hjs : D.τ (D.nextIdx i hi)<s :=
        D.tau_lt_of_segIndex_lt s _ (D.lt_nextIdx i hi)
      apply le_iSup_of_le (some ⟨i,hi⟩)
      change D.curve s x ≤ if D.τ (D.nextIdx i hi) ≤ s ∧ s ≤ D.τ i then _ else ⊥
      rw [if_pos ⟨hjs.le,his⟩,curve_on_closed_adjacent D i hi hjs.le his]
    · have hlast : i=Fin.last D.N := by
        ext
        simp only [Fin.val_last]
        omega
      have htail : s ≤ D.τ (Fin.last D.N) := hlast ▸ his
      apply le_iSup_of_le none
      change D.curve s x ≤ if s ≤ D.τ (Fin.last D.N) then _ else ⊥
      rw [if_pos htail,D.curve_of_le_last htail]
  · exact iSup_le (fun q => parameterPiece_le_curve D x q s)

/-- Genuine relative parameter USC of each closed source chord, with
both source endpoints allowed to be bottom. -/
theorem upperSemicontinuousOn_closed_adjacent_chord (D : PiecewiseLinearData θ)
    (i : Fin (D.N+1)) (hi : i.val<D.N) (x : M) :
    UpperSemicontinuousOn (fun s =>
      affineComb (D.param i hi s) (D.A i) (D.A (D.nextIdx i hi)) x)
      (Icc (D.τ (D.nextIdx i hi)) (D.τ i)) := by
  let j := D.nextIdx i hi
  let K := Icc (D.τ j) (D.τ i)
  have hd : 0<D.τ i-D.τ j := sub_pos.mpr (D.strictAnti (D.lt_nextIdx i hi))
  have hp : Continuous (D.param i hi) := by
    unfold param
    fun_prop
  have ht0 : ∀ s∈K,0 ≤ D.param i hi s := fun s hs =>
    div_nonneg (sub_nonneg.mpr hs.2) hd.le
  have ht1 : ∀ s∈K,D.param i hi s ≤ 1 := fun s hs =>
    (div_le_one hd).mpr (by linarith [hs.1])
  have hleft := SGPT.NAPotential.Berkovich.HullParameterUSC.upperSemicontinuousOn_coe_mul_fixed
    (continuous_const.sub hp).continuousOn (fun s hs => sub_nonneg.mpr (ht1 s hs))
    ((D.isThetaPSH i).1 x)
  have hright := SGPT.NAPotential.Berkovich.HullParameterUSC.upperSemicontinuousOn_coe_mul_fixed
    hp.continuousOn ht0 ((D.isThetaPSH j).1 x)
  exact upperSemicontinuousOn_eReal_add hleft hright
    (fun s hs => SGPT.NAPotential.Berkovich.HullParameterUSC.coe_mul_fixed_ne_top
      (sub_nonneg.mpr (ht1 s hs)) ((D.isThetaPSH i).1 x))
    (fun s hs => SGPT.NAPotential.Berkovich.HullParameterUSC.coe_mul_fixed_ne_top
      (ht0 s hs) ((D.isThetaPSH j).1 x))

/-- The original closed source pieces, extended by bottom, are globally
upper semicontinuous. -/
theorem upperSemicontinuous_parameterPiece (D : PiecewiseLinearData θ) (x : M)
    (q : ParameterPieceIndex D) : UpperSemicontinuous (parameterPiece D x q) := by
  classical
  cases q with
  | none =>
    change UpperSemicontinuous
      (SGPT.NAPotential.Berkovich.HullParameterUSC.closedCut
        (Iic (D.τ (Fin.last D.N))) (fun _ => D.A (Fin.last D.N) x))
    exact SGPT.NAPotential.Berkovich.HullParameterUSC.upperSemicontinuous_closedCut
      isClosed_Iic (upperSemicontinuous_const.upperSemicontinuousOn _)
  | some p =>
    have he : parameterPiece D x (some p)=
        SGPT.NAPotential.Berkovich.HullParameterUSC.closedCut
          (Icc (D.τ (D.nextIdx p.val p.property)) (D.τ p.val))
          (fun s => affineComb (D.param p.val p.property s)
            (D.A p.val) (D.A (D.nextIdx p.val p.property)) x) := by
      funext s
      by_cases hs : D.τ (D.nextIdx p.val p.property) ≤ s ∧ s ≤ D.τ p.val
      · simp only [parameterPiece,SGPT.NAPotential.Berkovich.HullParameterUSC.closedCut,
          mem_Icc,if_pos hs]
      · simp only [parameterPiece,SGPT.NAPotential.Berkovich.HullParameterUSC.closedCut,
          mem_Icc,if_neg hs]
    rw [he]
    exact SGPT.NAPotential.Berkovich.HullParameterUSC.upperSemicontinuous_closedCut
      isClosed_Icc (upperSemicontinuousOn_closed_adjacent_chord D p.val p.property x)

/-- The opening original assertion of the whole source remark: the
unchanged, generally nonconcave curve is parameter upper semicontinuous
at every spatial point, including every nodal pole and N=0. -/
theorem upperSemicontinuous_curve_parameter (D : PiecewiseLinearData θ) (x : M) :
    UpperSemicontinuous (fun s => D.curve s x) := by
  rw [curve_eq_iSup_parameterPiece]
  exact SGPT.NAPotential.Berkovich.HullParameterUSC.upperSemicontinuous_iSup_finite
    (upperSemicontinuous_parameterPiece D x)

end SGPT.NAPotential.Berkovich.PiecewiseLinearData.SimplexRevision.WholeHull
