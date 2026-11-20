import SGPT.Unibranch.PrimeNov16AnalyticNormalizationNativeMonic
import SGPT.Unibranch.PrimeNov16AnalyticNormalizationGraphFinite

/-! Actual native graph stalk finiteness at EVERY point, including H=0.
Blueprint: prime-nov16-analytic-normalization-graph-stalk-finite.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter TopologicalSpace Polynomial
open scoped Topology
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open HolGerm GermAlgebraicParametrization GermParametrizationData RegularLocusDense
namespace SGPT.Unibranch.PrimeNov16AnalyticNormalizationGraphStalkFinite
open PrimeNov16AnalyticNormalizationDenominatorGraph
open PrimeNov16AnalyticNormalizationGraphFinite
open PrimeNov16AnalyticNormalizationStalkCalculus

theorem baseProjection_coordinateProjection (n k : ℕ) :
    baseProjection n k = coordinateProjection (n+k) n := by
  ext z i
  have hi : i.val < n+k := by omega
  simp [baseProjection,EuclideanSpace.finAddEquivProd,EuclideanSpace.sumEquivProd,
    LinearIsometryEquiv.piLpCongrLeft_apply,coordinateProjection_apply,hi]
  rfl

theorem fibreProjection_coordinate {n k : ℕ} (z : ComplexModel (n+k)) (i : Fin k) :
    fibreProjection n k z i = z (Fin.natAdd n i) := by
  simp [fibreProjection,EuclideanSpace.finAddEquivProd,EuclideanSpace.sumEquivProd,
    LinearIsometryEquiv.piLpCongrLeft_apply]

def nativeCarrier {n k : ℕ} (U : Opens (ComplexModel n)) (C : Set U)
    (H : ComplexModel n → ℂ) (G : Fin k → ComplexModel n → ℂ) : Set (ComplexModel (n+k)) :=
  Subtype.val '' graphClosure U C H G

def nativePoint {n k : ℕ} (U : Opens (ComplexModel n)) (C : Set U)
    (H : ComplexModel n → ℂ) (G : Fin k → ComplexModel n → ℂ)
    (p : graphClosure U C H G) : nativeCarrier U C H G :=
  ⟨p.val.val,⟨p.val,p.property,rfl⟩⟩

theorem graph_native_stalkStructureMap_finite {n k : ℕ}
    (U : Opens (ComplexModel n)) (C : Set U)
    (H : ComplexModel n → ℂ) (G : Fin k → ComplexModel n → ℂ)
    (d : Fin k → ℕ) (a : Fin k → ℕ → ComplexModel n → ℂ)
    (ha : ∀ i j,j < d i → DifferentiableOn ℂ (a i j) U)
    (hmonic : ∀ x : C,H x.val.val ≠ 0 → ∀ i,
      monicEval (d i) (a i) x.val.val (G i x.val.val/H x.val.val) = 0)
    (p : graphClosure U C H G) :
    (stalkStructureMap (nativeCarrier U C H G) (nativePoint U C H G p) n).Finite := by
  apply stalkStructureMap_finite (Nat.le_add_right n k)
  intro r hr hnr
  let i : Fin k := ⟨r-n,by omega⟩
  have hi : Fin.natAdd n i = (⟨r,hr⟩ : Fin (n+k)) := by
    apply Fin.ext
    simp only [Fin.val_natAdd]
    dsimp [i]
    omega
  let b : ℕ → ComplexModel n → ℂ := fun j x =>
    if j < d i then a i j (x+baseProjection n k p.val.val) else 0
  have hb : ∀ j,∀ᶠ x in 𝓝 (0 : ComplexModel n),DifferentiableAt ℂ (b j) x := by
    intro j
    by_cases hj : j < d i
    · have ht : Tendsto (fun x : ComplexModel n => x+baseProjection n k p.val.val)
          (𝓝 0) (𝓝 (baseProjection n k p.val.val)) := by
        simpa only [zero_add] using
          (show Continuous (fun x : ComplexModel n => x+baseProjection n k p.val.val)
            from continuous_id.add continuous_const).tendsto (0 : ComplexModel n)
      filter_upwards [ht.eventually (U.isOpen.mem_nhds p.val.property)] with x hx
      change DifferentiableAt ℂ (fun x => if j < d i then
        a i j (x+baseProjection n k p.val.val) else 0) x
      simp only [if_pos hj]
      exact ((ha i j hj).differentiableAt (U.isOpen.mem_nhds hx)).comp x
        (differentiableAt_id.add_const _)
    · change ∀ᶠ x in 𝓝 (0 : ComplexModel n),DifferentiableAt ℂ
        (fun x => if j < d i then a i j (x+baseProjection n k p.val.val) else 0) x
      simp only [if_neg hj]
      exact Eventually.of_forall fun _ => differentiableAt_const (0 : ℂ)
  apply PrimeNov16AnalyticNormalizationNativeMonic.exists_monic_germ_of_native_equation
    (nativeCarrier U C H G) p.val.val hr (d i) b hb
  apply Eventually.of_forall
  intro v hv
  obtain ⟨z,hz,hzv⟩ := hv
  have hroot := monic_on_graphClosure U H G d a ha hmonic hz i
  have hbase : baseProjection n k z.val =
      coordinateProjection (n+k) n v + baseProjection n k p.val.val := by
    rw [hzv,map_add,baseProjection_coordinateProjection]
  have hfibre : fibreProjection n k z.val i = v ⟨r,hr⟩+p.val.val ⟨r,hr⟩ := by
    rw [fibreProjection_coordinate,hzv]
    change (v+p.val.val) (Fin.natAdd n i) = _
    rw [hi]
    rfl
  rw [hbase,hfibre] at hroot
  change monicEval (d i) b (coordinateProjection (n+k) n v)
    (v ⟨r,hr⟩+p.val.val ⟨r,hr⟩) = 0
  rw [monicEval]
  convert hroot using 1
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  simp only [b,if_pos (Finset.mem_range.mp hj)]

end SGPT.Unibranch.PrimeNov16AnalyticNormalizationGraphStalkFinite
