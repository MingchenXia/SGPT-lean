import SGPT.BDivisor.BD7EffectiveCone
import SGPT.BDivisor.DFAlgComparison
import SGPT.BDivisor.BD3SnapperNef

/-! Top-degree scalar comparison on a common algebraic decreasing approximation. -/

set_option autoImplicit false

noncomputable section

namespace SGPT.BDivisor.BD7

open Filter Set
open scoped Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.Pending
open CurrentBottChernClass CanonicalCurrentFrame
open SGPT.BDivisor.DangFavre SGPT.BDivisor.DFAlg
open SGPT.Hodge.BDivChain.NativeDraft SGPT.Hodge.BDivChain.NativeDraft.VolumeNetDraft
open SGPT.Hodge.BDivChain.SourceNefIntersectionDraft

attribute [local instance] blowup_model_connectedSpace

variable {m : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel (m + 1)) X]
  [IsComplexManifold (m + 1) X] [CompactSpace X] [ConnectedSpace X]
  [MeasurableSpace X] [BorelSpace X]

local notation "Sys" => ModelSystem.blowup (m + 1) X

/-- The modelwise Chern comparison, applied to the same decreasing approximants as in the
algebraic definition, identifies the two numerical limits. Here `chern` is the forward map
of the cofinal comparison. The mixed product need only be compared at the Cartier terms. -/
theorem algebraicScalar_eq_nefIntersection_of_antitone
    {A J : Type*} [Preorder J] [IsDirected J (· ≤ ·)] [Nonempty J]
    (κ : KahlerBackground (m + 1) X)
    (chern : A → WeilFamilyAny Sys)
    (C : Fin (m + 1) → J → A) (D : Fin (m + 1) → A)
    (hCartier : ∀ i j, IsAlgNefCartierAny (chern (C i j)))
    (bk : ∀ π : (ModelSystem.blowup (m + 1) X).Model, KahlerBackground (m + 1) π.1.carrier)
    (hEff : ∀ i j k, j ≤ k → ∀ π : (ModelSystem.blowup (m + 1) X).Model,
      (chern (C i j)).val π - (chern (C i k)).val π ∈
        @closure _ (euclideanTopology (RealBottChern (m + 1) π.1.carrier))
          (finiteEffectiveCone fun P : SGPT.PSH.GeometricPrimeCarrier (m + 1) π.1.carrier =>
            DFAlg.cycleClass (SGPT.Siu.primeEffectiveDivisor P)))
    (hConverges : ∀ i, ConvergesAny atTop (fun j => chern (C i j)) (chern (D i)))
    (mixed : (Fin (m + 1) → A) → ℝ)
    (r : ∀ j, CommonNefRealization (fun i => chern (C i j)))
    (hMixed : ∀ j, mixed (fun i => C i j) = (r j).intersection)
    (s : ℝ) (hScalar : Tendsto (fun j => mixed (fun i => C i j)) atTop (𝓝 s)) :
    s = (nefIntersection (fun i => chern (D i))).toReal := by
  have hDecreasing : ∀ i j k, j ≤ k → LEAny (chern (C i k)) (chern (C i j)) :=
    fun i j k hjk => leAny_of_modelwise_effectiveClosure _ _ bk (hEff i j k hjk)
  have hAnalytic :=
    (DFAlg.tendsto_intersection_of_antitone_alg κ (fun i j => chern (C i j))
      (fun i => chern (D i)) hCartier hDecreasing hConverges r).2
  have hClassical : Tendsto (fun j => (r j).intersection) atTop (𝓝 s) :=
    hScalar.congr' (Eventually.of_forall hMixed)
  exact tendsto_nhds_unique hClassical hAnalytic

end SGPT.BDivisor.BD7
