import SGPT.Foundations.Schemes.NativeTensorPowerAnyFrame
import SGPT.Projective.OkoNov16OrdinaryGAGAAllFrames
import SGPT.PSH.CanonicalGrowthManifold

/-! Blueprint first: oko-nov16-original-veronese-infty-transport.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Okounkov.OkoNov16
open Set Filter CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.NAPotential.GAGAMult SGPT.GAGA.H0L SGPT.PSH
open scoped Topology
variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (n : ℕ)
  (J : ClosedProjectiveEmbedding f) [SmoothOfRelativeDimension n f]
  [IsSeparated f] [QuasiCompact f]
local instance veroneseInftyTopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance veroneseInftyCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f n
local instance veroneseInftyManifold : IsComplexManifold n (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f n

private theorem veroneseInfty_changeFrame {P : X.Modules} {U V : X.Opens}
    (α : LocalBundleFrame P U) (β : LocalBundleFrame P V) (k : ℕ)
    (s : bundlePowerGlobalSections P k) {u : SchemeComplexPoint f → EReal}
    (p : SchemeComplexPoint f) (hpU : schemeComplexPointImage f p∈U)
    (hpV : schemeComplexPointImage f p∈V)
    (hmem : (inftyIdeal (n:=n) u).mem p (sectionFrameCoefficient f n J α k s)) :
    (inftyIdeal (n:=n) u).mem p (sectionFrameCoefficient f n J β k s) := by
  have hU : IsOpen (schemeComplexPointImage f ⁻¹' (U:Set X)) :=
    U.isOpen.preimage (schemeComplexPointImage_continuous f)
  have hV : IsOpen (schemeComplexPointImage f ⁻¹' (V:Set X)) :=
    V.isOpen.preimage (schemeComplexPointImage_continuous f)
  have heq : sectionFrameCoefficient f n J β k s =ᶠ[𝓝 p] fun y =>
      schemeFrameTransition f n J (α.tensorPower k) (β.tensorPower k) y *
        sectionFrameCoefficient f n J α k s y := by
    filter_upwards [hU.mem_nhds hpU,hV.mem_nhds hpV] with y hyU hyV
    exact ordinaryOriginal_coefficient_transition f n J s (α.tensorPower k) (β.tensorPower k) hyU hyV
  exact (inftyIdeal_mem_congr heq).mpr (inftyIdeal_mul_mem
    (schemeFrameTransition_holomorphicAt f n J (α.tensorPower k) (β.tensorPower k) p hpU hpV) hmem)

omit [IsSeparated f] [QuasiCompact f] in
private theorem veroneseInfty_matchedCoefficient {L : X.Modules}
    (a : LineBundleAtlas L) (r k : ℕ) (s : bundlePowerGlobalSections L (r*k))
    {U : X.Opens} (α : LocalBundleFrame L U) (p : SchemeComplexPoint f)
    (hp : schemeComplexPointImage f p∈U) :
    sectionFrameCoefficient f n J (α.tensorPower r) k
      ((nativeLineTensorPowerMulIso a r k).hom.val.app (Opposite.op ⊤) s) =ᶠ[𝓝 p]
    sectionFrameCoefficient f n J α (r*k) s := by
  let := J.isSeparated
  let := J.quasiCompact
  have hU : IsOpen (schemeComplexPointImage f ⁻¹' (U:Set X)) :=
    U.isOpen.preimage (schemeComplexPointImage_continuous f)
  filter_upwards [hU.mem_nhds hp] with y hy
  have hn := PresheafOfModules.naturality_apply (nativeLineTensorPowerMulIso a r k).hom.val U.leTop.op s
  have hcoef := nativeLineTensorPowerMulIso_anyFrame a r k α (𝟙 U)
    ((bundleTensorPower L (r*k)).val.map U.leTop.op s)
  rw [hn] at hcoef
  exact congrArg (fun t : Γ(X,U) => schemeOpenRegularFunction f n J U t y) hcoef

omit [IsSeparated f] [QuasiCompact f] in
theorem original_veronesePower_isInfty_iff {L : X.Modules}
    (a : LineBundleAtlas L) (r k : ℕ) (s : bundlePowerGlobalSections L (r*k))
    (u : SchemeComplexPoint f → EReal) :
    IsInftySection f n J (fun y => (r:EReal)*u y) k
      ((nativeLineTensorPowerMulIso a r k).hom.val.app (Opposite.op ⊤) s) ↔
    IsInftySection f n J u (r*k) s := by
  let := J.isSeparated
  let := J.quasiCompact
  have hmul : ((r*k:ℕ):EReal)=(r:EReal)*(k:EReal) := by
    rw [← EReal.coe_natCast,Nat.cast_mul,EReal.coe_mul]
    rfl
  have hweight : (fun y => (k:EReal)*((r:EReal)*u y)) =
      (fun y => ((r*k:ℕ):EReal)*u y) := by
    funext y
    rw [hmul]
    ac_rfl
  change IsIdealSection f n J (inftyIdeal (n:=n) (fun y => (k:EReal)*((r:EReal)*u y))) k _ ↔
    IsIdealSection f n J (inftyIdeal (n:=n) (fun y => ((r*k:ℕ):EReal)*u y)) (r*k) s
  rw [hweight]
  constructor
  · intro hs U α p hp
    have hm := hs U (α.tensorPower r) p hp
    exact (inftyIdeal_mem_congr (veroneseInfty_matchedCoefficient f n J a r k s α p hp)).mp hm
  · intro hs U γ p hp
    obtain ⟨i,hi⟩ := a.covers (schemeComplexPointImage f p)
    have hm := hs _ (a.frame i) p hi
    have hm' := (inftyIdeal_mem_congr (veroneseInfty_matchedCoefficient f n J a r k s (a.frame i) p hi)).mpr hm
    exact veroneseInfty_changeFrame f n J ((a.frame i).tensorPower r) γ k _ p hi hp hm'
end SGPT.Okounkov.OkoNov16
