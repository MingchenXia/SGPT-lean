import SGPT.Projective.OkounkovOriginalCancellationProduct
import SGPT.Okounkov.AlgebraicValuationBodies
import SGPT.NAPotential.GAGAMult2Algebraic
import SGPT.Foundations.Analysis.Pending.MultiplierIdealProductComparison

/-! Actual original coefficient transitions and multiplier-ideal-preserving genuine sheaf products.
Blueprint: okounkov-original-ideal-products.tex. No whole current-invariance source credit yet. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Okounkov.OriginalIdealProducts
open Set Filter CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Okounkov.AlgebraicValuation SGPT.Okounkov.ValGen2
open SGPT.NAPotential.GAGAMult MultiplierIdealProductComparison

variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (n : ℕ) (E : ClosedProjectiveEmbedding f)
  [SmoothOfRelativeDimension n f] [IsSeparated f] [QuasiCompact f]

local instance idealProductTopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance idealProductCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f n
local instance idealProductManifold : IsComplexManifold n (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f n

private def ordinaryCoefficient {M : X.Modules} {U : X.Opens} (e : LocalBundleFrame M U) (s : Γ(M,⊤)) :
    SchemeComplexPoint f → ℂ :=
  schemeOpenRegularFunction f n E U (e.coefficients (𝟙 _) (M.val.map U.leTop.op s))

omit [IsSeparated f] [QuasiCompact f] in
private theorem ordinaryCoefficient_subopen {M : X.Modules} {U W : X.Opens}
    (e : LocalBundleFrame M U) (s : Γ(M,⊤)) (hWU : W ≤ U) (p : SchemeComplexPoint f)
    (hp : schemeComplexPointImage f p ∈ W) :
    schemeOpenRegularFunction f n E W (e.coefficients (homOfLE hWU) (M.val.map W.leTop.op s)) p =
      ordinaryCoefficient f n E e s p :=
  (congrArg (fun r : Γ(X,W) => schemeOpenRegularFunction f n E W r p)
    (coefficients_restrict_top e hWU s)).trans
    (schemeOpenRegularFunction_restrict f n E W U hWU _ hp)

omit [IsSeparated f] [QuasiCompact f] in
/-- EVERY original ordinary coefficient has its exact genuine original analytic unit transition. -/
theorem originalOrdinaryCoefficient_transition {M : X.Modules} {U V : X.Opens}
    (e : LocalBundleFrame M U) (g : LocalBundleFrame M V) (s : Γ(M,⊤))
    (p : SchemeComplexPoint f) (hpU : schemeComplexPointImage f p ∈ U) (hpV : schemeComplexPointImage f p ∈ V) :
    schemeOpenRegularFunction f n E V (g.coefficients (𝟙 _) (M.val.map V.leTop.op s)) p =
      schemeFrameTransition f n E e g p *
      schemeOpenRegularFunction f n E U (e.coefficients (𝟙 _) (M.val.map U.leTop.op s)) p := by
  let W : X.Opens := U ⊓ V
  let l : W ⟶ U := homOfLE inf_le_left
  let r : W ⟶ V := homOfLE inf_le_right
  have hp : schemeComplexPointImage f p ∈ W := ⟨hpU,hpV⟩
  have hcoef := localBundleFrameTransition_coefficients e g l r (M.val.map W.leTop.op s)
  have he := congrArg (fun q : Γ(X,W) => schemeOpenRegularFunction f n E W q p) hcoef
  rw [schemeOpenRegularFunction_mul f n E W _ _ hp] at he
  calc
    _ = schemeOpenRegularFunction f n E W (g.coefficients r (M.val.map W.leTop.op s)) p :=
      (ordinaryCoefficient_subopen f n E g s inf_le_right p hp).symm
    _ = _ := he.trans (congrArg (schemeFrameTransition f n E e g p * ·)
      (ordinaryCoefficient_subopen f n E e s inf_le_left p hp))

/-- Original line-power ideal membership manufactures EVERY-frame ordinary membership of the SAME actual power section. -/
theorem isPlainMultiplierIdealSection_of_isIdealSection {L : X.Modules} (a : LineBundleAtlas L)
    (φ : SchemeComplexPoint f → EReal) (m : ℕ) (s : bundlePowerGlobalSections L m)
    (hs : IsIdealSection f n E (multiplierIdeal (n:=n) (m:ℝ) φ) m s) :
    IsPlainIdealSection f n E (multiplierIdeal (n:=n) (m:ℝ) φ) s := by
  intro V g p hpV
  obtain ⟨i,hi⟩ := a.covers (schemeComplexPointImage f p)
  let e := (a.frame i).tensorPower m
  have htr := schemeFrameTransition_holomorphicAt f n E e g p hi hpV
  have hmem := mem_multiplierIdeal_holomorphic_mul htr (hs (a.opens i) (a.frame i) p hi)
  apply mem_multiplierIdeal_congr hmem
  have hO : IsOpen (schemeComplexPointImage f ⁻¹' (a.opens i ⊓ V)) :=
    (a.opens i ⊓ V).isOpen.preimage (schemeComplexPointImage_continuous f)
  filter_upwards [hO.mem_nhds ⟨hi,hpV⟩] with y hy
  exact (originalOrdinaryCoefficient_transition f n E e g s y hy.1 hy.2).symm

section Product
variable {P Q R : X.Modules} {I : Type} (U : I → X.Opens) (hcover : ∀ x : X, ∃ i, x ∈ U i)
  (p : ∀ i, LocalBundleFrame P (U i)) (q : ∀ i, LocalBundleFrame Q (U i))
  (r : ∀ i, LocalBundleFrame R (U i))
  (htrans : ∀ i j (W : X.Opens) (h : W ⟶ U i) (l : W ⟶ U j),
    localBundleFrameTransition ((p i).tensor (q i)) ((p j).tensor (q j)) h l =
      localBundleFrameTransition (r i) (r j) h l)

/-- A genuine original frame-descended product preserves actual multiplier sections in EVERY target frame. -/
theorem coverProduct_isPlainMultiplierIdealSection (φ : SchemeComplexPoint f → EReal) (c : ℝ)
    (s : Γ(P,⊤)) (hs : IsPlainIdealSection f n E (multiplierIdeal (n:=n) c φ) s) (t : Γ(Q,⊤)) :
    IsPlainIdealSection f n E (multiplierIdeal (n:=n) c φ) (coverProduct U hcover p q r htrans s t) := by
  intro V e x hxV
  obtain ⟨i,hi⟩ := hcover (schemeComplexPointImage f x)
  have ht := schemeOpenRegularFunction_holomorphicAt f n E (U i)
    ((q i).coefficients (𝟙 _) (Q.val.map (U i).leTop.op t)) x hi
  have htr := schemeFrameTransition_holomorphicAt f n E (r i) e x hi hxV
  have hmem := mem_multiplierIdeal_holomorphic_mul htr
    (mem_multiplierIdeal_holomorphic_mul ht (hs (U i) (p i) x hi))
  apply mem_multiplierIdeal_congr hmem
  have hO : IsOpen (schemeComplexPointImage f ⁻¹' (U i ⊓ V)) :=
    (U i ⊓ V).isOpen.preimage (schemeComplexPointImage_continuous f)
  filter_upwards [hO.mem_nhds ⟨hi,hxV⟩] with y hy
  have hcoef := coverProduct_coefficients U hcover p q r htrans i s t
  have he := congrArg (fun z : Γ(X,U i) => schemeOpenRegularFunction f n E (U i) z y) hcoef
  rw [schemeOpenRegularFunction_mul f n E (U i) _ _ hy.1] at he
  change ordinaryCoefficient f n E (r i) (coverProduct U hcover p q r htrans s t) y =
    ordinaryCoefficient f n E (p i) s y * ordinaryCoefficient f n E (q i) t y at he
  have hh := originalOrdinaryCoefficient_transition f n E (r i) e
    (coverProduct U hcover p q r htrans s t) y hy.1 hy.2
  change schemeFrameTransition f n E (r i) e y *
    (ordinaryCoefficient f n E (q i) t y * ordinaryCoefficient f n E (p i) s y) =
    ordinaryCoefficient f n E e (coverProduct U hcover p q r htrans s t) y
  calc
    _ = schemeFrameTransition f n E (r i) e y *
        (ordinaryCoefficient f n E (p i) s y * ordinaryCoefficient f n E (q i) t y) := by ring
    _ = schemeFrameTransition f n E (r i) e y *
        ordinaryCoefficient f n E (r i) (coverProduct U hcover p q r htrans s t) y :=
      congrArg (schemeFrameTransition f n E (r i) e y * ·) he.symm
    _ = _ := hh.symm

end Product

/-- SAME actual original dual cancellation genuinely preserves the SAME multiplier-ideal exponent/weight. -/
theorem originalCancellationProduct_isPlainMultiplierIdealSection {L L' A : X.Modules}
    (a : LineBundleAtlas L) (b : LineBundleAtlas L') (d : LineBundleAtlas A)
    (φ : SchemeComplexPoint f → EReal) (m k : ℕ) (s : bundlePowerGlobalSections L m)
    (hs : IsIdealSection f n E (multiplierIdeal (n:=n) (m:ℝ) φ) m s)
    (t : Γ(bundleTensor (bundleTensorPower (bundleTensor L' (bundleDual L)) m) (bundleTensorPower A k),⊤)) :
    IsPlainIdealSection f n E (multiplierIdeal (n:=n) (m:ℝ) φ)
      (OriginalCancellation.originalCancellationProduct a b d m k s t) := by
  unfold OriginalCancellation.originalCancellationProduct
  apply coverProduct_isPlainMultiplierIdealSection f n E
  exact isPlainMultiplierIdealSection_of_isIdealSection f n E a φ m s hs

end SGPT.Okounkov.OriginalIdealProducts
