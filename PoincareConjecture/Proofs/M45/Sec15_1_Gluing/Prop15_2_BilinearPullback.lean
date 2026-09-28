import PoincareConjecture.Proofs.M45.Sec15_1_Gluing.Prop15_2_PullbackErrors








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8

open Filter
open scoped ContDiff Topology

namespace PoincareConjecture.M45.PointJetsVanish

variable {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

set_option maxHeartbeats 800000 in




theorem bilinear_pullback {l : Filter ι} {x : ι → E}
    {B : ι → E → E →L[ℝ] E →L[ℝ] ℝ} {a : ι → E → E}
    (hB : PointJetsVanish B (fun i => a i (x i)) l)
    (ha : ∀ m, FinitePointJetBounded m a x l)
    (hBs : ∀ i, ContDiffAt ℝ ∞ (B i) (a i (x i)))
    (has : ∀ i, ContDiffAt ℝ ∞ (a i) (x i)) :
    PointJetsVanish (fun i y => (B i (a i y)).bilinearComp
      (fderiv ℝ (a i) y) (fderiv ℝ (a i) y)) x l := by
  let T := E →L[ℝ] E →L[ℝ] ℝ
  let : NormedAddCommGroup T := inferInstance
  let : NormedSpace ℝ T := inferInstance
  let : NormedAddCommGroup (E →L[ℝ] E) := inferInstance
  let : NormedSpace ℝ (E →L[ℝ] E) := inferInstance
  let flip : T →L[ℝ] T :=
    (ContinuousLinearMap.flipₗᵢ ℝ E E ℝ).toContinuousLinearEquiv.toContinuousLinearMap
  let op : T →L[ℝ] (E →L[ℝ] E) →L[ℝ] T :=
    (ContinuousLinearMap.compL ℝ (E →L[ℝ] E) T T flip).comp
      (ContinuousLinearMap.compL ℝ E E (E →L[ℝ] ℝ))
  have hop (b : T) (A : E →L[ℝ] E) : op b A = (b.comp A).flip := rfl
  have hC := hB.comp ha has hBs
  have hd (m : ℕ) : FinitePointJetBounded m (fun i => fderiv ℝ (a i)) x l :=
    (ha (m + 1)).fderiv
  have hCs (i : ι) : ContDiffAt ℝ ∞ (B i ∘ a i) (x i) := (hBs i).comp (x i) (has i)
  have hds (i : ι) : ContDiffAt ℝ ∞ (fderiv ℝ (a i)) (x i) :=
    (has i).fderiv_right (m := ∞) (by simp)
  have hfirst : PointJetsVanish
      (fun i y => op (B i (a i y)) (fderiv ℝ (a i) y)) x l :=
    PointJetsVanish.bilinear (F := T) (G := E →L[ℝ] E) (H := T)
      hC hd hCs hds op
  have hfirsts (i : ι) : ContDiffAt ℝ ∞
      (fun y => op (B i (a i y)) (fderiv ℝ (a i) y)) (x i) :=
    op.isBoundedBilinearMap.contDiff.comp₂_contDiffAt (hCs i) (hds i)
  have hsecond : PointJetsVanish
      (fun i y => op (op (B i (a i y)) (fderiv ℝ (a i) y)) (fderiv ℝ (a i) y)) x l :=
    PointJetsVanish.bilinear (F := T) (G := E →L[ℝ] E) (H := T)
      hfirst hd hfirsts hds op
  simpa only [hop, Function.comp_apply, ContinuousLinearMap.bilinearComp] using hsecond

end PoincareConjecture.M45.PointJetsVanish
