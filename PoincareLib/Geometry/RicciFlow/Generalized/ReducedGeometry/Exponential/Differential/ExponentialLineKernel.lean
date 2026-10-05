import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Exponential.Differential.ExponentialLineRegularity

/-!
# A kernel direction has stationary actual endpoint coordinates

Morgan-Tian Lemma 6.22 and Proposition 6.30, pp. 115-116, 118-119.
The affine chain rule identifies the actual parameter tangent with
the frozen exponential differential. Its vanishing therefore forces
the derivative of every smooth inverse-gauge coordinate to vanish.
-/

set_option autoImplicit false
-- Actual horizontal and self-model tangent fibers use the installed metric norm.
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareMT.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T : ℝ} {x : G.Point}

private theorem horizontal_t2Space : T2Space (G.Horizontal x) :=
  FiberBundle.t2Space (EuclideanSpace ℝ (Fin n)) G.Horizontal x

attribute [local instance] horizontal_t2Space

/-- The affine parameter tangent is exactly the actual frozen
exponential differential, including physical endpoint times,
Lemma 6.22, pp. 115-116. -/
theorem exponentialLine_mfderiv (E : M14ExponentialFamily G T x)
    (Z W : G.Horizontal x) {s : ℝ} (hs : (Z, s) ∈ E.domain) :
    mfderiv (𝓘(ℝ, ℝ)) (spacetimeModel n) (fun r : ℝ => E.gamma (Z + r • W) s) 0 (1 : ℝ) =
      (E.differential Z s hs W).val := by
  let metric := G.spacetime.horizontalMetric.toRiemannianMetric
  let : NormedAddCommGroup (G.Horizontal x) :=
    (metric.toCore x).toNormedAddCommGroupOfTopology
      (metric.continuousAt x) (metric.isVonNBounded x)
  let : InnerProductSpace ℝ (G.Horizontal x) :=
    .ofCoreOfTopology (metric.toCore x) (metric.continuousAt x) (metric.isVonNBounded x)
  let : Bundle.RiemannianBundle (G.Horizontal : G.Point → Type _) := ⟨metric⟩
  have hline : HasDerivAt (fun r : ℝ => Z + r • W) W 0 := by
    simpa only [id_eq, one_smul] using ((hasDerivAt_id (0 : ℝ)).smul_const W).const_add Z
  have hlineM : mfderiv (𝓘(ℝ, ℝ)) (𝓘(ℝ, G.Horizontal x))
      (fun r : ℝ => Z + r • W) 0 (1 : ℝ) = W := by
    rw [mfderiv_eq_fderiv, hline.hasFDerivAt.fderiv]
    change (1 : ℝ) • W = W
    exact one_smul ℝ W
  have hchain := mfderiv_comp_apply_of_eq (x := (0 : ℝ))
    ((exponentialFamily_gamma_slice_contMDiffAt E hs).mdifferentiableAt (by simp))
    hline.differentiableAt.mdifferentiableAt (by simp only [zero_smul, add_zero]) (1 : ℝ)
  rw [hlineM] at hchain
  exact hchain.trans (E.differential_pointwise_mfderiv Z s hs W).symm

/-- A kernel vector of the actual exponential differential has zero
endpoint-coordinate derivative in every smooth compatible inverse
gauge at an interior meeting time, Proposition 6.30, pp. 118-119. -/
theorem exponentialLine_coordinate_deriv_eq_zero (E : M14ExponentialFamily G T x)
    (Z W : G.Horizontal x) {b c : ℝ} {U : Set ℝ} (hU : IsOpen U) (hzero : 0 ∈ U)
    (hsurv : ∀ r ∈ U, (Z + r • W, b) ∈ E.domain) (hc : c ∈ Ioo 0 b)
    (hZ : (Z, c) ∈ E.domain) (hker : E.differential Z c hZ W = 0)
    (j : G.gaugeCover.index)
    (lift : G.Point → (G.timeIntervals.interval (G.gaugeCover.interval j)).Point ×
      G.gaugeCover.spatial j)
    (hlift : ContMDiffAt (spacetimeModel n) (spacetimeModel n) ∞ lift (E.gamma Z c)) :
    deriv (fun r : ℝ => (lift (E.gamma (Z + r • W) c)).2.val) 0 = 0 := by
  have hF : MDifferentiableAt (𝓘(ℝ, ℝ)) (spacetimeModel n)
      (fun r : ℝ => E.gamma (Z + r • W) c) 0 := by
    have h := (exponentialLine_contMDiffAt E Z W hU hsurv hc hzero).comp 0
      (contMDiffAt_const.prodMk contMDiffAt_id)
    exact h.mdifferentiableAt (by simp)
  have hq : MDifferentiableAt (spacetimeModel n) (𝓡 n)
      (fun q => (lift q).2.val) (E.gamma Z c) :=
    (contMDiff_subtype_val.contMDiffAt.comp _
      (contMDiff_snd.contMDiffAt.comp _ hlift)).mdifferentiableAt (by simp)
  have hchain := mfderiv_comp_apply_of_eq (x := (0 : ℝ)) hq hF
    (by simp only [zero_smul, add_zero]) (1 : ℝ)
  rw [exponentialLine_mfderiv E Z W hZ, hker] at hchain
  have hchain0 : mfderiv (𝓘(ℝ, ℝ)) (𝓡 n)
      (fun r : ℝ => (lift (E.gamma (Z + r • W) c)).2.val) 0 (1 : ℝ) = 0 :=
    hchain.trans (map_zero _)
  have hmf : mfderiv (𝓘(ℝ, ℝ)) (𝓡 n)
      (fun r : ℝ => (lift (E.gamma (Z + r • W) c)).2.val) 0 =
      fderiv ℝ (fun r : ℝ => (lift (E.gamma (Z + r • W) c)).2.val) 0 := mfderiv_eq_fderiv
  have hd : fderiv ℝ (fun r : ℝ => (lift (E.gamma (Z + r • W) c)).2.val) 0 (1 : ℝ) = 0 :=
    (congrArg (fun L : ℝ →L[ℝ] EuclideanSpace ℝ (Fin n) => L 1) hmf).symm.trans hchain0
  exact fderiv_apply_one_eq_deriv.symm.trans hd

end PoincareMT.M14
