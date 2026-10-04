import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Persistence.SourceNames.Metric
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Persistence.Comparison.Initial.PhysicalInitialChart
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Persistence.Charts.SmoothChartInverse
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Persistence.Limit.Coordinates.NormalizedCoefficients

/-!
# The birth comparison chart on the physical slice

The actual M36 map followed by the local-result embedding is a partial
diffeomorphism on each buffered standard ball. Its exact physical ball
image and its normalized coefficient identity are retained explicitly.
Morgan--Tian, Claim 16.6 and Lemma 16.8, pp. 371-373;
see M44 derivation 44.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology ENNReal

universe u

namespace PoincareMT.M44

local notation "E" => StandardCapSpace

/-- The composed local-result comparison is a smooth partial chart
onto the actual physical ball, with its literal map. Source:
Claim 16.6 and Corollary 16.7, pp. 371-372; M44 derivation 44. -/
theorem exists_physical_birth_chart
    (F : SurgeryFlowData.{u}) (t : ℝ) (hT : t ∈ F.surgery_times)
    [Nonempty (F.slice t).carrier] (i : Fin (F.event t hT).cap_count)
    {R eta : ℝ} (hR : 0 < R) (hReta : R < eta⁻¹)
    (Q : SurgeryCapClose F.standard_initial
      ((F.event t hT).local_result i).output ((F.event t hT).local_result i).metric
      ((F.event t hT).local_result i).tip (((F.event t hT).necks i).neck.scale) eta)
    (hball : Q.map '' F.standard_initial.metric.ball 0 R =
      ((F.event t hT).local_result i).metric.ball ((F.event t hT).local_result i).tip
        (((F.event t hT).necks i).neck.scale * R)) :
    ∃ e : PartialDiffeomorph (𝓡 3) (𝓡 3) E (F.slice t).carrier ∞,
      e.source = F.standard_initial.metric.ball 0 R ∧
      (∀ x, e x = (F.event t hT).local_embed i (Q.map x)) ∧
      e.target = (F.metric t).ball ((F.event t hT).caps i).tip (F.parameters.h t * R) ∧
      IsPreconnected e.target := by
  let f : E → (F.slice t).carrier := fun x => (F.event t hT).local_embed i (Q.map x)
  let B := F.standard_initial.metric.ball 0 R
  have hB : IsOpen B := by
    dsimp only [B]
    rw [M36.standard_ball_eq_euclidean F.standard_initial hR]
    exact Metric.isOpen_ball
  have hsub : B ⊆ Q.toPartialDiffeomorph.source := by
    intro x hx
    exact hx.trans_le (ENNReal.ofReal_le_ofReal hReta.le)
  have hf : ContMDiffOn (𝓡 3) (𝓡 3) ∞ f B :=
    ((F.event t hT).local_embed_smooth i).comp_contMDiffOn (Q.map_smooth.mono hsub)
  have hinj : InjOn f B := by
    intro x hx y hy heq
    exact Q.left_inverse.injOn (hsub hx) (hsub hy)
      ((F.event t hT).local_embed_injective i heq)
  have hD (x : E) (hx : x ∈ B) : Function.Bijective (mfderiv (𝓡 3) (𝓡 3) f x) := by
    have hQ := Poincare.mfderiv_bijective_of_smooth_leftInvOn
      Q.toPartialDiffeomorph.open_source Q.map_smooth Q.inverse_smooth Q.left_inverse (hsub hx)
    have hL := ((F.event t hT).local_result i).metric.mfderiv_bijective_of_pullback_eq
      (F.metric t) (Q.map x) ((F.event t hT).local_metric i (Q.map x))
    have hdiffQ := Q.toPartialDiffeomorph.mdifferentiableAt (by simp) (hsub hx)
    have hdiffL := ((F.event t hT).local_embed_smooth i).mdifferentiable (by simp) (Q.map x)
    change Function.Bijective (mfderiv (𝓡 3) (𝓡 3)
      ((F.event t hT).local_embed i ∘ Q.map) x)
    rw [mfderiv_comp x hdiffL hdiffQ]
    exact hL.comp hQ
  let e := Poincare.partialDiffeomorphOfInjOn f B hB hf hinj hD
  have hcompact := Q.isCompact_closure_image_ball hR hReta
  rw [hball] at hcompact
  have himage : f '' B =
      (F.metric t).ball ((F.event t hT).caps i).tip (F.parameters.h t * R) := by
    calc
      _ = (F.event t hT).local_embed i '' (Q.map '' B) :=
        (image_image ((F.event t hT).local_embed i) Q.map B).symm
      _ = (F.event t hT).local_embed i ''
          ((F.event t hT).local_result i).metric.ball ((F.event t hT).local_result i).tip
            (((F.event t hT).necks i).neck.scale * R) := congrArg _ hball
      _ = (F.metric t).ball ((F.event t hT).caps i).tip
          (((F.event t hT).necks i).neck.scale * R) :=
        local_result_ball_image F t hT i (mul_pos Q.scale_pos hR) hcompact
      _ = _ := congrArg (fun h => (F.metric t).ball ((F.event t hT).caps i).tip (h * R))
        ((F.event t hT).neck_scale i)
  have hconnected : IsPreconnected B := by
    dsimp only [B]
    rw [M36.standard_ball_eq_euclidean F.standard_initial hR]
    exact (convex_ball (0 : E) _).isPreconnected
  exact ⟨e, rfl, fun _ => rfl, himage, hconnected.image f hf.continuousOn⟩

/-- Pullback of the actual normalized birth metric is the supplied
M36 normalized coefficient field on the comparison domain. Source:
Claim 16.6 and Lemma 16.8, pp. 371-373; M44 derivation 44. -/
theorem physical_birth_pullback_eq
    (F : SurgeryFlowData.{u}) (t : ℝ) (hT : t ∈ F.surgery_times)
    [Nonempty (F.slice t).carrier] (i : Fin (F.event t hT).cap_count)
    {eta : ℝ}
    (Q : SurgeryCapClose F.standard_initial
      ((F.event t hT).local_result i).output ((F.event t hT).local_result i).metric
      ((F.event t hT).local_result i).tip (((F.event t hT).necks i).neck.scale) eta)
    (g : RiemannianMetric 3 (F.slice t).carrier)
    (hg : ∀ y v w, g.inner y v w = (F.parameters.h t)⁻¹ ^ 2 * (F.metric t).inner y v w)
    {f : E → (F.slice t).carrier} {U : Set E} (hU : IsOpen U)
    (hsub : U ⊆ F.standard_initial.metric.ball 0 eta⁻¹)
    (hf : ∀ x ∈ U, f x = (F.event t hT).local_embed i (Q.map x)) :
    EqOn (g.pullbackCoefficients f) Q.normalizedCoefficients U := by
  intro x hx
  have hfg : f =ᶠ[𝓝 x] (F.event t hT).local_embed i ∘ Q.map :=
    eventually_of_mem (hU.mem_nhds hx) hf
  have hdiffQ := Q.toPartialDiffeomorph.mdifferentiableAt (by simp) (hsub hx)
  have hdiffL := ((F.event t hT).local_embed_smooth i).mdifferentiable (by simp) (Q.map x)
  have hderiv := mfderiv_comp x hdiffL hdiffQ
  ext v w
  change g.inner (f x) (mfderiv (𝓡 3) (𝓡 3) f x v)
    (mfderiv (𝓡 3) (𝓡 3) f x w) = _
  rw [hg, hfg.mfderiv_eq, hderiv]
  change (F.parameters.h t)⁻¹ ^ 2 *
    (F.metric t).inner (f x)
      (mfderiv (𝓡 3) (𝓡 3) ((F.event t hT).local_embed i) (Q.map x)
        (mfderiv (𝓡 3) (𝓡 3) Q.map x v))
      (mfderiv (𝓡 3) (𝓡 3) ((F.event t hT).local_embed i) (Q.map x)
        (mfderiv (𝓡 3) (𝓡 3) Q.map x w)) = _
  rw [hf x hx, (F.event t hT).local_metric]
  rw [Q.normalizedCoefficients_apply]
  exact congrArg (fun h : ℝ => h⁻¹ ^ 2 *
    ((F.event t hT).local_result i).metric.inner (Q.map x)
      (mfderiv (𝓡 3) (𝓡 3) Q.map x v) (mfderiv (𝓡 3) (𝓡 3) Q.map x w))
    ((F.event t hT).neck_scale i).symm

end PoincareMT.M44
