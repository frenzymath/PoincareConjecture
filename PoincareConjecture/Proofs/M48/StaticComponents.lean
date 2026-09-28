import PoincareConjecture.Proofs.M48.StaticMetric
import PoincareConjecture.Proofs.M48.StaticTopology









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff ENNReal

universe u

namespace PoincareConjecture

variable {M N : Type u}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N]
  [IsManifold (𝓡 3) ∞ N] [T3Space N] [MeasurableSpace N] [BorelSpace N]
  {g : RiemannianMetric 3 M} {h : RiemannianMetric 3 N}
  {e : Diffeomorph (𝓡 3) (𝓡 3) M N ∞}


noncomputable def SingularCComponent.m48_pullback {D' : LeviCivitaData h} {C : ℝ}
    (K : SingularCComponent h D' C) (he : MetricHomothety g h e 1)
    (H : MetricHomothetyCalculus g h e 1) (D : LeviCivitaData g) :
    SingularCComponent g D C := by
  have hpair (x : M) (v w : TangentSpace (𝓡 3) x)
      (hv : LeviCivitaData.IsOrthonormalPair g x v w) :
      LeviCivitaData.IsOrthonormalPair h (e x)
        (mfderiv (𝓡 3) (𝓡 3) e x v) (mfderiv (𝓡 3) (𝓡 3) e x w) := by
    simpa only [LeviCivitaData.IsOrthonormalPair, he x v v, he x w w,
      he x v w, one_mul] using hv
  exact {
    constant_pos := K.constant_pos
    basepoint := e.symm K.basepoint
    carrier := e ⁻¹' K.carrier
    component_eq := by
      rw [K.component_eq]
      exact M48.preimage_connectedComponent e.toHomeomorph K.basepoint
    compact := e.toHomeomorph.isCompact_preimage.mpr K.compact
    topology := by
      rcases K.topology with hQ | hQ
      · obtain ⟨Q⟩ := hQ
        exact Or.inl ⟨Q.m48_pullback e⟩
      · obtain ⟨Q⟩ := hQ
        exact Or.inr ⟨Q.m48_pullback e⟩
    positive_sectional := by
      intro x hx v w hv
      have hbound := K.positive_sectional (e x) hx _ _ (hpair x v w hv)
      simpa only [H.sectional_eq D D', div_one] using hbound
    sectional_lower := by
      intro x hx v w hv
      rw [H.m48_scalarSup_eq D D']
      have hbound := K.sectional_lower (e x) hx _ _ (hpair x v w hv)
      simpa only [H.sectional_eq D D', div_one] using hbound
    diameter_lower := by
      rw [H.m48_intrinsicDiameter_eq,
        H.m48_scalar_range D D' K.carrier (fun r => r ^ (-1 / 2 : ℝ))]
      exact K.diameter_lower
    diameter_upper := by
      rw [H.m48_intrinsicDiameter_eq,
        H.m48_scalar_range D D' K.carrier (fun r => r ^ (-1 / 2 : ℝ))]
      exact K.diameter_upper }

omit [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [T3Space N] [MeasurableSpace N] [BorelSpace N] in

theorem M48.singularMetricPullback_eq (he : MetricHomothety g h e 1)
    {X : Type u} [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X] [IsManifold (𝓡 3) ∞ X]
    (i : X → N) (hi : ContMDiff (𝓡 3) (𝓡 3) ∞ i) :
    singularMetricPullback g (e.symm ∘ i) = singularMetricPullback h i := by
  let j := e.symm ∘ i
  have hj := e.symm.contMDiff.comp hi
  have hcomp : e ∘ j = i := by
    funext x
    exact e.apply_symm_apply _
  funext x v
  have hd : (mfderiv (𝓡 3) (𝓡 3) e (j x)).comp (mfderiv (𝓡 3) (𝓡 3) j x) =
      mfderiv (𝓡 3) (𝓡 3) i x := by
    rw [← mfderiv_comp x (e.contMDiff.mdifferentiable (by simp) _)
      (hj.mdifferentiable (by simp) _), hcomp]
  have hv (w : TangentSpace (𝓡 3) x) :
      mfderiv (𝓡 3) (𝓡 3) e (j x) (mfderiv (𝓡 3) (𝓡 3) j x w) =
        mfderiv (𝓡 3) (𝓡 3) i x w := congrArg (fun A => A w) hd
  have hm := he (j x) (mfderiv (𝓡 3) (𝓡 3) j x (v 0))
    (mfderiv (𝓡 3) (𝓡 3) j x (v 1))
  rw [hv, hv, one_mul] at hm
  dsimp only [j, Function.comp_apply] at hm
  rw [e.apply_symm_apply] at hm
  exact hm.symm


noncomputable def SingularRoundComponent.m48_pullback {epsilon : ℝ}
    (K : SingularRoundComponent h epsilon) (he : MetricHomothety g h e 1) :
    SingularRoundComponent g epsilon where
  epsilon_pos := K.epsilon_pos
  basepoint := e.symm K.basepoint
  carrier := e ⁻¹' K.carrier
  component_eq := by
    rw [K.component_eq]
    exact M48.preimage_connectedComponent e.toHomeomorph K.basepoint
  compact := e.toHomeomorph.isCompact_preimage.mpr K.compact
  model := K.model
  model_compact := K.model_compact
  model_connected := K.model_connected
  model_metric := K.model_metric
  model_connection := K.model_connection
  model_curvature_one := K.model_curvature_one
  forward := e.symm ∘ K.forward
  inverse := K.inverse ∘ e
  forward_image := by
    rw [Set.range_comp, K.forward_image]
    exact e.toHomeomorph.symm.image_eq_preimage_symm _
  forward_openEmbedding := e.symm.toHomeomorph.isOpenEmbedding.comp K.forward_openEmbedding
  forward_smooth := e.symm.contMDiff.comp K.forward_smooth
  inverse_smooth := K.inverse_smooth.comp e.contMDiff.contMDiffOn (fun _ hx => hx)
  left_inverse := fun x => by
    dsimp only [Function.comp_apply]
    rw [e.apply_symm_apply]
    exact K.left_inverse x
  right_inverse := fun x hx => by
    dsimp only [Function.comp_apply]
    rw [K.right_inverse hx, e.symm_apply_apply]
  scale := K.scale
  scale_pos := K.scale_pos
  metric_comparison := by
    rw [M48.singularMetricPullback_eq he K.forward K.forward_smooth]
    exact K.metric_comparison

end PoincareConjecture
