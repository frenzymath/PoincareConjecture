import PoincareConjecture.Proofs.M32.Claim11_32.Extension.StaticMetric
import PoincareConjecture.Proofs.M32.Claim11_32.Extension.StaticTopology
import PoincareConjecture.Definitions.Ch11.SingularLimits













set_option autoImplicit false

open Set
open scoped Manifold ContDiff ENNReal

universe u

namespace PoincareConjecture.M32

variable {M N : Type u}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N]
  [IsManifold (𝓡 3) ∞ N] [T3Space N] [MeasurableSpace N] [BorelSpace N]
  {g : RiemannianMetric 3 M} {h : RiemannianMetric 3 N}
  {e : Diffeomorph (𝓡 3) (𝓡 3) M N ∞}



noncomputable def pullbackSingularCComponent {D' : LeviCivitaData h} {C : ℝ}
    (K : SingularCComponent h D' C) (he : MetricHomothety g h e 1)
    (Hcal : MetricHomothetyCalculus g h e 1) (D : LeviCivitaData g) :
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
      exact homeomorph_preimage_connectedComponent e.toHomeomorph K.basepoint
    compact := e.toHomeomorph.isCompact_preimage.mpr K.compact
    topology := by
      rcases K.topology with hQ | hQ
      · obtain ⟨Q⟩ := hQ
        exact Or.inl ⟨pullbackClosedComponentCertificate e Q⟩
      · obtain ⟨Q⟩ := hQ
        exact Or.inr ⟨pullbackClosedComponentCertificate e Q⟩
    positive_sectional := by
      intro x hx v w hv
      have hbound := K.positive_sectional (e x) hx _ _ (hpair x v w hv)
      simpa only [Hcal.sectional_eq D D', div_one] using hbound
    sectional_lower := by
      intro x hx v w hv
      rw [unitHomothety_scalarSup_eq Hcal D D']
      have hbound := K.sectional_lower (e x) hx _ _ (hpair x v w hv)
      simpa only [Hcal.sectional_eq D D', div_one] using hbound
    diameter_lower := by
      rw [unitHomothety_intrinsicDiameter_eq Hcal,
        unitHomothety_scalar_range Hcal D D' K.carrier (fun r => r ^ (-1 / 2 : ℝ))]
      exact K.diameter_lower
    diameter_upper := by
      rw [unitHomothety_intrinsicDiameter_eq Hcal,
        unitHomothety_scalar_range Hcal D D' K.carrier (fun r => r ^ (-1 / 2 : ℝ))]
      exact K.diameter_upper }

omit [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [T3Space N] [MeasurableSpace N] [BorelSpace N] in


theorem singularMetricPullback_eq_of_unitHomothety (he : MetricHomothety g h e 1)
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



noncomputable def pullbackSingularRoundComponent {epsilon : ℝ}
    (K : SingularRoundComponent h epsilon) (he : MetricHomothety g h e 1) :
    SingularRoundComponent g epsilon where
  epsilon_pos := K.epsilon_pos
  basepoint := e.symm K.basepoint
  carrier := e ⁻¹' K.carrier
  component_eq := by
    rw [K.component_eq]
    exact homeomorph_preimage_connectedComponent e.toHomeomorph K.basepoint
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
    rw [singularMetricPullback_eq_of_unitHomothety he K.forward K.forward_smooth]
    exact K.metric_comparison

end PoincareConjecture.M32
