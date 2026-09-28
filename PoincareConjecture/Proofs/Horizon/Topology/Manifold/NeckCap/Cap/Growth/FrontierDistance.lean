import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.Growth.BoundaryDistance
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.Growth.MixedBoundary













set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture.CapCertificate



theorem exists_frontier_edist_lower_of_boundary_contact :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 1000 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        {g : RiemannianMetric 3 M},
        ∀ (C D : CapCertificate g), C.epsilon ≤ ε₀ → D.epsilon = C.epsilon →
        (frontier C.carrier ∩ D.boundary_sphere).Nonempty →
        ∀ {z y : M}, z ∈ frontier C.carrier → y ∉ D.carrier →
          ENNReal.ofReal ((0.38 : ℝ) * D.boundary_neck.scale * D.epsilon⁻¹) ≤
            g.edist z y := by
  obtain ⟨ε₁, hε₁, hsmall, hfrontier⟩ :=
    exists_frontier_carrier_subset_closure_positive_end.{u}
  obtain ⟨ε₂, hε₂, _, hscale⟩ :=
    EpsilonNeck.exists_scale_comparison_at_common_closure.{u}
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, (min_le_left _ _).trans hsmall, ?_⟩
  intro M _ _ _ _ _ _ _ g C D hε heq ⟨x, hx, hxD⟩ z y hz hy
  have hCsmall : C.epsilon ≤ 1 / 1000 :=
    (hε.trans (min_le_left _ _)).trans hsmall
  have hxquarter := hfrontier C (hε.trans (min_le_left _ _)) hx
  have hzquarter := hfrontier C (hε.trans (min_le_left _ _)) hz
  have hdiam := C.end_neck.edist_le_of_mem_closure_positive_quarter_pair
    (C.end_neck_epsilon.trans_le hCsmall)
    (by simpa only [C.end_neck_epsilon] using hxquarter)
    (by simpa only [C.end_neck_epsilon] using hzquarter)
  rw [C.end_neck_epsilon, ← heq] at hdiam
  have hs := (hscale C.end_neck D.boundary_neck
    (C.end_neck_epsilon.trans_le (hε.trans (min_le_right _ _)))
    ((D.boundary_neck_epsilon.trans heq).trans_le (hε.trans (min_le_right _ _)))
    ⟨x, frontier_subset_closure (C.frontier_carrier_subset_frontier_end hx),
      subset_closure (D.boundary_neck.central_sphere_subset
        (D.boundary_eq_neck_sphere ▸ hxD))⟩).1
  have hnum : (0.51 : ℝ) * C.end_neck.scale * D.epsilon⁻¹ +
      (0.38 : ℝ) * D.boundary_neck.scale * D.epsilon⁻¹ ≤
        (0.9 : ℝ) * D.boundary_neck.scale * D.epsilon⁻¹ := by
    have hb : (0.51 : ℝ) * C.end_neck.scale + (0.38 : ℝ) * D.boundary_neck.scale ≤
        (0.9 : ℝ) * D.boundary_neck.scale := by
      nlinarith [C.end_neck.scale_pos]
    nlinarith [mul_le_mul_of_nonneg_right hb (inv_pos.mpr D.epsilon_pos).le]
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hscaleC := C.end_neck.scale_pos
  have hscaleD := D.boundary_neck.scale_pos
  have hepsilon := D.epsilon_pos
  apply ENNReal.le_of_add_le_add_left ENNReal.ofReal_ne_top
    (a := ENNReal.ofReal ((0.51 : ℝ) * C.end_neck.scale * D.epsilon⁻¹))
  calc
    _ = ENNReal.ofReal ((0.51 : ℝ) * C.end_neck.scale * D.epsilon⁻¹ +
        (0.38 : ℝ) * D.boundary_neck.scale * D.epsilon⁻¹) := by
      rw [ENNReal.ofReal_add (by positivity) (by positivity)]
    _ ≤ ENNReal.ofReal ((0.9 : ℝ) * D.boundary_neck.scale * D.epsilon⁻¹) :=
      ENNReal.ofReal_le_ofReal hnum
    _ ≤ g.edist x y := D.boundary_edist_lower_of_not_mem_carrier hxD hy
    _ ≤ g.edist x z + g.edist z y := Manifold.riemannianEDist_triangle
    _ ≤ ENNReal.ofReal ((0.51 : ℝ) * C.end_neck.scale * D.epsilon⁻¹) + g.edist z y :=
      add_le_add hdiam le_rfl



theorem exists_frontier_edist_lower_of_mixed_boundary :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 1000 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        {g : RiemannianMetric 3 M},
        ∀ (C D : CapCertificate g), C.epsilon ≤ ε₀ → D.epsilon = C.epsilon →
        (D.boundary_sphere ∩ C.carrier).Nonempty →
        (¬ D.boundary_sphere ⊆ C.carrier) →
        ∀ {z y : M}, z ∈ frontier C.carrier → y ∉ D.carrier →
          ENNReal.ofReal ((0.38 : ℝ) * D.boundary_neck.scale * D.epsilon⁻¹) ≤
            g.edist z y := by
  obtain ⟨ε₀, hε₀, hsmall, hbound⟩ := exists_frontier_edist_lower_of_boundary_contact.{u}
  refine ⟨ε₀, hε₀, hsmall, ?_⟩
  intro M _ _ _ _ _ _ _ g C D hε heq hmeet hmiss z y hz hy
  exact hbound C D hε heq (C.frontier_inter_boundary_nonempty_of_mixed D hmeet hmiss) hz hy

end PoincareConjecture.CapCertificate
