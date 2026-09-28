import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.Core.Standardization
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Diffeomorph.EssentialSphere.RadialCylinder










set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.CapCertificate

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace E3 M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  {g : RiemannianMetric 3 M} (C : CapCertificate g)

private theorem radial_coordinates_of_one_lt_norm {x : E3} (hx : 1 < ‖x‖)
    {r : ℝ} (hr : ‖x‖ < Real.exp r) :
    ∃ p : RoundCylinderSpace, p.2 ∈ Ioo 0 r ∧ Real.exp p.2 • (p.1 : E3) = x := by
  have hx0 : x ≠ 0 := by intro h; norm_num [h] at hx
  let J := Poincare.sphereCylinderDiffeomorphPunctured
  let p := J.symm ⟨x, hx0⟩
  have hp : Real.exp p.2 • (p.1 : E3) = x :=
    congrArg Subtype.val (J.apply_symm_apply ⟨x, hx0⟩)
  have hnorm : Real.exp p.2 = ‖x‖ := by
    rw [← hp, norm_smul]
    simp [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  refine ⟨p, ⟨?_, ?_⟩, hp⟩
  · apply Real.exp_lt_exp.mp
    simpa only [Real.exp_zero, hnorm] using hx
  · exact Real.exp_lt_exp.mp (hnorm.symm ▸ hr)



theorem ball_image_eq_closed_core_union_collar
    (b : OpenPartialHomeomorph E3 M)
    (hs : Metric.closedBall 0 1 ⊆ b.source)
    (hclosed : b '' Metric.closedBall 0 1 = C.closed_core)
    {r : ℝ} (hr : 0 < r) (σ : ℝ)
    (hcollar : ∀ p : RoundCylinderSpace, |p.2| < r →
      Real.exp p.2 • (p.1 : E3) ∈ b.source ∧
      b (Real.exp p.2 • (p.1 : E3)) = C.boundary_neck.coordinate_map (p.1, σ * p.2)) :
    Metric.ball 0 (Real.exp r) ⊆ b.source ∧
      b '' Metric.ball 0 (Real.exp r) = C.closed_core ∪
        (fun p : RoundCylinderSpace => C.boundary_neck.coordinate_map (p.1, σ * p.2)) ''
          (univ ×ˢ Ioo 0 r) := by
  have hnorm {x : E3} (hx : x ∈ Metric.ball 0 (Real.exp r)) : ‖x‖ < Real.exp r := by
    simpa using hx
  have hsmall : Metric.closedBall (0 : E3) 1 ⊆ Metric.ball 0 (Real.exp r) :=
    Metric.closedBall_subset_ball (by simpa using Real.exp_lt_exp.mpr hr)
  constructor
  · intro x hx
    by_cases hle : ‖x‖ ≤ 1
    · exact hs (by simpa using hle)
    · obtain ⟨p, hp, rfl⟩ := radial_coordinates_of_one_lt_norm (lt_of_not_ge hle) (hnorm hx)
      exact (hcollar p (by simpa only [abs_of_pos hp.1] using hp.2)).1
  · apply Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩
      by_cases hle : ‖x‖ ≤ 1
      · exact Or.inl (hclosed ▸ mem_image_of_mem b (by simpa using hle))
      · obtain ⟨p, hp, rfl⟩ := radial_coordinates_of_one_lt_norm (lt_of_not_ge hle) (hnorm hx)
        exact Or.inr ⟨p, ⟨mem_univ _, hp⟩,
          (hcollar p (by simpa only [abs_of_pos hp.1] using hp.2)).2.symm⟩
    · rintro x (hx | ⟨p, hp, rfl⟩)
      · rw [← hclosed] at hx
        exact image_mono hsmall hx
      · refine ⟨Real.exp p.2 • (p.1 : E3), ?_, (hcollar p ?_).2⟩
        · have he : Real.exp p.2 < Real.exp r := Real.exp_lt_exp.mpr hp.2.2
          simpa [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs,
            abs_of_pos (Real.exp_pos _)] using he
        · simpa only [abs_of_pos hp.2.1] using hp.2.2

end PoincareConjecture.CapCertificate
