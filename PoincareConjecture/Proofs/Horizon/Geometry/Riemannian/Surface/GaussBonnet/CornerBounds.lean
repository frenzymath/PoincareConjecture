import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.MetricCorners








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle

namespace PoincareConjecture

variable {S : Type*} [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [IsManifold (𝓡 2) ∞ S]


theorem RiemannianMetric.cornerAngle_mem_Ioo_of_not_smul
    (g : RiemannianMetric 2 S) (x : S) (v w : TangentSpace (𝓡 2) x)
    (h : ∀ a : ℝ, w ≠ a • v) : g.cornerAngle x v w ∈ Ioo 0 Real.pi := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 2) : S → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hang : g.cornerAngle x v w = InnerProductGeometry.angle v w := by
    unfold RiemannianMetric.cornerAngle InnerProductGeometry.angle
    change Real.arccos (inner ℝ
      ((Real.sqrt (inner ℝ v v))⁻¹ • v) ((Real.sqrt (inner ℝ w w))⁻¹ • w)) = _
    simp only [real_inner_self_eq_norm_sq, Real.sqrt_sq (norm_nonneg _),
      real_inner_smul_left, inner_smul_right, mul_inv_rev, div_eq_mul_inv]
    congr 1
    ring
  rw [hang]
  constructor
  · apply lt_of_le_of_ne (InnerProductGeometry.angle_nonneg _ _)
    intro heq
    obtain ⟨_, a, _, ha⟩ := InnerProductGeometry.angle_eq_zero_iff.mp heq.symm
    exact h a ha
  · apply lt_of_le_of_ne (InnerProductGeometry.angle_le_pi _ _)
    intro heq
    obtain ⟨_, a, _, ha⟩ := InnerProductGeometry.angle_eq_pi_iff.mp heq
    exact h a ha

namespace Topology.Surface



theorem coordinateSectorAngle_mem_Ioo
    (g : RiemannianMetric 2 S)
    (F : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) S)
    (c : AffineBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 2)))
    (hF : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F F.source)
    (hFi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F.symm F.target)
    (hc : c 0 ∈ F.source) :
    g.cornerAngle (F (c 0))
      ((mfderiv (𝓡 2) (𝓡 2) F (c 0)) (c 1 - c 0))
      ((mfderiv (𝓡 2) (𝓡 2) F (c 0)) (c 2 - c 0)) ∈ Ioo 0 Real.pi := by
  apply g.cornerAngle_mem_Ioo_of_not_smul
  intro a ha
  have hD : F.MDifferentiable (𝓡 2) (𝓡 2) :=
    ⟨hF.mdifferentiableOn (by simp), hFi.mdifferentiableOn (by simp)⟩
  have heq : c 2 - c 0 = a • (c 1 - c 0) := by
    apply hD.mfderiv_injective hc
    exact ha.trans (map_smul (mfderiv (𝓡 2) (𝓡 2) F (c 0)) a (c 1 - c 0)).symm
  have h := congrArg (c.coord 2).linear heq
  have hval (i : Fin 3) : (c.coord 2).linear (c i - c 0) = c.coord 2 (c i) - c.coord 2 (c 0) :=
    (c.coord 2).linearMap_vsub _ _
  rw [map_smul, hval 2, hval 1] at h
  norm_num [AffineBasis.coord_apply, Fin.ext_iff] at h

omit [IsManifold (𝓡 2) ∞ S] in


theorem coordinateTriangleVelocity_not_smul
    (F : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) S)
    (b : AffineBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 2)))
    (hF : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F F.source)
    (hFi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F.symm F.target)
    (hb : convexHull ℝ (range b) ⊆ F.source)
    {i j k : Fin 3} (hik : i ≠ k) (hjk : j ≠ k) (a : ℝ) :
    coordinateTriangleVelocity F b i k ≠ a • coordinateTriangleVelocity F b i j := by
  intro h
  rw [coordinateTriangleVelocity_eq_differential F b hF hb,
    coordinateTriangleVelocity_eq_differential F b hF hb] at h
  have hD : F.MDifferentiable (𝓡 2) (𝓡 2) :=
    ⟨hF.mdifferentiableOn (by simp), hFi.mdifferentiableOn (by simp)⟩
  have heq : b k - b i = a • (b j - b i) := by
    apply hD.mfderiv_injective (hb (subset_convexHull ℝ _ (mem_range_self i)))
    dsimp only [TangentSpace] at h ⊢
    exact h.trans (map_smul (mfderiv (𝓡 2) (𝓡 2) F (b i)) a (b j - b i)).symm
  have hc := congrArg (b.coord k).linear heq
  have hval (m : Fin 3) : (b.coord k).linear (b m - b i) = b.coord k (b m) - b.coord k (b i) :=
    (b.coord k).linearMap_vsub (b m) (b i)
  rw [map_smul, hval k, hval j, b.coord_apply_eq,
    b.coord_apply_ne hik.symm, b.coord_apply_ne hjk.symm] at hc
  norm_num at hc



theorem coordinateTriangleAngle_mem_Ioo
    (g : RiemannianMetric 2 S)
    (F : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) S)
    (b : AffineBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 2)))
    (hF : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F F.source)
    (hFi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F.symm F.target)
    (hb : convexHull ℝ (range b) ⊆ F.source) (i : Fin 3) :
    coordinateTriangleAngle g F b i ∈ Ioo 0 Real.pi := by
  apply g.cornerAngle_mem_Ioo_of_not_smul
  apply coordinateTriangleVelocity_not_smul F b hF hFi hb
  · exact (Fin.succAbove_ne i 1).symm
  · exact (Fin.succAbove_right_injective.ne (by decide : (0 : Fin 2) ≠ 1))

end Topology.Surface
end PoincareConjecture
