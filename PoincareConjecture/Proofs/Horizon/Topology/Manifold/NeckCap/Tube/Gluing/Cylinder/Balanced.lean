import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Tube.Gluing.Finite.Certificate
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Tube.Gluing.Infinite.BiInfinite










set_option autoImplicit false

open Set TopologicalSpace
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.BalancedNeckChain

local notation "CylModel" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)

theorem exists_cylinder_with_middle_threshold :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        {g : RiemannianMetric 3 M} {ε : ℝ} (C : BalancedNeckChain g ε),
        ε ≤ ε₀ → (∀ i ∈ C.shape.active, (C.neck i).IsSeparating) →
        ∃ D : Diffeomorph CylModel (𝓡 3) RoundCylinderSpace C.unionOpen ∞,
        ∃ j ∈ C.shape.active, ∃ c ∈ Ioo (-ε⁻¹) ε⁻¹,
          range (fun q : UnitTwoSphere => (D (q, 0) : M)) =
            range (fun q : UnitTwoSphere => (C.neck j).coordinate_map (q, c)) := by
  obtain ⟨ε₁, hε₁, hsmall, hfinite⟩ := exists_finite_cylinder_with_middle_threshold.{u}
  obtain ⟨ε₂, hε₂, _, hforward⟩ := exists_normalized_forward_cylinder_threshold.{u}
  obtain ⟨ε₃, hε₃, _, hbackward⟩ := exists_normalized_backward_cylinder_threshold.{u}
  obtain ⟨ε₄, hε₄, _, hbi⟩ := exists_biInfinite_cylinder_threshold.{u}
  refine ⟨min ε₁ (min ε₂ (min ε₃ ε₄)), lt_min hε₁ (lt_min hε₂ (lt_min hε₃ hε₄)),
    (min_le_left _ _).trans hsmall, ?_⟩
  intro M _ _ _ _ _ _ _ g ε C hε hsep
  have hb : ε ≤ ε₁ ∧ ε ≤ ε₂ ∧ ε ≤ ε₃ ∧ ε ≤ ε₄ := by
    simpa only [le_min_iff] using hε
  have hεpos : 0 < ε := by
    obtain ⟨i, hi⟩ := C.active_nonempty
    exact C.epsilon_eq i hi ▸ (C.neck i).epsilon_pos
  have hzero : (0 : ℝ) ∈ Ioo (-ε⁻¹) ε⁻¹ :=
    ⟨neg_neg_of_pos (inv_pos.mpr hεpos), inv_pos.mpr hεpos⟩
  cases hshape : C.shape with
  | finite a b => simpa only [hshape] using hfinite C hb.1 a b hshape
  | forward a =>
    obtain ⟨D, r, hr, hlocal, _⟩ := hforward C hb.2.1 hsep a hshape
    refine ⟨D, a, by change a ≤ a; exact le_rfl, 0, hzero, ?_⟩
    congr 1
    funext q
    exact hlocal (q, 0) (by simpa only [abs_zero] using hr)
  | backward b =>
    obtain ⟨D, r, hr, hlocal, _⟩ := hbackward C hb.2.2.1 b hshape
    refine ⟨D, b, by change b ≤ b; exact le_rfl, 0, hzero, ?_⟩
    congr 1
    funext q
    simpa only [neg_zero] using hlocal (q, 0) (by simpa only [abs_zero] using hr)
  | biInfinite =>
    obtain ⟨D, hDzero⟩ := hbi C hb.2.2.2 hsep hshape 0
    exact ⟨D, 0, by trivial, 0, hzero,
      hDzero.trans (C.neck 0).centralSphere_range.symm⟩

theorem exists_openCylinderModel_threshold :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        {g : RiemannianMetric 3 M} {ε : ℝ} (C : BalancedNeckChain g ε),
        ε ≤ ε₀ → (∀ i ∈ C.shape.active, (C.neck i).IsSeparating) →
        ∃ T : OpenCylinderModel (C.unionOpen : Set M),
          ∀ i ∈ C.shape.active, SmoothSphereIsotopicIn (C.unionOpen : Set M)
            (C.neck i).central_sphere T.middleSphere := by
  obtain ⟨ε₁, hε₁, hsmall, hcylinder⟩ := exists_cylinder_with_middle_threshold.{u}
  obtain ⟨ε₂, hε₂, _, hmodel⟩ := exists_openCylinderModel_of_middle_slice_threshold.{u}
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, (min_le_left _ _).trans hsmall, ?_⟩
  intro M _ _ _ _ _ _ _ g ε C hε hsep
  obtain ⟨D, j, hj, c, hc, hDzero⟩ := hcylinder C (hε.trans (min_le_left _ _)) hsep
  exact hmodel C (hε.trans (min_le_right _ _)) D j hj c hc hDzero

end PoincareConjecture.BalancedNeckChain
