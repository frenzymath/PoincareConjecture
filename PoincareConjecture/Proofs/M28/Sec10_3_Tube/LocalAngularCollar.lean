import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Tube.Gluing.Angular
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Tube.Gluing.ContainedCollar
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.LocalGluingSliceProjection
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension














set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.EpsilonNeck

local notation "CylModel" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)



theorem exists_angular_collar_extension_m28 :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        {g : RiemannianMetric 3 M} (A B : EpsilonNeck g),
        A.epsilon ≤ ε₀ → B.epsilon ≤ ε₀ →
        ∀ s ∈ Ioo (-B.epsilon⁻¹) B.epsilon⁻¹,
        (∀ q : UnitTwoSphere, B.coordinate_map (q, s) ∈ A.carrier) →
        ∃ (r : ℝ) (D : Diffeomorph CylModel CylModel
            RoundCylinderSpace RoundCylinderSpace ∞),
          0 < r ∧ (∀ p : RoundCylinderSpace, (D p).2 = p.2) ∧
          ∀ t : ℝ, |t| < r →
            s + t ∈ Ioo (-B.epsilon⁻¹) B.epsilon⁻¹ ∧
            (∀ q : UnitTwoSphere, B.coordinate_map (q, s + t) ∈ A.carrier) ∧
            ∀ q : UnitTwoSphere,
              (D (q, t)).1 = (A.coordinate_inverse (B.coordinate_map (q, s + t))).1 := by
  obtain ⟨ε₀, hε₀, hε₀small, hprojection⟩ := exists_sphereSlice_projection_diffeomorph_m28.{u}
  refine ⟨ε₀, hε₀, hε₀small, ?_⟩
  intro M _ _ _ _ _ _ _ g A B hA hB s hs hc
  obtain ⟨R, hR, hcollar⟩ := A.exists_contained_slice_collar B hs hc
  let r := R / 4
  have hr : 0 < r := by dsimp [r]; positivity
  have hrR : 2 * r < R := by dsimp [r]; linarith
  let b : ContDiffBump (0 : ℝ) := ⟨r, 2 * r, hr, by linarith⟩
  let σ : ℝ → ℝ := fun t => s + t * b t
  have hσ : ContDiff ℝ ∞ σ := contDiff_const.add (contDiff_id.mul b.contDiff)
  have hσinner (t : ℝ) (ht : |t| < r) : σ t = s + t := by
    have hb : b t = 1 := b.one_of_mem_closedBall
      (by simpa [Metric.mem_closedBall, Real.dist_eq] using ht.le)
    simp only [σ, hb, mul_one]
  have hdisp (t : ℝ) : |t * b t| < R := by
    by_cases ht : |t| < 2 * r
    · have hle : |t * b t| ≤ |t| := by
        rw [abs_mul, abs_of_nonneg b.nonneg]
        nlinarith [b.le_one (x := t), abs_nonneg t]
      exact hle.trans_lt (ht.trans hrR)
    · have hb : b t = 0 := b.zero_of_le_dist
        (by simpa [Real.dist_eq] using le_of_not_gt ht)
      simpa only [hb, mul_zero, abs_zero] using hR
  have hbound (t : ℝ) : σ t ∈ Ioo (-B.epsilon⁻¹) B.epsilon⁻¹ := by
    obtain ⟨q⟩ := (inferInstance : Nonempty UnitTwoSphere)
    exact (hcollar q (t * b t) (hdisp t)).1
  have hcontain (t : ℝ) (q : UnitTwoSphere) : B.coordinate_map (q, σ t) ∈ A.carrier :=
    (hcollar q (t * b t) (hdisp t)).2
  choose f hf using fun t => hprojection A B hA hB (hbound t) (hcontain t)
  have hf_smooth : ContMDiff CylModel (𝓡 2) ∞
      (fun p : RoundCylinderSpace => f p.2 p.1) := by
    have heq : (fun p : RoundCylinderSpace => f p.2 p.1) =
        fun p => (A.coordinate_inverse (B.coordinate_map (p.1, σ p.2))).1 :=
      funext fun p => hf p.2 p.1
    rw [heq]
    have hcoord : ContMDiff CylModel CylModel ∞
        (fun p : RoundCylinderSpace => A.coordinate_inverse
          (B.coordinate_map (p.1, σ p.2))) := by
      intro p
      apply (A.coordinate_inverse_smooth.contMDiffAt
        (A.carrier_open.mem_nhds (hcontain p.2 p.1))).comp p
      apply (B.coordinate_map_smooth.contMDiffAt
        (B.cylinderDomain_open.mem_nhds ⟨mem_univ _, hbound p.2⟩)).comp p
      exact (contMDiff_fst.prodMk (hσ.contMDiff.comp contMDiff_snd)).contMDiffAt
    exact contMDiff_fst.comp hcoord
  obtain ⟨D, hD⟩ := CylinderGluing.exists_fiber_diffeomorph f hf_smooth
  refine ⟨r, D, hr, ?_, ?_⟩
  · intro p
    rw [hD]
  · intro t ht
    refine ⟨hσinner t ht ▸ hbound t, ?_, ?_⟩
    · intro q
      simpa only [hσinner t ht] using hcontain t q
    · intro q
      rw [hD]
      simpa only [hσinner t ht] using hf t q

end PoincareConjecture.EpsilonNeck
