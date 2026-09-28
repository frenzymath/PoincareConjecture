import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.Boundedness.Projective.Diameter
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Geodesic.Competitor

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open Poincare.Geometry.Riemannian.SpaceForm
open scoped Topology Manifold ContDiff Bundle ENNReal

namespace PoincareConjecture

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]

theorem intrinsicEDist_cylinderCover_le_axial_add
    (g : RiemannianMetric 3 M) (f : RoundCylinderSpace → M)
    {ε Q : ℝ} (hε : 0 < ε) (hQ : 0 < Q)
    (hf : ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ f
      (univ ×ˢ Ioo (-ε⁻¹) ε⁻¹))
    (hclose : RoundCylinderClose ε 0
      (fun z v w => Q * roundCylinderPullback g f z v w))
    {z w : RoundCylinderSpace}
    (hz : z.2 ∈ Ioo (-ε⁻¹) ε⁻¹) (hw : w.2 ∈ Ioo (-ε⁻¹) ε⁻¹) :
    intrinsicEDist g (f '' (univ ×ˢ Ioo (-ε⁻¹) ε⁻¹)) (f z) (f w) ≤
      ENNReal.ofReal (Real.sqrt ((1 + ε) / Q) *
        (|w.2 - z.2| + Real.sqrt 2 * (Real.pi + 1))) := by
  let := RiemannianMetric.lineProductChartedSpace (n := 2) (M := UnitTwoSphere)
  let := RiemannianMetric.lineProductIsManifold (n := 2) (M := UnitTwoSphere)
  let e := roundCylinderModelDiffeomorph
  let U : Set RoundCylinderSpace := univ ×ˢ Ioo (-ε⁻¹) ε⁻¹
  have hU : IsOpen U := isOpen_univ.prod isOpen_Ioo
  have hflat : ContMDiffOn (𝓡 3) (𝓡 3) ∞ f U := by
    have he : (e.symm : RoundCylinderSpace → RoundCylinderSpace) = id := rfl
    have h := hf.comp e.symm.contMDiff.contMDiffOn
      (show MapsTo e.symm U U from by rw [he]; exact mapsTo_id _)
    simpa only [he, Function.comp_id] using h
  have hpull (x : RoundCylinderSpace) (hx : x ∈ U)
      (v : TangentSpace (𝓡 3) x) :
      g.inner (f x) (mfderiv (𝓡 3) (𝓡 3) f x v)
          (mfderiv (𝓡 3) (𝓡 3) f x v) =
        roundCylinderPullback g f x
          (mfderiv (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) e.symm x v)
          (mfderiv (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) e.symm x v) := by
    have hh := mfderiv_comp x
      ((hf.contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt (by simp))
      (e.symm.contMDiff.mdifferentiable (by simp) x)
    change mfderiv (𝓡 3) (𝓡 3) f x = _ at hh
    change g.inner _ _ _ = g.inner _ _ _
    rw [hh]
    rfl
  let C := Real.sqrt ((1 + ε) / Q)
  have hC : 0 < C := Real.sqrt_pos.mpr (by positivity)
  have hnorm (x : RoundCylinderSpace) (hx : x ∈ U)
      (v : TangentSpace (𝓡 3) x) :
      g.tangentNorm (f x) (mfderiv (𝓡 3) (𝓡 3) f x v) ≤
        C * roundCylinderMetric.tangentNorm x v := by
    have hb := roundCylinderClose_scaled_pullback_quadratic_error g f hε.le hclose hx.2
      (mfderiv (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) e.symm x v)
    rw [← roundCylinderMetric_inner_flat x v v, ← hpull x hx v] at hb
    have hinner : g.inner (f x) (mfderiv (𝓡 3) (𝓡 3) f x v)
          (mfderiv (𝓡 3) (𝓡 3) f x v) ≤ C ^ 2 * roundCylinderMetric.inner x v v := by
      rw [show C ^ 2 = (1 + ε) / Q from Real.sq_sqrt (by positivity),
        div_mul_eq_mul_div, le_div_iff₀ hQ]
      have h := (abs_le.mp hb).2
      nlinarith
    simpa only [RiemannianMetric.tangentNorm, Real.sqrt_mul (sq_nonneg C),
      Real.sqrt_sq hC.le] using Real.sqrt_le_sqrt hinner
  have htransport := roundCylinderMetric.intrinsicEDist_image_le_of_tangentNorm_le g
    hU (hflat.of_le (by simp)) (mapsTo_image f U) hC hnorm z w
  have hmodel : intrinsicEDist roundCylinderMetric U z w ≤
      ENNReal.ofReal (|w.2 - z.2| + Real.sqrt 2 * (Real.pi + 1)) := by
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 2) : UnitTwoSphere → Type _) :=
      ⟨(roundSphereMetric 2).toRiemannianMetric⟩
    have hdist : (roundSphereMetric 2).edist z.1 w.1 < ENNReal.ofReal (Real.pi + 1) := by
      rw [roundSphereMetric_edist_eq_angle (by norm_num : 1 ≤ 2)]
      apply ENNReal.ofReal_lt_ofReal_iff (by positivity) |>.mpr
      exact (Real.arccos_le_pi _).trans_lt (by linarith)
    obtain ⟨σ, h0, h1, hσ, hlen⟩ := Manifold.exists_lt_of_riemannianEDist_lt hdist
    let η : ℝ → RoundCylinderSpace := fun t => (σ t, z.2 + t * (w.2 - z.2))
    have hη := EpsilonNeck.model_path_smooth (z := z) (w := w) hσ
    have hpath : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 (e ∘ η) (Icc (0 : ℝ) 1) :=
      (e.contMDiff.of_le (by simp : (1 : ℕ∞ω) ≤ (∞ : ℕ∞ω))).comp_contMDiffOn hη
    have hend0 : (e ∘ η) 0 = z := by
      change (σ 0, z.2 + 0 * (w.2 - z.2)) = z
      simp [h0]
    have hend1 : (e ∘ η) 1 = w := by
      change (σ 1, z.2 + 1 * (w.2 - z.2)) = w
      simp [h1]
    apply roundCylinderMetric.intrinsicEDist_le_of_path hpath hend0 hend1
    · exact image_subset_iff.mpr (EpsilonNeck.model_path_mem hz hw)
    · have hh := EpsilonNeck.model_path_length_le (z := z) (w := w) hσ hlen.le
      rw [ENNReal.ofReal_add (abs_nonneg _) (by positivity)]
      simpa only [abs_sub_comm, add_comm] using hh
  exact (htransport.trans (mul_le_mul_right hmodel _)).trans_eq
    (ENNReal.ofReal_mul hC.le).symm

end PoincareConjecture
