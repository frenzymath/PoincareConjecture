import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.AsymptoticSoliton
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Rescaling.Geometry
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.Norm

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.AncientKappaSolution

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]

noncomputable def surfaceRescaling (K : AncientKappaSolution 2 M)
    (tau : ℝ) (htau : 0 < tau) : AncientRescaling K tau := by
  have hmap : MapsTo (fun s : ℝ => 0 + s / tau⁻¹) (Iio 0) (Iic 0) := by
    intro s hs
    simp only [zero_add, div_inv_eq_mul, mem_Iic]
    exact le_of_lt (mul_neg_of_neg_of_pos hs htau)
  have hne : (Iio (0 : ℝ)).Nontrivial :=
    ⟨-1, by norm_num, -2, by norm_num, by norm_num⟩
  let F := K.flow.parabolicRescale tau⁻¹ (inv_pos.mpr htau) 0 hmap
    (inferInstance : (Iio (0 : ℝ)).OrdConnected) hne
  have htime (t : ℝ) : 0 + t / tau⁻¹ = tau * t := by simp [mul_comm]
  refine {
    tau_pos := htau
    flow := F
    metric_scale := ?_
    ricci_scale := ?_
    scalar_scale := ?_
    curvature_norm_scale := ?_ }
  · intro t _ x v w
    simp only [F, RicciFlow.parabolicRescale, rescaledMetric_inner, htime, one_div]
  · intro t _ x v w
    have h :=
      K.flow.parabolicRescale_ricci tau⁻¹ (inv_pos.mpr htau) 0 hmap
        (inferInstance : (Iio (0 : ℝ)).OrdConnected) hne t x v w
    change (F.connection t).ricci x v w = _ at h
    rw [htime] at h
    exact h
  · intro t _ x
    have h :=
      K.flow.parabolicRescale_scalarCurvature tau⁻¹ (inv_pos.mpr htau) 0 hmap
        (inferInstance : (Iio (0 : ℝ)).OrdConnected) hne t x
    change (F.connection t).scalarCurvature x = _ at h
    rw [htime, inv_inv] at h
    exact h
  · intro t _ x
    rw [(F.connection t).curvatureTensorNorm_eq_abs_scalarCurvature,
      (K.flow.connection (tau * t)).curvatureTensorNorm_eq_abs_scalarCurvature]
    have hscalar := K.flow.parabolicRescale_scalarCurvature tau⁻¹ (inv_pos.mpr htau)
      0 hmap (inferInstance : (Iio (0 : ℝ)).OrdConnected) hne t x
    change (F.connection t).scalarCurvature x = _ at hscalar
    rw [hscalar, htime, inv_inv, abs_mul, abs_of_pos htau]

theorem exists_diverging_surfaceRescalings (K : AncientKappaSolution 2 M) :
    ∃ tau : ℕ → ℝ, (∀ k, 0 < tau k) ∧ Tendsto tau atTop atTop ∧
      ∀ k, Nonempty (AncientRescaling K (tau k)) := by
  refine ⟨fun k => (k : ℝ) + 1, fun k => by positivity, ?_, ?_⟩
  · exact tendsto_atTop_mono (fun k => le_add_of_nonneg_right zero_le_one)
      tendsto_natCast_atTop_atTop
  · intro k
    exact ⟨K.surfaceRescaling ((k : ℝ) + 1) (by positivity)⟩

end PoincareConjecture.AncientKappaSolution
