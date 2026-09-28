import PoincareConjecture.Proofs.M36.NeckCoordinates
import PoincareConjecture.Proofs.M12.Geometry.Riemannian.Curvature.LocalIsometryInvariants
import PoincareConjecture.Proofs.M34.Lemma12_3_Estimates.Regularity










set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.Proofs.M47

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M} {g0 : StandardInitialMetric}
  {K : MetricSurgeryConstants} {I : MetricSurgeryInput K g}



theorem retained_neck_scalar_eq (R : MetricSurgeryResult g0 I)
    {x : M} (hx : x ∈ I.neck.region (-I.neck.epsilon⁻¹) 0) :
    R.connection.scalarCurvature (R.collapse x) = I.neck.connection.scalarCurvature x := by
  have hsub : I.neck.region (-I.neck.epsilon⁻¹) 0 ⊆
      I.neck.region (-I.neck.epsilon⁻¹) 1 :=
    fun _ hy => ⟨hy.1, hy.2.1, hy.2.2.trans zero_lt_one⟩
  exact (I.neck.connection.scalarCurvature_eq_of_local_isometry R.connection
    (M36.neck_region_isOpen I.neck _ _) (R.retained_smooth.mono hsub)
    (fun y hy v w => (R.retained_metric y (Or.inl hy) v w).symm) hx).symm




theorem retained_central_coordinate_scalar_eq (R : MetricSurgeryResult g0 I)
    (q : UnitTwoSphere) :
    R.connection.scalarCurvature (R.collapse (I.neck.coordinate_map (q, 0))) =
      I.neck.connection.scalarCurvature (I.neck.coordinate_map (q, 0)) := by
  let N := I.neck
  have hinv : (1 : ℝ) < N.epsilon⁻¹ := by
    rw [inv_eq_one_div]
    apply (lt_div_iff₀ N.epsilon_pos).mpr
    linarith [N.epsilon_lt_half]
  let gamma : ℝ → M := fun s => N.coordinate_map (q, s)
  have hcoords (s : ℝ) (hs : s ∈ Icc (-1 : ℝ) 0) :
      (q, s) ∈ univ ×ˢ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ :=
    ⟨mem_univ _, by constructor <;> linarith [hs.1, hs.2]⟩
  have hgamma : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) ∞ gamma (Icc (-1) 0) :=
    N.coordinate_map_smooth.comp (contMDiff_const.prodMk contMDiff_id).contMDiffOn hcoords
  have hregion (s : ℝ) (hs : s ∈ Icc (-1 : ℝ) 0) :
      gamma s ∈ N.region (-N.epsilon⁻¹) 1 := by
    refine ⟨M36.neck_coordinate_mem N _ (hcoords s hs), ?_, ?_⟩
    · rw [M36.neck_inverse_coordinate N _ (hcoords s hs)]
      exact (hcoords s hs).2.1
    · rw [M36.neck_inverse_coordinate N _ (hcoords s hs)]
      exact hs.2.trans_lt zero_lt_one
  have hpost : ContinuousOn (fun s => R.connection.scalarCurvature (R.collapse (gamma s)))
      (Icc (-1 : ℝ) 0) :=
    (M34.contMDiff_scalarCurvature R.connection).continuous.comp_continuousOn
      (R.retained_smooth.continuousOn.comp hgamma.continuousOn hregion)
  have hpre : ContinuousOn (fun s => N.connection.scalarCurvature (gamma s))
      (Icc (-1 : ℝ) 0) :=
    (M34.contMDiff_scalarCurvature N.connection).continuous.comp_continuousOn hgamma.continuousOn
  have heq : EqOn (fun s => R.connection.scalarCurvature (R.collapse (gamma s)))
      (fun s => N.connection.scalarCurvature (gamma s)) (Ioo (-1 : ℝ) 0) := by
    intro s hs
    apply retained_neck_scalar_eq R
    refine ⟨(hregion s ⟨hs.1.le, hs.2.le⟩).1,
      (hregion s ⟨hs.1.le, hs.2.le⟩).2.1, ?_⟩
    rw [M36.neck_inverse_coordinate N _ (hcoords s ⟨hs.1.le, hs.2.le⟩)]
    exact hs.2
  exact heq.of_subset_closure hpost hpre Ioo_subset_Icc_self
    (by rw [closure_Ioo (by norm_num : (-1 : ℝ) ≠ 0)]) (by norm_num : (0 : ℝ) ∈ Icc (-1) 0)



theorem retained_neck_center_scalar (R : MetricSurgeryResult g0 I) :
    R.connection.scalarCurvature (R.collapse I.neck.center) = I.neck.scale⁻¹ ^ 2 := by
  obtain ⟨⟨q, z⟩, ⟨_, hz⟩, hq⟩ :=
    I.neck.central_sphere_eq ▸ I.neck.center_on_central_sphere
  have hz0 : z = 0 := hz
  subst z
  have h := retained_central_coordinate_scalar_eq R q
  rw [hq] at h
  rw [h, I.neck.scale_eq_scalar, inv_pow,
    ← Real.rpow_mul_natCast I.neck.scalar_center_pos.le (-1 / 2) 2]
  norm_num [Real.rpow_neg_one]

end PoincareConjecture.Proofs.M47
