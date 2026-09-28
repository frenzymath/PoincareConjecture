import PoincareConjecture.Proofs.M35.Thm12_28.NeckHomeomorph
import PoincareConjecture.Proofs.M35.Thm12_28.SliceNeckGeometry

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.StandardEvolvingNeck

open M35.OrdinaryRealization

private theorem scalar_scale_inv_sq {Q : ℝ} (hQ : 0 < Q) :
    (Q ^ (-1 / 2 : ℝ))⁻¹ ^ 2 = Q := by
  rw [← Real.rpow_neg hQ.le, ← Real.rpow_natCast, ← Real.rpow_mul hQ.le]
  norm_num

noncomputable def toGeneralizedStrongNeck (P : M35StandardCapPredecessors)
    {atlas : StandardCylinderAtlas} {g₀ : StandardInitialMetric}
    {F : MaximalStandardCapFlow g₀} {t epsilon : ℝ} {x : StandardCapSpace} {I : Set ℝ}
    (N : StandardEvolvingNeck atlas F t epsilon x I) (hretained : Ioc (-1 : ℝ) 0 ⊆ I) :
    GeneralizedStrongNeck (generalizedFlow F.base.flow) t epsilon := by
  let e := sliceDiffeomorph N.time_mem
  let U : Set (slice (Ico 0 F.base.lifetime) t).carrier := e ⁻¹' N.patch.carrier
  let Q := (F.connection t).scalarCurvature x
  let r := Q ^ (-1 / 2 : ℝ)
  have hQ : 0 < Q := N.scalar_pos
  have hr : 0 < r := Real.rpow_pos_of_pos hQ _
  have hsq : r⁻¹ ^ 2 = Q := scalar_scale_inv_sq hQ
  have hscalar : (connection F.base.flow t).scalarCurvature (e.symm x) = Q :=
    scalar_eq P F.base.flow N.time_mem x
  let c : NeckDomain epsilon ≃ₜ U := N.patch.coordinateHomeomorph.trans
    (e.symm.toHomeomorph.subtype (p := fun y => y ∈ N.patch.carrier)
      (q := fun y => y ∈ U) (fun y => Iff.rfl))
  let f : StandardCylinderSpace → (slice (Ico 0 F.base.lifetime) t).carrier :=
    fun z => e.symm (N.patch.coordinate z)
  have htime (s : ℝ) (hs : s ∈ Ioc (-1 : ℝ) 0) : t + s / r⁻¹ ^ 2 ∈
      Ico 0 F.base.lifetime := by
    rw [hsq]
    exact N.interval_survival s (hretained hs)
  let cyl := sliceCylinder F.base.flow N.time_mem (r⁻¹ ^ 2)
    (by rw [hsq]; exact hQ) (Ioc (-1 : ℝ) 0) U htime
  have hpull (s : ℝ) (hs : s ∈ Ioc (-1 : ℝ) 0) :
      generalizedCylinderPullback cyl f s =
        fun z v w => Q * roundCylinderPullback (F.metric (t + s / Q))
          N.patch.coordinate z v w := by
    have h := sliceCylinder_roundCylinderPullback F.base.flow N.time_mem (r⁻¹ ^ 2)
      (by rw [hsq]; exact hQ) (Ioc (-1 : ℝ) 0) U htime N.patch.coordinate s hs
    exact h.trans (by rw [hsq]; rfl)
  refine {
    epsilon_pos := N.epsilon_pos
    center := e.symm x
    scalar_center_pos := hscalar.symm ▸ hQ
    scale := r
    scale_pos := hr
    scale_scalar := congrArg (fun R : ℝ => R ^ (-1 / 2 : ℝ)) hscalar.symm
    carrier := U
    carrier_open := N.patch.carrier_open.preimage e.continuous
    coordinate := c
    coordinate_map := f
    coordinate_map_eq := fun _ => rfl
    coordinate_map_smooth := e.symm.contMDiff.comp_contMDiffOn N.patch.coordinate_smooth
    coordinate_inverse := N.patch.inverse ∘ e
    coordinate_inverse_mem := fun y hy => N.patch.inverse_domain (e y) hy
    coordinate_inverse_left := ?_
    coordinate_inverse_right := ?_
    coordinate_inverse_smooth := N.patch.inverse_smooth.comp e.contMDiff.contMDiffOn
      (fun _ hy => hy)
    central_sphere := f '' (univ ×ˢ ({0} : Set ℝ))
    central_sphere_eq := rfl
    center_on_central_sphere := ?_
    central_sphere_subset := ?_
    time_cylinder := cyl
    cylinder_identity := ?_
    metric_comparison := ?_
  }
  · intro z
    change N.patch.inverse (N.patch.coordinate (z.1, z.2.val)) = (z.1, z.2.val)
    exact N.patch.coordinate_left_inverse ⟨mem_univ _, z.2.property⟩
  · intro y hy
    change e.symm (N.patch.coordinate (N.patch.inverse (e y))) = y
    exact (congrArg e.symm (N.patch.coordinate_right_inverse hy)).trans
      (e.symm_apply_apply y)
  · obtain ⟨q, hq⟩ := N.patch.center_sphere
    refine ⟨(q, 0), ⟨mem_univ _, rfl⟩, ?_⟩
    exact congrArg e.symm hq
  · rintro y ⟨z, hz, rfl⟩
    change N.patch.coordinate z ∈ N.patch.carrier
    rw [← N.patch.coordinate_image]
    refine ⟨z, ⟨mem_univ _, ?_⟩, rfl⟩
    have hz0 : z.2 = 0 := hz.2
    rw [hz0]
    exact ⟨neg_lt_zero.mpr N.patch.length_pos, N.patch.length_pos⟩
  · intro h y _hy
    exact sliceCylinder_zero_identity F.base.flow N.time_mem (r⁻¹ ^ 2) _
      (Ioc (-1 : ℝ) 0) U htime h y
  · obtain ⟨hsmooth, b, hb, hjet⟩ := N.close
    refine ⟨?_, b, hb, ?_⟩
    · intro s hs
      exact (congrArg (RoundCylinderTensorSmoothOn epsilon) (hpull s hs)).mpr
        (hsmooth s (hretained hs))
    · intro s hs z hz
      exact (congrArg (fun B => roundCylinderJetErrorSquared s B ⌊epsilon⁻¹⌋₊ z ≤ b)
        (hpull s hs)).mpr (hjet s (hretained hs) z hz)

theorem generalized_canonical_control (P : M35StandardCapPredecessors)
    {atlas : StandardCylinderAtlas} {g₀ : StandardInitialMetric}
    {F : MaximalStandardCapFlow g₀} {t epsilon C : ℝ} {x : StandardCapSpace} {I : Set ℝ}
    (N : StandardEvolvingNeck atlas F t epsilon x I) (hretained : Ioc (-1 : ℝ) 0 ⊆ I) :
    GeneralizedCanonicalControl (F := generalizedFlow F.base.flow) t
      ((sliceDiffeomorph N.time_mem).symm x) epsilon C :=
  .neck (N.toGeneralizedStrongNeck P hretained) rfl

end PoincareConjecture.StandardEvolvingNeck
