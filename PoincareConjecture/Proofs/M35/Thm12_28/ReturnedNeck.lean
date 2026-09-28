import PoincareConjecture.Proofs.M35.Thm12_28.CylinderMetricRigidity
import PoincareConjecture.Proofs.M35.Thm12_28.CylinderLocality

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.M35.OrdinaryRealization

noncomputable def standardPatchOfGeneralizedNeck {g₀ : StandardInitialMetric}
    {F : MaximalStandardCapFlow g₀} {t epsilon : ℝ}
    (N : GeneralizedStrongNeck (generalizedFlow F.base.flow) t epsilon) :
    StandardCylinderPatch epsilon⁻¹ N.center.val := by
  have ht : t ∈ Ico 0 F.base.lifetime := N.center.property
  let e := sliceDiffeomorph ht
  refine {
    length_pos := inv_pos.mpr N.epsilon_pos
    carrier := e.symm ⁻¹' N.carrier
    carrier_open := N.carrier_open.preimage e.symm.continuous
    coordinate := e ∘ N.coordinate_map
    inverse := N.coordinate_inverse ∘ e.symm
    coordinate_image := ?_
    coordinate_left_inverse := ?_
    coordinate_right_inverse := ?_
    inverse_domain := fun x hx => N.coordinate_inverse_mem (e.symm x) hx
    coordinate_smooth := e.contMDiff.comp_contMDiffOn N.coordinate_map_smooth
    inverse_smooth := N.coordinate_inverse_smooth.comp e.symm.contMDiff.contMDiffOn
      (fun _ hx => hx)
    center_sphere := ?_
  }
  · apply Subset.antisymm
    · rintro x ⟨z, hz, rfl⟩
      have hm : N.coordinate_map z ∈ N.carrier :=
        (N.coordinate_map_eq (z.1, ⟨z.2, hz.2⟩)) ▸
          (N.coordinate (z.1, ⟨z.2, hz.2⟩)).property
      exact (congrArg (fun y => y ∈ N.carrier)
        (e.symm_apply_apply (N.coordinate_map z))).mpr hm
    · intro x hx
      refine ⟨N.coordinate_inverse (e.symm x),
        ⟨mem_univ _, N.coordinate_inverse_mem (e.symm x) hx⟩, ?_⟩
      exact (congrArg e (N.coordinate_inverse_right (e.symm x) hx)).trans
        (e.apply_symm_apply x)
  · intro z hz
    exact (congrArg N.coordinate_inverse (e.symm_apply_apply (N.coordinate_map z))).trans
      ((congrArg N.coordinate_inverse
      (N.coordinate_map_eq (z.1, ⟨z.2, hz.2⟩)).symm).trans
        (N.coordinate_inverse_left (z.1, ⟨z.2, hz.2⟩)))
  · intro x hx
    exact (congrArg e (N.coordinate_inverse_right (e.symm x) hx)).trans
      (e.apply_symm_apply x)
  · have hc := N.center_on_central_sphere
    rw [N.central_sphere_eq] at hc
    obtain ⟨z, hz, hcenter⟩ := hc
    have hz0 : z.2 = 0 := hz.2
    refine ⟨z.1, ?_⟩
    exact (congrArg (fun s : ℝ => e (N.coordinate_map (z.1, s))) hz0.symm).trans
      (congrArg e hcenter)

noncomputable def standardNeckOfGeneralizedNeck (P : M35StandardCapPredecessors)
    (atlas : StandardCylinderAtlas) {g₀ : StandardInitialMetric}
    {F : MaximalStandardCapFlow g₀} {t epsilon : ℝ}
    (N : GeneralizedStrongNeck (generalizedFlow F.base.flow) t epsilon)
    (he : epsilon < 1 / 2) :
    StandardEvolvingNeck atlas F t epsilon N.center.val (Ioc (-1 : ℝ) 0) := by
  let Q := (F.connection t).scalarCurvature N.center.val
  have hscalar : ((generalizedFlow F.base.flow).connection t).scalarCurvature N.center = Q :=
    scalar_eq P F.base.flow N.center.property N.center.val
  have hQ : 0 < Q := N.scalar_center_pos.trans_eq hscalar
  have hscale : N.scale⁻¹ ^ 2 = Q := by
    calc
      _ = (((generalizedFlow F.base.flow).connection t).scalarCurvature
          N.center ^ (-1 / 2 : ℝ))⁻¹ ^ 2 :=
        congrArg (fun r : ℝ => r⁻¹ ^ 2) N.scale_scalar
      _ = Q := by
        rw [hscalar, ← Real.rpow_neg hQ.le, ← Real.rpow_natCast,
          ← Real.rpow_mul hQ.le]
        norm_num
  have ht : t ∈ Ico 0 F.base.lifetime := N.center.property
  let e := sliceDiffeomorph ht
  have hzero : (0 : ℝ) ∈ Ioc (-1 : ℝ) 0 := by norm_num
  have hmem (z : StandardCylinderSpace) (hz : z.2 ∈ Ioo (-epsilon⁻¹) epsilon⁻¹) :
      N.coordinate_map z ∈ N.carrier :=
    (N.coordinate_map_eq (z.1, ⟨z.2, hz⟩)) ▸ (N.coordinate (z.1, ⟨z.2, hz⟩)).property
  refine {
    time_mem := N.center.property
    epsilon_pos := N.epsilon_pos
    epsilon_lt_half := he
    scalar_pos := hQ
    patch := standardPatchOfGeneralizedNeck N
    interval_survival := ?_
    close := ?_
  }
  · intro u hu
    have h := (N.time_cylinder.forward u hu N.center).property
    change t + u / N.scale⁻¹ ^ 2 ∈ Ico 0 F.base.lifetime at h
    rwa [hscale] at h
  · apply cylinder_family_congr _ N.metric_comparison
    intro u hu z hz v w
    unfold generalizedCylinderPullback
    rw [dif_pos hu]
    have hp := cylinder_pullbackInner_eq F.base.flow N.time_cylinder isPreconnected_Ioc
      N.carrier_open hzero (fun y hy => N.cylinder_identity hzero y hy) hu (hmem z hz)
      (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) N.coordinate_map z v)
      (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) N.coordinate_map z w)
    refine hp.trans ?_
    have hd (v : TangentSpace ((𝓡 2).prod 𝓘(ℝ, ℝ)) z) :
        mfderiv (𝓡 3) (𝓡 3) e (N.coordinate_map z)
            (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) N.coordinate_map z v) =
          mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) (e ∘ N.coordinate_map) z v :=
      (congrArg (fun L => L v) (e.mfderiv_comp (by simp) N.coordinate_map z)).symm
    change N.scale⁻¹ ^ 2 * (F.metric (t + u / N.scale⁻¹ ^ 2)).inner
      (e (N.coordinate_map z))
      (mfderiv (𝓡 3) (𝓡 3) e (N.coordinate_map z)
        (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) N.coordinate_map z v))
      (mfderiv (𝓡 3) (𝓡 3) e (N.coordinate_map z)
        (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) N.coordinate_map z w)) = _
    rw [hd v, hd w, hscale]
    rfl

end PoincareConjecture.M35.OrdinaryRealization
