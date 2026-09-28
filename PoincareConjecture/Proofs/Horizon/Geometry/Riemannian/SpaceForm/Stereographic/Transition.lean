import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.SpaceForm.Stereographic.Metric
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.TransitionBounds
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Composition

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Set Filter
open scoped Manifold ContDiff Topology InnerProductSpace

namespace Poincare.Geometry.Riemannian.SpaceForm

theorem sphere_chart_target {n : ℕ} (q : UnitSphere n) :
    (chartAt (EuclideanSpace ℝ (Fin n)) q).target = univ := by
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) := ⟨by simp⟩
  exact stereographic'_target (-q)

theorem sphere_chart_symm_contMDiff {n : ℕ} (q : UnitSphere n) :
    ContMDiff (𝓡 n) (𝓡 n) ∞ (chartAt (EuclideanSpace ℝ (Fin n)) q).symm := by
  have h := contMDiffOn_chart_symm (I := 𝓡 n) (x := q) (n := (∞ : ℕ∞ω))
  rw [sphere_chart_target q] at h
  exact contMDiffOn_univ.mp h

theorem sphere_chart_center {n : ℕ} (q : UnitSphere n) :
    chartAt (EuclideanSpace ℝ (Fin n)) q q = 0 := by
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) := ⟨by simp⟩
  change (stereographic' n (-q)) q = 0
  simp only [stereographic', OpenPartialHomeomorph.trans_apply]
  rw [stereographic_neg_apply]
  simp

theorem sphere_chart_symm_zero {n : ℕ} (q : UnitSphere n) :
    (chartAt (EuclideanSpace ℝ (Fin n)) q).symm 0 = q := by
  rw [← sphere_chart_center q]
  exact (chartAt (EuclideanSpace ℝ (Fin n)) q).left_inv (mem_chart_source _ _)

theorem sphere_chart_symm_lipschitz {n : ℕ} (q : UnitSphere n) :
    LipschitzWith 1 (fun x : EuclideanSpace ℝ (Fin n) =>
      ((chartAt (EuclideanSpace ℝ (Fin n)) q).symm x : EuclideanSpace ℝ (Fin (n + 1)))) := by
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) := ⟨by simp⟩
  let c := chartAt (EuclideanSpace ℝ (Fin n)) q
  let f : UnitSphere n → EuclideanSpace ℝ (Fin (n + 1)) := Subtype.val
  have hc := sphere_chart_symm_contMDiff q
  have hf : ContMDiff (𝓡 n) (𝓡 (n + 1)) ∞ f := contMDiff_coe_sphere
  have hsmooth : ContDiff ℝ ∞ (f ∘ c.symm) :=
    contMDiff_iff_contDiff.mp (hf.comp hc)
  apply lipschitzWith_of_nnnorm_fderiv_le (hsmooth.differentiable (by simp))
  intro x
  change ‖fderiv ℝ (f ∘ c.symm) x‖ ≤ (1 : ℝ)
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro v
  have hder : fderiv ℝ (f ∘ c.symm) x =
      (mfderiv (𝓡 n) (𝓡 (n + 1)) f (c.symm x)).comp
        (mfderiv (𝓡 n) (𝓡 n) c.symm x) := by
    rw [← mfderiv_eq_fderiv]
    exact mfderiv_comp x (hf (c.symm x) |>.mdifferentiableAt (by simp))
      (hc x |>.mdifferentiableAt (by simp))
  have h := (roundSphere_chart_quadratic_bounds q (x := x) le_rfl v).2
  change (roundSphereMetric n).inner (c.symm x)
    (mfderiv (𝓡 n) (𝓡 n) c.symm x v)
    (mfderiv (𝓡 n) (𝓡 n) c.symm x v) ≤ ‖v‖ ^ 2 at h
  rw [roundSphereMetric_inner, PoincareConjecture.RiemannianMetric.euclideanMetric_inner] at h
  have hsq : ‖fderiv ℝ (f ∘ c.symm) x v‖ ^ 2 ≤ ‖v‖ ^ 2 := by
    rw [hder]
    change (@norm (EuclideanSpace ℝ (Fin (n + 1))) _
      ((mfderiv (𝓡 n) (𝓡 (n + 1)) f (c.symm x))
        ((mfderiv (𝓡 n) (𝓡 n) c.symm x) v))) ^ 2 ≤ ‖v‖ ^ 2
    simpa only [real_inner_self_eq_norm_sq] using h
  simpa only [one_mul] using
    (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

theorem norm_sphere_chart_symm_sub_center_le {n : ℕ} (q : UnitSphere n)
    (x : EuclideanSpace ℝ (Fin n)) :
    ‖((chartAt (EuclideanSpace ℝ (Fin n)) q).symm x : EuclideanSpace ℝ (Fin (n + 1))) - q‖ ≤ ‖x‖ := by
  have h := (sphere_chart_symm_lipschitz q).dist_le_mul x 0
  simpa only [sphere_chart_symm_zero, dist_eq_norm, sub_zero, NNReal.coe_one, one_mul] using h

theorem sphere_mem_chart_source_of_nonneg_inner {n : ℕ} (p z : UnitSphere n)
    (h : 0 ≤ ⟪(p : EuclideanSpace ℝ (Fin (n + 1))), z⟫_ℝ) :
    z ∈ (chartAt (EuclideanSpace ℝ (Fin n)) p).source := by
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) := ⟨by simp⟩
  change z ∈ (stereographic' n (-p)).source
  rw [stereographic'_source]
  intro heq
  have hz : z = -p := mem_singleton_iff.mp heq
  subst z
  have hp := norm_eq_of_mem_sphere p
  change 0 ≤ ⟪(p : EuclideanSpace ℝ (Fin (n + 1))), -(p : EuclideanSpace ℝ (Fin (n + 1)))⟫_ℝ at h
  simp only [inner_neg_right, real_inner_self_eq_norm_sq, hp] at h
  norm_num at h

theorem norm_sphere_chart_le_two_of_nonneg_inner {n : ℕ} (p z : UnitSphere n)
    (h : 0 ≤ ⟪(p : EuclideanSpace ℝ (Fin (n + 1))), z⟫_ℝ) :
    ‖chartAt (EuclideanSpace ℝ (Fin n)) p z‖ ≤ 2 := by
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) := ⟨by simp⟩
  change ‖(stereographic' n (-p)) z‖ ≤ 2
  let v : EuclideanSpace ℝ (Fin (n + 1)) := -p
  let U : (ℝ ∙ v)ᗮ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n) :=
    (OrthonormalBasis.fromOrthogonalSpanSingleton n
    (ne_zero_of_mem_unit_sphere (-p))).repr
  change ‖U (stereoToFun v (z : EuclideanSpace ℝ (Fin (n + 1))))‖ ≤ 2
  rw [U.norm_map, stereoToFun_apply, norm_smul]
  have hproj : ‖(ℝ ∙ v)ᗮ.orthogonalProjectionOnto (z : EuclideanSpace ℝ (Fin (n + 1)))‖ ≤ 1 := by
    simpa only [norm_eq_of_mem_sphere z] using
      (ℝ ∙ v)ᗮ.norm_orthogonalProjectionOnto_apply_le (z : EuclideanSpace ℝ (Fin (n + 1)))
  have hden : 1 ≤ 1 - innerSL ℝ v (z : EuclideanSpace ℝ (Fin (n + 1))) := by
    change 1 ≤ 1 - ⟪-(p : EuclideanSpace ℝ (Fin (n + 1))), z⟫_ℝ
    rw [inner_neg_left]
    linarith
  have hc : ‖2 / (1 - innerSL ℝ v (z : EuclideanSpace ℝ (Fin (n + 1))))‖ ≤ 2 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    apply (div_le_iff₀ (by linarith)).mpr
    linarith
  exact (mul_le_mul_of_nonneg_left hproj (norm_nonneg _)).trans
    ((mul_one _).le.trans hc)

theorem sphere_chart_transition_mapsTo_ball {n : ℕ} (p q : UnitSphere n)
    (hpq : ‖(q : EuclideanSpace ℝ (Fin (n + 1))) - p‖ < 1 / 2) :
    ∀ x ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (1 / 2),
      (chartAt (EuclideanSpace ℝ (Fin n)) q).symm x ∈
          (chartAt (EuclideanSpace ℝ (Fin n)) p).source ∧
        (chartAt (EuclideanSpace ℝ (Fin n)) p)
          ((chartAt (EuclideanSpace ℝ (Fin n)) q).symm x) ∈
            Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 3 := by
  intro x hx
  have hx' : ‖x‖ < 1 / 2 := by simpa only [Metric.mem_ball, dist_zero_right] using hx
  let z := (chartAt (EuclideanSpace ℝ (Fin n)) q).symm x
  have hdist : ‖(z : EuclideanSpace ℝ (Fin (n + 1))) - p‖ < 1 := by
    have h := (norm_sub_le_norm_sub_add_norm_sub (z : EuclideanSpace ℝ (Fin (n + 1))) q p).trans
      (add_le_add (norm_sphere_chart_symm_sub_center_le q x) le_rfl)
    linarith
  have hinner : 0 ≤ ⟪(p : EuclideanSpace ℝ (Fin (n + 1))), z⟫_ℝ := by
    have h := real_inner_le_norm (p : EuclideanSpace ℝ (Fin (n + 1))) (p - z)
    rw [inner_sub_right, real_inner_self_eq_norm_sq, norm_eq_of_mem_sphere p,
      norm_sub_rev] at h
    nlinarith
  exact ⟨sphere_mem_chart_source_of_nonneg_inner p z hinner, by
    rw [Metric.mem_ball, dist_zero_right]
    exact (norm_sphere_chart_le_two_of_nonneg_inner p z hinner).trans_lt (by norm_num)⟩

theorem contDiffOn_sphere_chart_transition {n : ℕ} (p q : UnitSphere n)
    (hpq : ‖(q : EuclideanSpace ℝ (Fin (n + 1))) - p‖ < 1 / 2) :
    ContDiffOn ℝ ∞
      ((chartAt (EuclideanSpace ℝ (Fin n)) p) ∘
        (chartAt (EuclideanSpace ℝ (Fin n)) q).symm)
      (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (1 / 2)) := by
  apply contMDiffOn_iff_contDiffOn.mp
  exact (contMDiffOn_chart (I := 𝓡 n) (x := p)).comp
    (sphere_chart_symm_contMDiff q).contMDiffOn
    (fun x hx => (sphere_chart_transition_mapsTo_ball p q hpq x hx).1)

theorem sphere_chart_transition_metric {n : ℕ} (p q : UnitSphere n)
    (hpq : ‖(q : EuclideanSpace ℝ (Fin (n + 1))) - p‖ < 1 / 2)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ Metric.ball 0 (1 / 2))
    (v w : EuclideanSpace ℝ (Fin n)) :
    let cp := chartAt (EuclideanSpace ℝ (Fin n)) p
    let cq := chartAt (EuclideanSpace ℝ (Fin n)) q
    let f := cp ∘ cq.symm
    (roundSphereMetric n).pullbackCoefficients cp.symm (f x)
        (fderiv ℝ f x v) (fderiv ℝ f x w) =
      (roundSphereMetric n).pullbackCoefficients cq.symm x v w := by
  let cp := chartAt (EuclideanSpace ℝ (Fin n)) p
  let cq := chartAt (EuclideanSpace ℝ (Fin n)) q
  let f := cp ∘ cq.symm
  change (roundSphereMetric n).pullbackCoefficients cp.symm (f x)
      (fderiv ℝ f x v) (fderiv ℝ f x w) =
    (roundSphereMetric n).pullbackCoefficients cq.symm x v w
  have hf : DifferentiableAt ℝ f x :=
    ((contDiffOn_sphere_chart_transition p q hpq).contDiffAt
      (Metric.isOpen_ball.mem_nhds hx)).differentiableAt (by simp)
  have heq : cp.symm ∘ f =ᶠ[𝓝 x] cq.symm := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hx] with y hy
    exact cp.left_inv (sphere_chart_transition_mapsTo_ball p q hpq y hy).1
  exact (roundSphereMetric n).pullbackCoefficients_comp_of_eventuallyEq
    ((sphere_chart_symm_contMDiff p (f x)).mdifferentiableAt (by simp)) hf heq v w

theorem exists_uniform_sphere_chart_transition_jet_bound {n : ℕ}
    (p : UnitSphere n) (q : ℕ → UnitSphere n)
    (hpq : ∀ i, ‖(q i : EuclideanSpace ℝ (Fin (n + 1))) - p‖ < 1 / 2)
    (j : ℕ) :
    ∃ B : ℝ, ∀ i x, x ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (1 / 2) →
      ‖iteratedFDeriv ℝ j
        ((chartAt (EuclideanSpace ℝ (Fin n)) p) ∘
          (chartAt (EuclideanSpace ℝ (Fin n)) (q i)).symm) x‖ ≤ B := by
  let A := fun i => (roundSphereMetric n).pullbackCoefficients
    (chartAt (EuclideanSpace ℝ (Fin n)) (q i)).symm
  let B := fun _ : ℕ => (roundSphereMetric n).pullbackCoefficients
    (chartAt (EuclideanSpace ℝ (Fin n)) p).symm
  have hs (z : UnitSphere n) : ContDiff ℝ ∞
      ((roundSphereMetric n).pullbackCoefficients
        (chartAt (EuclideanSpace ℝ (Fin n)) z).symm) := by
    apply contDiff_iff_contDiffAt.mpr
    intro x
    exact (roundSphereMetric n).contDiffAt_pullbackCoefficients (sphere_chart_symm_contMDiff z x)
  apply PoincareConjecture.CoordinateTransition.uniform_derivative_bounds_of_local_isometries
    (d := n) (U := Metric.ball 0 (1 / 2)) (V := Metric.ball 0 3)
    (f := fun i => (chartAt (EuclideanSpace ℝ (Fin n)) p) ∘
      (chartAt (EuclideanSpace ℝ (Fin n)) (q i)).symm)
    (A := A) (B := B) Metric.isOpen_ball Metric.isOpen_ball Metric.isBounded_ball
    (fun i => (hs (q i)).contDiffOn) (fun _ => (hs p).contDiffOn)
    (fun i => contDiffOn_sphere_chart_transition p (q i) (hpq i))
    (by
      intro i x _ v w
      change (roundSphereMetric n).pullbackCoefficients
        (chartAt (EuclideanSpace ℝ (Fin n)) (q i)).symm x v w =
        (roundSphereMetric n).pullbackCoefficients
          (chartAt (EuclideanSpace ℝ (Fin n)) (q i)).symm x w v
      rw [roundSphereMetric_pullbackCoefficients_chart]
      change _ * ⟪v, w⟫_ℝ = _ * ⟪w, v⟫_ℝ
      rw [real_inner_comm v w])
    (by
      intro i x _ v w
      change (roundSphereMetric n).pullbackCoefficients
        (chartAt (EuclideanSpace ℝ (Fin n)) p).symm x v w =
        (roundSphereMetric n).pullbackCoefficients
          (chartAt (EuclideanSpace ℝ (Fin n)) p).symm x w v
      rw [roundSphereMetric_pullbackCoefficients_chart]
      change _ * ⟪v, w⟫_ℝ = _ * ⟪w, v⟫_ℝ
      rw [real_inner_comm v w])
    (a := 16 / (3 ^ 2 + 4) ^ 2) (by norm_num)
    (fun i x hx v => (roundSphere_chart_quadratic_bounds (q i) (r := 3)
      (by have hh : ‖x‖ < 1 / 2 := by simpa only [Metric.mem_ball, dist_zero_right] using hx
          linarith) v).1)
    (fun i x hx v => (roundSphere_chart_quadratic_bounds p (r := 3)
      (show ‖x‖ ≤ 3 from
        (show ‖x‖ < 3 from by simpa only [Metric.mem_ball, dist_zero_right] using hx).le) v).1)
    (fun m => ?_)
    (fun i x hx => (sphere_chart_transition_mapsTo_ball p (q i) (hpq i) x hx).2)
    (fun i x hx v w => sphere_chart_transition_metric p (q i) (hpq i) hx v w) j
  obtain ⟨C, _, hC⟩ := exists_uniform_roundSphere_chart_jet_bound n m 3
  refine ⟨C, ?_, ?_⟩
  · intro i x hx
    exact hC (q i) x (by
      have hh : ‖x‖ < 1 / 2 := by simpa only [Metric.mem_ball, dist_zero_right] using hx
      linarith)
  · intro i x hx
    apply hC p x
    exact (show ‖x‖ < 3 from by simpa only [Metric.mem_ball, dist_zero_right] using hx).le

end Poincare.Geometry.Riemannian.SpaceForm
