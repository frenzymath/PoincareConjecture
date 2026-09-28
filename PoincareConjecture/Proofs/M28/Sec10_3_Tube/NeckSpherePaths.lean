import PoincareConjecture.Proofs.M28.Sec10_3_Tube.StandardSpherePaths
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.NeckLengthComparison
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.MetricComparison

set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology ENNReal Bundle InnerProductSpace

universe u

namespace PoincareConjecture.M28

open Proofs.M28.NeckLengthComparison

set_option backward.isDefEq.respectTransparency false in

theorem standardSphereMetric_tangentNorm_eq_norm (q : UnitTwoSphere)
    (v : EuclideanSpace ℝ (Fin 2)) :
    standardSphereMetric.tangentNorm q v = ‖v‖ := by
  calc
    _ = ‖mfderiv (𝓡 2) (𝓡 3) (fun x : UnitTwoSphere => x.1) q v‖ :=
      standardSphereMetric_tangentNorm q v
    _ = ‖v‖ := by
      rw [norm_eq_sqrt_real_inner, sphere_inclusion_inner,
        real_inner_self_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] {g : RiemannianMetric 3 M}

set_option backward.isDefEq.respectTransparency false in

theorem coordinate_sphere_pathELength_le (N : EpsilonNeck g)
    {γ : ℝ → UnitTwoSphere} (hγ : ContMDiff 𝓘(ℝ, ℝ) (𝓡 2) 1 γ)
    {s : ℝ} (hs : s ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) (a b : ℝ) :
    g.pathELength (fun t => N.coordinate_map (γ t, s)) a b ≤
      ENNReal.ofReal (4 * N.scale) * standardSphereMetric.pathELength γ a b := by
  have hderiv (t : ℝ) :
      mfderiv 𝓘(ℝ, ℝ) (𝓡 3) (fun t => N.coordinate_map (γ t, s)) t 1 =
        mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) N.coordinate_map (γ t, s)
          (mfderiv 𝓘(ℝ, ℝ) (𝓡 2) γ t 1, 0) := by
    have hcoord : MDifferentiableAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3)
        N.coordinate_map (γ t, s) :=
      ((N.coordinate_map_smooth (γ t, s) ⟨mem_univ _, hs⟩).contMDiffAt
        ((isOpen_univ.prod isOpen_Ioo).mem_nhds ⟨mem_univ _, hs⟩)).mdifferentiableAt
          (by simp)
    have hγt : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 2) γ t :=
      hγ.contMDiffAt.mdifferentiableAt one_ne_zero
    change mfderiv 𝓘(ℝ, ℝ) (𝓡 3)
      (N.coordinate_map ∘ fun t => (γ t, s)) t 1 = _
    rw [mfderiv_comp t hcoord (hγt.prodMk mdifferentiableAt_const),
      mfderiv_prodMk hγt mdifferentiableAt_const, mfderiv_const]
    rfl
  rw [g.pathELength_eq_lintegral_tangentNorm,
    standardSphereMetric.pathELength_eq_lintegral_tangentNorm,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply setLIntegral_mono' measurableSet_Icc
  intro t _
  rw [hderiv]
  have hspeed := N.coordinate_sphere_speed_upper (γ t, s) hs
    (mfderiv 𝓘(ℝ, ℝ) (𝓡 2) γ t 1)
  have hnorm := standardSphereMetric_tangentNorm_eq_norm (γ t)
    (mfderiv 𝓘(ℝ, ℝ) (𝓡 2) γ t 1 : EuclideanSpace ℝ (Fin 2))
  have hspeed' := hspeed.trans_eq
    (congrArg (fun r : ℝ => 4 * N.scale * r) hnorm.symm)
  exact (ENNReal.ofReal_le_ofReal hspeed').trans_eq
    (ENNReal.ofReal_mul (mul_nonneg (by norm_num) N.scale_pos.le))

theorem exists_central_sphere_shortcut (N : EpsilonNeck g) {x y : M}
    (hx : x ∈ N.central_sphere) (hy : y ∈ N.central_sphere) :
    ∃ σ : ℝ → M, σ 0 = x ∧ σ 1 = y ∧
      ContMDiff 𝓘(ℝ, ℝ) (𝓡 3) 1 σ ∧ MapsTo σ univ N.central_sphere ∧
      g.pathELength σ 0 1 <
        ENNReal.ofReal ((4 * standardSpherePathCeiling) * N.scale) ∧
      σ =ᶠ[𝓝 (0 : ℝ)] (fun _ => x) ∧ σ =ᶠ[𝓝 (1 : ℝ)] (fun _ => y) := by
  rw [N.central_sphere_eq] at hx hy
  obtain ⟨⟨p, s⟩, ⟨_, hs⟩, hpx⟩ := hx
  obtain ⟨⟨q, t⟩, ⟨_, ht⟩, hqy⟩ := hy
  have hs0 : s = 0 := hs
  have ht0 : t = 0 := ht
  subst s
  subst t
  obtain ⟨γ, hγ0, hγ1, hγ, hγlen, hγnear0, hγnear1⟩ :=
    exists_standardSphere_short_path p q
  have hzero : (0 : ℝ) ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ :=
    ⟨neg_neg_of_pos (inv_pos.mpr N.epsilon_pos), inv_pos.mpr N.epsilon_pos⟩
  let σ : ℝ → M := fun u => N.coordinate_map (γ u, 0)
  have hσ : ContMDiff 𝓘(ℝ, ℝ) (𝓡 3) 1 σ := by
    rw [← contMDiffOn_univ]
    apply (N.coordinate_map_smooth.of_le (by simp)).comp
    · exact (hγ.prodMk contMDiff_const).contMDiffOn
    · intro u _
      exact ⟨mem_univ _, hzero⟩
  refine ⟨σ, by simpa [σ, hγ0] using hpx, by simpa [σ, hγ1] using hqy,
    hσ, ?_, ?_, ?_, ?_⟩
  · intro u _
    rw [N.central_sphere_eq]
    exact ⟨(γ u, 0), ⟨mem_univ _, rfl⟩, rfl⟩
  · have hscale : 0 < 4 * N.scale := mul_pos (by norm_num) N.scale_pos
    have hbound := (coordinate_sphere_pathELength_le N hγ hzero 0 1).trans_lt
      (ENNReal.mul_lt_mul_right (ne_of_gt (ENNReal.ofReal_pos.mpr hscale))
        ENNReal.ofReal_ne_top hγlen)
    convert hbound using 1
    rw [← ENNReal.ofReal_mul hscale.le]
    congr 1
    ring
  · filter_upwards [hγnear0] with u hu
    change N.coordinate_map (γ u, 0) = x
    rw [hu]
    exact hpx
  · filter_upwards [hγnear1] with u hu
    change N.coordinate_map (γ u, 0) = y
    rw [hu]
    exact hqy

end PoincareConjecture.M28
