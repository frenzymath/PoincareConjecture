import PoincareConjecture.Proofs.M28.Sec10_3_Tube.NeckCenterConnector
import PoincareConjecture.Proofs.M28.Prop9_79_Persistence.CapTopology.NeckCollar

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology ENNReal Bundle

universe u

namespace PoincareConjecture.M28

open Proofs.M28.NeckLengthComparison

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] {g : RiemannianMetric 3 M}

set_option backward.isDefEq.respectTransparency false in

theorem exists_neck_region_center_connector (N : EpsilonNeck g)
    {a b : ℝ} (ha : a < 0) (hb : 0 < b) {p : M}
    (hp : p ∈ N.region a b) :
    ∃ γ : ℝ → M, γ 0 = p ∧ γ 1 = N.center ∧
      ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 γ (Icc (0 : ℝ) 1) ∧
      MapsTo γ (Icc (0 : ℝ) 1) (N.region a b) ∧
      g.pathELength γ 0 1 < ENNReal.ofReal
        ((2 * N.epsilon⁻¹ + 4 * standardSpherePathCeiling) * N.scale) := by
  have hscale : 0 < N.scale := N.scale_pos
  have hinv : 0 < N.epsilon⁻¹ := inv_pos.mpr N.epsilon_pos
  have hL : 0 < standardSpherePathCeiling := standardSpherePathCeiling_pos
  let q : UnitTwoSphere := (N.coordinate_inverse p).1
  let s : ℝ := (N.coordinate_inverse p).2
  have hs : s ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ :=
    (N.coordinate_inverse_mem p hp.1).2
  have hsabs : |s| < N.epsilon⁻¹ := abs_lt.mpr hs
  let η : ℝ → RoundCylinderSpace := fun t => (q, (1 - t) * s)
  let α : ℝ → M := N.coordinate_map ∘ η
  have hscalar : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) 1
      (fun t : ℝ => (1 - t) * s) := by
    rw [contMDiff_iff_contDiff]
    fun_prop
  have hη : ContMDiff 𝓘(ℝ, ℝ) ((𝓡 2).prod 𝓘(ℝ, ℝ)) 1 η :=
    contMDiff_const.prodMk hscalar
  have hηN : MapsTo η (Icc (0 : ℝ) 1)
      (univ ×ˢ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) := by
    intro t ht
    refine ⟨mem_univ _, abs_lt.mp ((show |(1 - t) * s| ≤ |s| from ?_).trans_lt hsabs)⟩
    rw [abs_mul, abs_of_nonneg (sub_nonneg.mpr ht.2)]
    nlinarith [abs_nonneg s, ht.1]
  have hα : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 α (Icc (0 : ℝ) 1) :=
    (N.coordinate_map_smooth.of_le (by simp)).comp hη.contMDiffOn hηN
  have hηR (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : (1 - t) * s ∈ Ioo a b := by
    have hseg : s + t • (0 - s) ∈ Ioo a b := by
      apply (convex_Ioo (𝕜 := ℝ) a b).segment_subset hp.2 ⟨ha, hb⟩
      rw [segment_eq_image' (𝕜 := ℝ) s 0]
      exact ⟨t, ht, rfl⟩
    have heq : (1 - t) * s = s + t • (0 - s) := by
      simp only [smul_eq_mul]
      ring
    rwa [heq]
  have hαN : MapsTo α (Icc (0 : ℝ) 1) (N.region a b) := by
    intro t ht
    refine ⟨N.coordinate_map_mem_of_axial (η t) (hηN ht).2, ?_⟩
    change a < (N.coordinate_inverse (N.coordinate_map (η t))).2 ∧
      (N.coordinate_inverse (N.coordinate_map (η t))).2 < b
    rw [N.coordinate_inverse_coordinate_map (hηN ht)]
    exact hηR t ht
  have hα0 : α 0 = p := by
    simpa [α, η, q, s] using N.coordinate_map_coordinate_inverse hp.1
  have hα1 : α 1 = N.coordinate_map (q, 0) := by simp [α, η]
  have hηderiv (t : ℝ) :
      mfderiv 𝓘(ℝ, ℝ) ((𝓡 2).prod 𝓘(ℝ, ℝ)) η t 1 = (0, -s) := by
    have hd : HasDerivAt (fun t : ℝ => (1 - t) * s) (-s) t := by
      simpa only [zero_sub, neg_mul, one_mul] using!
        ((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)).mul_const s
    change mfderiv 𝓘(ℝ, ℝ) ((𝓡 2).prod 𝓘(ℝ, ℝ))
      (fun t => (q, (1 - t) * s)) t 1 = _
    rw [mfderiv_prodMk mdifferentiableAt_const
      (hscalar.contMDiffAt.mdifferentiableAt one_ne_zero), mfderiv_const]
    apply Prod.ext
    · rfl
    · change mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun t : ℝ => (1 - t) * s) t 1 = -s
      rw [mfderiv_eq_fderiv]
      change fderiv ℝ (fun u : ℝ => (1 - u) * s) t (1 : ℝ) = -s
      exact hd.deriv
  have hαderiv (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      curveVelocity α t =
        mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) N.coordinate_map (η t) (0, -s) := by
    have hcoord : MDifferentiableAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3)
        N.coordinate_map (η t) :=
      ((N.coordinate_map_smooth (η t) (hηN ht)).contMDiffAt
        ((isOpen_univ.prod isOpen_Ioo).mem_nhds (hηN ht))).mdifferentiableAt (by simp)
    change mfderiv 𝓘(ℝ, ℝ) (𝓡 3) (N.coordinate_map ∘ η) t 1 = _
    rw [mfderiv_comp t hcoord (hη.contMDiffAt.mdifferentiableAt one_ne_zero)]
    change mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) N.coordinate_map (η t)
      (mfderiv 𝓘(ℝ, ℝ) ((𝓡 2).prod 𝓘(ℝ, ℝ)) η t 1) = _
    rw [hηderiv]
  have hspeed (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      g.tangentNorm (α t) (curveVelocity α t) ≤ 2 * N.scale * |s| := by
    rw [hαderiv t ht]
    change g.tangentNorm (N.coordinate_map (η t))
      (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) N.coordinate_map (η t) (0, -s)) ≤ _
    have hh := (N.coordinate_speed_bounds (η t) (hηN ht).2 (0, -s)).2
    simpa only [roundCylinderMetric_self_eq, norm_zero, zero_pow (by decide : 2 ≠ 0),
      mul_zero, zero_add, neg_sq, Real.sqrt_sq_eq_abs] using hh
  have hαlen : g.pathELength α 0 1 < ENNReal.ofReal (2 * N.scale * N.epsilon⁻¹) := by
    have hb := Proofs.M09.pathELength_le_of_speed_le g α 0 1
      (2 * N.scale * |s|) (by positivity) hspeed
    have hstrict : 2 * N.scale * |s| < 2 * N.scale * N.epsilon⁻¹ :=
      mul_lt_mul_of_pos_left hsabs (mul_pos (by norm_num) N.scale_pos)
    have hb' : g.pathELength α 0 1 ≤ ENNReal.ofReal (2 * N.scale * |s|) := by
      simpa using hb
    exact hb'.trans_lt ((ENNReal.ofReal_lt_ofReal_iff
      (by positivity : 0 < 2 * N.scale * N.epsilon⁻¹)).mpr hstrict)
  have hx : N.coordinate_map (q, 0) ∈ N.central_sphere := by
    rw [N.central_sphere_eq]
    exact ⟨(q, 0), ⟨mem_univ _, rfl⟩, rfl⟩
  obtain ⟨β, hβ0, hβ1, hβ, hβsphere, hβlen, _, _⟩ :=
    exists_central_sphere_shortcut N hx N.center_on_central_sphere
  have hβN : MapsTo β (Icc (0 : ℝ) 1) (N.region a b) :=
    fun t _ => N.central_sphere_subset_region ha hb (hβsphere (mem_univ t))
  obtain ⟨γ, hγ0, hγ1, hγ, hγN, hγlen⟩ :=
    exists_intrinsic_splice g hα hβ.contMDiffOn hαN hβN (hα1.trans hβ0.symm)
  refine ⟨γ, hγ0.trans hα0, hγ1.trans hβ1, hγ, hγN, ?_⟩
  rw [hγlen]
  have hsum := ENNReal.add_lt_add hαlen hβlen
  convert hsum using 1
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1
  ring

end PoincareConjecture.M28
