import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Geometry.Comparison
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.TangentBound
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.PathDisplacement
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.SpaceForm.SphereDistance









noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set
open Poincare.Geometry.Riemannian.SpaceForm
open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.EpsilonNeck

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] {g : RiemannianMetric 3 M} (N : EpsilonNeck g)

theorem edist_coordinate_map_slice_le (q r : UnitTwoSphere) {a : ℝ}
    (ha : a ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) :
    g.edist (N.coordinate_map (q, a)) (N.coordinate_map (r, a)) ≤
      ENNReal.ofReal (N.scale * Real.sqrt (1 + N.epsilon) * Real.sqrt 2 * Real.pi) := by
  have hcoord (q : UnitTwoSphere) :
      ContMDiffAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ N.coordinate_map (q, a) :=
    N.coordinate_map_smooth.contMDiffAt
      (N.cylinderDomain_open.mem_nhds ⟨mem_univ q, ha⟩)
  let F : UnitTwoSphere → M := fun q => N.coordinate_map (q, a)
  have hF : ContMDiff (𝓡 2) (𝓡 3) 1 F := by
    intro q
    exact ((hcoord q).comp q
      (contMDiffAt_id.prodMk contMDiffAt_const)).of_le (by simp)
  have hderiv (q : UnitTwoSphere) (v : TangentSpace (𝓡 2) q) :
      mfderiv (𝓡 2) (𝓡 3) F q v =
        mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) N.coordinate_map (q, a) (v, 0) := by
    dsimp only [TangentSpace] at v ⊢
    change mfderiv (𝓡 2) (𝓡 3)
      (N.coordinate_map ∘ fun q : UnitTwoSphere => (q, a)) q v = _
    have h := mfderiv_comp_apply q ((hcoord q).mdifferentiableAt (by simp))
      (mdifferentiableAt_id.prodMk mdifferentiableAt_const) v
    simp only [id_eq, mfderiv_prod_left] at h
    exact h
  let C := N.scale * Real.sqrt (1 + N.epsilon) * Real.sqrt 2
  have hplus : 0 ≤ 1 + N.epsilon := by linarith [N.epsilon_pos]
  have hC : 0 < C := mul_pos (mul_pos N.scale_pos
    (Real.sqrt_pos.mpr (by linarith [N.epsilon_pos]))) (Real.sqrt_pos.mpr (by norm_num))
  have hCsq : C ^ 2 = (1 + N.epsilon) * N.scale ^ 2 * 2 := by
    dsimp [C]
    rw [mul_pow, mul_pow, Real.sq_sqrt hplus, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    ring
  have hbound (q : UnitTwoSphere) (v : TangentSpace (𝓡 2) q) :
      g.inner (F q) (mfderiv (𝓡 2) (𝓡 3) F q v)
        (mfderiv (𝓡 2) (𝓡 3) F q v) ≤
        C ^ 2 * (roundSphereMetric 2).inner q v v := by
    have h := (N.pullback_metric_bounds (z := (q, a)) ha (v, 0)).2
    rw [hderiv, hCsq]
    simpa only [roundCylinderPullback, EvolvingRoundCylinderMetric,
      roundSphereMetric_inner, RiemannianMetric.euclideanMetric_inner,
      sub_zero, mul_one, zero_mul, add_zero, mul_assoc] using h
  have hdist := (roundSphereMetric 2).edist_le_mul_of_inner_mfderiv_le
    g hF hC hbound q r
  have hpi : (roundSphereMetric 2).edist q r ≤ ENNReal.ofReal Real.pi := by
    rw [Poincare.Geometry.Riemannian.SpaceForm.roundSphereMetric_edist_eq_angle (by norm_num)]
    exact ENNReal.ofReal_le_ofReal (Real.arccos_le_pi _)
  exact hdist.trans (by
    rw [ENNReal.ofReal_mul hC.le]
    exact mul_le_mul' le_rfl hpi)

theorem edist_coordinate_map_zero_le (q r : UnitTwoSphere) :
    g.edist (N.coordinate_map (q, 0)) (N.coordinate_map (r, 0)) ≤
      ENNReal.ofReal (N.scale * Real.sqrt (1 + N.epsilon) * Real.sqrt 2 * Real.pi) :=
  N.edist_coordinate_map_slice_le q r
    ⟨neg_neg_of_pos (inv_pos.mpr N.epsilon_pos), inv_pos.mpr N.epsilon_pos⟩

theorem edist_central_sphere_le {x y : M}
    (hx : x ∈ N.central_sphere) (hy : y ∈ N.central_sphere) :
    g.edist x y ≤
      ENNReal.ofReal (N.scale * Real.sqrt (1 + N.epsilon) * Real.sqrt 2 * Real.pi) := by
  rw [N.central_sphere_eq] at hx hy
  rcases hx with ⟨⟨q, a⟩, ⟨_, ha⟩, rfl⟩
  rcases hy with ⟨⟨r, b⟩, ⟨_, hb⟩, rfl⟩
  have ha0 : a = 0 := ha
  have hb0 : b = 0 := hb
  subst a
  subst b
  exact N.edist_coordinate_map_zero_le q r

theorem edist_central_sphere_le_two_pi_mul_scale {x y : M}
    (hx : x ∈ N.central_sphere) (hy : y ∈ N.central_sphere) :
    g.edist x y ≤ ENNReal.ofReal ((2 * Real.pi) * N.scale) := by
  apply (N.edist_central_sphere_le hx hy).trans
  apply ENNReal.ofReal_le_ofReal
  have hs : Real.sqrt (1 + N.epsilon) * Real.sqrt 2 ≤ 2 := by
    have hsq : (Real.sqrt (1 + N.epsilon) * Real.sqrt 2) ^ 2 =
        (1 + N.epsilon) * 2 := by
      rw [mul_pow, Real.sq_sqrt (by linarith [N.epsilon_pos]),
        Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    nlinarith [N.epsilon_lt_half, mul_nonneg (Real.sqrt_nonneg (1 + N.epsilon))
      (Real.sqrt_nonneg 2)]
  have h := mul_le_mul_of_nonneg_left hs N.scale_pos.le
  nlinarith [mul_le_mul_of_nonneg_right h Real.pi_pos.le]



theorem edist_coordinate_map_axis_le (q : UnitTwoSphere) {a b : ℝ}
    (ha : a ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹)
    (hb : b ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) :
    g.edist (N.coordinate_map (q, a)) (N.coordinate_map (q, b)) ≤
      ENNReal.ofReal (N.scale * Real.sqrt (1 + N.epsilon) * |b - a|) := by
  let γ : ℝ → M := fun t => N.coordinate_map (q, t)
  have hγ : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) ∞ γ
      (Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) :=
    N.coordinate_map_smooth.comp (contMDiff_const.prodMk contMDiff_id).contMDiffOn
      (fun _ ht => ⟨mem_univ _, ht⟩)
  have hspeed (t : ℝ) (ht : t ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) :
      g.tangentNorm (γ t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) γ t 1) ≤
        N.scale * Real.sqrt (1 + N.epsilon) := by
    have hcoord : ContMDiffAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞
        N.coordinate_map (q, t) := N.coordinate_map_smooth.contMDiffAt
      (N.cylinderDomain_open.mem_nhds ⟨mem_univ q, ht⟩)
    have hd : mfderiv 𝓘(ℝ, ℝ) (𝓡 3) γ t 1 =
        mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) N.coordinate_map (q, t) (0, 1) := by
      change mfderiv 𝓘(ℝ, ℝ) (𝓡 3)
        (N.coordinate_map ∘ fun t : ℝ => (q, t)) t 1 = _
      rw [mfderiv_comp_apply t (hcoord.mdifferentiableAt (by simp))
        (mdifferentiableAt_const.prodMk mdifferentiableAt_id)]
      simp only [mfderiv_prod_right]
      rfl
    have h := (N.pullback_metric_bounds (z := (q, t)) ht (0, 1)).2
    have hinner : g.inner (γ t)
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) γ t 1)
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) γ t 1) ≤
          (N.scale * Real.sqrt (1 + N.epsilon)) ^ 2 := by
      rw [hd, mul_pow, Real.sq_sqrt (by linarith [N.epsilon_pos])]
      simpa only [roundCylinderPullback, EvolvingRoundCylinderMetric,
        roundSphereMetric_inner, RiemannianMetric.euclideanMetric_inner,
        map_zero, inner_zero_left, mul_zero, zero_mul, zero_add, one_mul, mul_one,
        mul_comm] using h
    exact (Real.sqrt_le_sqrt hinner).trans_eq
      (Real.sqrt_sq (mul_nonneg N.scale_pos.le (Real.sqrt_nonneg _)))
  have hordered {a b : ℝ} (ha : a ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹)
      (hb : b ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) (hab : a ≤ b) :
      g.edist (γ a) (γ b) ≤
        ENNReal.ofReal (N.scale * Real.sqrt (1 + N.epsilon) * (b - a)) := by
    apply g.edist_le_of_tangentNorm_le hab isOpen_Ioo
      (fun t ht => ⟨ha.1.trans_le ht.1, ht.2.trans_lt hb.2⟩) hγ
      (mul_nonneg N.scale_pos.le (Real.sqrt_nonneg _))
    exact fun t ht => hspeed t ⟨ha.1.trans_le ht.1, ht.2.trans_lt hb.2⟩
  rcases le_total a b with hab | hba
  · simpa only [abs_of_nonneg (sub_nonneg.mpr hab)] using hordered ha hb hab
  · let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    have hcomm : g.edist (γ a) (γ b) = g.edist (γ b) (γ a) :=
      Manifold.riemannianEDist_comm
    change g.edist (γ a) (γ b) ≤ _
    rw [hcomm, abs_of_nonpos (sub_nonpos.mpr hba), neg_sub]
    exact hordered hb ha hba



theorem edist_central_sphere_le_of_mem_carrier {x y : M}
    (hx : x ∈ N.carrier) (hy : y ∈ N.central_sphere) :
    g.edist x y ≤
      ENNReal.ofReal ((2 * Real.pi + 2 * |(N.coordinate_inverse x).2|) * N.scale) := by
  have hscale := N.scale_pos
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let z := N.coordinate_inverse x
  have hz : z.2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ :=
    (N.coordinate_inverse_mem x hx).2
  have hzero : (0 : ℝ) ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ :=
    ⟨neg_neg_of_pos (inv_pos.mpr N.epsilon_pos), inv_pos.mpr N.epsilon_pos⟩
  have hcoord : N.coordinate_map z = x := by
    have h := congrArg Subtype.val (N.coordinate_inverse_right x hx)
    rwa [N.coordinate_map_eq] at h
  have hcentral : N.coordinate_map (z.1, 0) ∈ N.central_sphere := by
    rw [N.central_sphere_eq]
    exact ⟨(z.1, 0), ⟨mem_univ _, rfl⟩, rfl⟩
  have haxial := N.edist_coordinate_map_axis_le z.1 hz hzero
  simp only [zero_sub, abs_neg] at haxial
  rw [Prod.eta z, hcoord] at haxial
  have hroot : Real.sqrt (1 + N.epsilon) ≤ 2 := by
    have hs := Real.sq_sqrt (show 0 ≤ 1 + N.epsilon by linarith [N.epsilon_pos])
    nlinarith [Real.sqrt_nonneg (1 + N.epsilon), N.epsilon_lt_half]
  have haxis : N.scale * Real.sqrt (1 + N.epsilon) * |z.2| ≤
      2 * |z.2| * N.scale := by
    calc
      _ ≤ N.scale * 2 * |z.2| :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hroot N.scale_pos.le) (abs_nonneg _)
      _ = _ := by ring
  calc
    g.edist x y ≤ g.edist x (N.coordinate_map (z.1, 0)) +
        g.edist (N.coordinate_map (z.1, 0)) y := Manifold.riemannianEDist_triangle
    _ ≤ ENNReal.ofReal (2 * |z.2| * N.scale) +
        ENNReal.ofReal ((2 * Real.pi) * N.scale) :=
      add_le_add (haxial.trans (ENNReal.ofReal_le_ofReal haxis))
        (N.edist_central_sphere_le_two_pi_mul_scale hcentral hy)
    _ = _ := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      ring

theorem toReal_edist_central_sphere_le_of_mem_carrier {x y : M}
    (hx : x ∈ N.carrier) (hy : y ∈ N.central_sphere) :
    (g.edist x y).toReal ≤
      (2 * Real.pi + 2 * |(N.coordinate_inverse x).2|) * N.scale := by
  have hscale := N.scale_pos
  have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top
    (N.edist_central_sphere_le_of_mem_carrier hx hy)
  rwa [ENNReal.toReal_ofReal (by positivity)] at h



theorem toReal_edist_central_sphere_le_of_abs_axis_le_one {x y : M}
    (hx : x ∈ N.carrier) (hy : y ∈ N.central_sphere)
    (haxis : |(N.coordinate_inverse x).2| ≤ 1) :
    (g.edist x y).toReal ≤ (2 * Real.pi + 2) * N.scale := by
  apply (N.toReal_edist_central_sphere_le_of_mem_carrier hx hy).trans
  exact mul_le_mul_of_nonneg_right (by linarith) N.scale_pos.le



theorem edist_center_le_of_mem_carrier {x : M} (hx : x ∈ N.carrier) :
    g.edist N.center x ≤
      ENNReal.ofReal ((2 * Real.pi + 2 * N.epsilon⁻¹) * N.scale) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let z := N.coordinate_inverse x
  have hscale := N.scale_pos
  have hepsilon := N.epsilon_pos
  have hz : z.2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ :=
    (N.coordinate_inverse_mem x hx).2
  have hzero : (0 : ℝ) ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ :=
    ⟨neg_neg_of_pos (inv_pos.mpr N.epsilon_pos), inv_pos.mpr N.epsilon_pos⟩
  have hcoord : N.coordinate_map z = x := by
    have h := congrArg Subtype.val (N.coordinate_inverse_right x hx)
    rwa [N.coordinate_map_eq] at h
  have hcentral : N.coordinate_map (z.1, 0) ∈ N.central_sphere := by
    rw [N.central_sphere_eq]
    exact ⟨(z.1, 0), ⟨mem_univ _, rfl⟩, rfl⟩
  have haxial := N.edist_coordinate_map_axis_le z.1 hzero hz
  simp only [sub_zero] at haxial
  rw [Prod.eta z, hcoord] at haxial
  have hroot : Real.sqrt (1 + N.epsilon) ≤ 2 := by
    have hs := Real.sq_sqrt (show 0 ≤ 1 + N.epsilon by linarith [N.epsilon_pos])
    nlinarith [Real.sqrt_nonneg (1 + N.epsilon), N.epsilon_lt_half]
  have haxis : N.scale * Real.sqrt (1 + N.epsilon) * |z.2| ≤
      2 * N.epsilon⁻¹ * N.scale := by
    have hzabs : |z.2| ≤ N.epsilon⁻¹ := (abs_le.mpr ⟨hz.1.le, hz.2.le⟩)
    calc
      _ ≤ N.scale * 2 * N.epsilon⁻¹ :=
        mul_le_mul (mul_le_mul_of_nonneg_left hroot N.scale_pos.le) hzabs
          (abs_nonneg _) (by positivity)
      _ = _ := by ring
  calc
    g.edist N.center x ≤ g.edist N.center (N.coordinate_map (z.1, 0)) +
        g.edist (N.coordinate_map (z.1, 0)) x := Manifold.riemannianEDist_triangle
    _ ≤ ENNReal.ofReal ((2 * Real.pi) * N.scale) +
        ENNReal.ofReal (2 * N.epsilon⁻¹ * N.scale) :=
      add_le_add (N.edist_central_sphere_le_two_pi_mul_scale
        N.center_on_central_sphere hcentral)
        (haxial.trans (ENNReal.ofReal_le_ofReal haxis))
    _ = _ := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      ring

end PoincareConjecture.EpsilonNeck
