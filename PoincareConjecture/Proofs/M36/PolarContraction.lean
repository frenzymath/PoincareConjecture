import PoincareConjecture.Proofs.M36.PolarMetric
import PoincareConjecture.Proofs.M36.CollapseMap
import PoincareConjecture.Proofs.M36.StandardCapConcavity










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M36

local notation "E₂" => EuclideanSpace ℝ (Fin 2)
local notation "C" => StandardCylinderCoordinates
local notation "IC" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)

theorem cylinder_height_translation_mfderiv (a : ℝ)
    (z : StandardCylinderSpace) (v : C) :
    mfderiv IC IC (fun w : StandardCylinderSpace => (w.1, w.2 - a)) z v = v := by
  erw [mfderiv_prodMk mdifferentiableAt_fst
    (mdifferentiableAt_snd.sub mdifferentiableAt_const), mfderiv_fst,
    mfderiv_sub mdifferentiableAt_snd mdifferentiableAt_const,
    mfderiv_snd, mfderiv_const]
  change (v.1, v.2 - 0) = v
  simp

theorem adaptedPolarPoint_quadratic_end (g₀ : StandardInitialMetric)
    (z : StandardCylinderSpace) (hz : g₀.cylindrical_end.radius < z.2) (v : C) :
    g₀.metric.inner (adaptedPolarPoint g₀ z)
      (mfderiv IC (𝓡 3) (adaptedPolarPoint g₀) z v)
      (mfderiv IC (𝓡 3) (adaptedPolarPoint g₀) z v) =
      RoundCylinderMetric z v v := by
  let T : StandardCylinderSpace → StandardCylinderSpace :=
    fun w => (w.1, w.2 - g₀.cylindrical_end.radius)
  have hT : ContMDiff IC IC ∞ T :=
    contMDiff_fst.prodMk (contMDiff_snd.sub contMDiff_const)
  have hE := (cylindrical_coordinate_contMDiffAt g₀ (T z)
    (by dsimp [T]; linarith [g₀.cylindrical_end.collar_pos])).mdifferentiableAt (by simp)
  have heq : adaptedPolarPoint g₀ =ᶠ[nhds z] g₀.cylindrical_end.coordinate ∘ T := by
    filter_upwards [(isOpen_lt continuous_const continuous_snd).mem_nhds hz] with w hw
    exact adaptedPolarPoint_eq_end g₀ w hw.le
  have hd := heq.mfderiv_eq (I := IC) (I' := 𝓡 3)
  rw [mfderiv_comp z hE ((hT z).mdifferentiableAt (by simp))] at hd
  have hdv := congrArg (fun L => L v) hd
  change mfderiv IC (𝓡 3) (adaptedPolarPoint g₀) z v =
    mfderiv IC (𝓡 3) g₀.cylindrical_end.coordinate (T z)
      (mfderiv IC IC T z v) at hdv
  have hTv : mfderiv IC IC T z v = v := cylinder_height_translation_mfderiv _ z v
  rw [hTv] at hdv
  rw [hdv, adaptedPolarPoint_eq_end g₀ z hz.le]
  exact g₀.cylindrical_end.metric_pullback (T z) (sub_nonneg.mpr hz.le) v v

theorem adaptedPolarPoint_contracts (g₀ : StandardInitialMetric)
    (z : StandardCylinderSpace) (hz : 0 < z.2) (v : C) :
    g₀.metric.inner (adaptedPolarPoint g₀ z)
      (mfderiv IC (𝓡 3) (adaptedPolarPoint g₀) z v)
      (mfderiv IC (𝓡 3) (adaptedPolarPoint g₀) z v) ≤
      RoundCylinderMetric z v v := by
  by_cases hR : z.2 ≤ g₀.cylindrical_end.radius + 1
  · let zstar : StandardCylinderSpace := (z.1, g₀.cylindrical_end.radius + 1)
    have hstarpos : 0 < zstar.2 := by
      dsimp [zstar]
      linarith [g₀.cylindrical_end.radius_pos]
    have hstar := adaptedPolarPoint_quadratic_end g₀ zstar (by dsimp [zstar]; linarith) v
    rw [adaptedPolarPoint_quadratic g₀ zstar hstarpos v] at hstar
    have hrad := (radialEuclideanRadius_strictMono g₀).monotone hR
    have hrpos := (radialEuclideanRadius_pos_iff g₀ _).mpr hz
    have hstarrpos := (radialEuclideanRadius_pos_iff g₀ _).mpr hstarpos
    have hp := euclideanWarpRadius_monotoneOn g₀ hrpos.le hstarrpos.le hrad
    have hpsq := pow_le_pow_left₀ (euclideanWarpRadius_pos g₀ hrpos).le hp 2
    have ha : 0 ≤ inner ℝ
        (mvfderiv (𝓡 2) (adaptedAngularEmbedding g₀) z.1 v.1)
        (mvfderiv (𝓡 2) (adaptedAngularEmbedding g₀) z.1 v.1) := real_inner_self_nonneg
    rw [adaptedPolarPoint_quadratic g₀ z hz v]
    calc
      _ ≤ euclideanWarpRadius g₀ (radialEuclideanRadius g₀ zstar.2) ^ 2 *
          inner ℝ (mvfderiv (𝓡 2) (adaptedAngularEmbedding g₀) z.1 v.1)
            (mvfderiv (𝓡 2) (adaptedAngularEmbedding g₀) z.1 v.1) + v.2 ^ 2 :=
        add_le_add (mul_le_mul_of_nonneg_right hpsq ha) le_rfl
      _ = _ := hstar
  · exact (adaptedPolarPoint_quadratic_end g₀ z (by linarith) v).le

theorem cylinder_height_reversal_mfderiv (S : ℝ)
    (z : StandardCylinderSpace) (v : C) :
    mfderiv IC IC (fun w : StandardCylinderSpace => (w.1, S - w.2)) z v = (v.1, -v.2) := by
  erw [mfderiv_prodMk mdifferentiableAt_fst
    (mdifferentiableAt_const.sub mdifferentiableAt_snd), mfderiv_fst,
    mfderiv_sub mdifferentiableAt_const mdifferentiableAt_snd,
    mfderiv_snd, mfderiv_const]
  change (v.1, 0 - v.2) = (v.1, -v.2)
  simp

theorem adaptedClippedCollapse_contracts (g₀ : StandardInitialMetric) (S : ℝ)
    (z : StandardCylinderSpace) (hz : z.2 < S) (v : C) :
    g₀.metric.inner (adaptedClippedCollapse g₀ S z)
      (mfderiv IC (𝓡 3) (adaptedClippedCollapse g₀ S) z v)
      (mfderiv IC (𝓡 3) (adaptedClippedCollapse g₀ S) z v) ≤
      RoundCylinderMetric z v v := by
  let T : StandardCylinderSpace → StandardCylinderSpace := fun w => (w.1, S - w.2)
  have hT : ContMDiff IC IC ∞ T :=
    contMDiff_fst.prodMk (contMDiff_const.sub contMDiff_snd)
  have heq : adaptedClippedCollapse g₀ S =ᶠ[nhds z] adaptedPolarPoint g₀ ∘ T := by
    filter_upwards [(isOpen_lt continuous_snd continuous_const).mem_nhds hz] with w hw
    exact adaptedClippedCollapse_of_lt g₀ S w hw
  have hd := heq.mfderiv_eq (I := IC) (I' := 𝓡 3)
  rw [mfderiv_comp z ((adaptedPolarPoint_contMDiff g₀ (T z)).mdifferentiableAt (by simp))
    ((hT z).mdifferentiableAt (by simp))] at hd
  have hdv := congrArg (fun L => L v) hd
  change mfderiv IC (𝓡 3) (adaptedClippedCollapse g₀ S) z v =
    mfderiv IC (𝓡 3) (adaptedPolarPoint g₀) (T z) (mfderiv IC IC T z v) at hdv
  rw [show mfderiv IC IC T z v = (v.1, -v.2) from cylinder_height_reversal_mfderiv S z v] at hdv
  rw [hdv, adaptedClippedCollapse_of_lt g₀ S z hz]
  have h := adaptedPolarPoint_contracts g₀ (T z) (sub_pos.mpr hz) (v.1, -v.2)
  convert! h using 1
  change 2 * (1 - (0 : ℝ)) * _ + v.2 * v.2 =
    2 * (1 - (0 : ℝ)) * _ + (-v.2) * (-v.2)
  ring

end PoincareConjecture.M36
