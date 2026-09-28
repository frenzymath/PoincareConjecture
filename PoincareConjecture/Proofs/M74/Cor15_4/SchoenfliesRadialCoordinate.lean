import PoincareConjecture.Proofs.M74.Cor15_4.PuncturedSphereEuclidean
import Mathlib.Analysis.Calculus.Deriv.Slope

set_option autoImplicit false

open Set Metric Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M74

noncomputable def schoenfliesBoundaryParam (s : ℝ) : ℝ := (1 - 2 * s) / (2 - s)

theorem schoenfliesBoundaryParam_mem {s : ℝ} (hs : s ∈ Ioo (-1 / 8 : ℝ) (1 / 8)) :
    schoenfliesBoundaryParam s ∈ Ioo (1 / 4 : ℝ) 1 := by
  have hd : 0 < 2 - s := by linarith [hs.2]
  exact ⟨(lt_div_iff₀ hd).mpr (by linarith [hs.2]),
    (div_lt_iff₀ hd).mpr (by linarith [hs.1])⟩

theorem shift_schoenfliesBoundaryParam {s : ℝ} (hs : s ∈ Ioo (-1 / 8 : ℝ) (1 / 8)) :
    shiftCollarParam (-schoenfliesBoundaryParam s) = s := by
  have heq : -schoenfliesBoundaryParam s = unshiftCollarParam s := by
    unfold schoenfliesBoundaryParam unshiftCollarParam
    ring
  rw [heq]
  exact shift_unshiftCollarParam ⟨by linarith [hs.1], by linarith [hs.2]⟩

theorem schoenfliesBoundaryParam_strictAntiOn :
    StrictAntiOn schoenfliesBoundaryParam (Ioo (-1 / 8 : ℝ) (1 / 8)) := by
  intro a ha b hb hab
  have hda : 0 < 2 - a := by linarith [ha.2]
  have hdb : 0 < 2 - b := by linarith [hb.2]
  exact (div_lt_div_iff₀ hdb hda).mpr (by nlinarith)

end PoincareConjecture.M74

namespace PoincareConjecture.SurgeryBallEmbedding

open M74 M25.Topology3D

variable {A : GeneralizedSliceCarrier.{u}} (B : SurgeryBallEmbedding A)
  (d : Diffeomorph (𝓡 3) (𝓡 3) A.carrier ThreeSphere ∞)

noncomputable def shiftedSchoenfliesRadius
    (D : SchoenfliesData (B.shiftedPunctureCollar d) (1 / 4)) (s : ℝ) : ℝ :=
  D.radial (schoenfliesBoundaryParam s)

theorem shiftedSchoenfliesRadius_zero
    (D : SchoenfliesData (B.shiftedPunctureCollar d) (1 / 4)) :
    B.shiftedSchoenfliesRadius d D 0 = D.radial (1 / 2) := by
  norm_num [shiftedSchoenfliesRadius, schoenfliesBoundaryParam]

theorem shiftedSchoenfliesRadius_mem
    (D : SchoenfliesData (B.shiftedPunctureCollar d) (1 / 4)) {s : ℝ}
    (hs : s ∈ Ioo (-1 / 8 : ℝ) (1 / 8)) :
    B.shiftedSchoenfliesRadius d D s ∈ Ioo (0 : ℝ) D.radius := by
  have ht := schoenfliesBoundaryParam_mem hs
  exact ⟨D.radial_pos _ ⟨ht.1.le, ht.2⟩, D.radial_lt _ ⟨ht.1.le, ht.2⟩⟩

theorem shiftedSchoenfliesRadius_chart
    (D : SchoenfliesData (B.shiftedPunctureCollar d) (1 / 4)) (q : UnitTwoSphere)
    {s : ℝ} (hs : s ∈ Ioo (-1 / 8 : ℝ) (1 / 8)) :
    D.chart (B.shiftedSchoenfliesRadius d D s • (D.boundary_map q).1) =
      B.punctureCollar d (q, s) := by
  have ht := schoenfliesBoundaryParam_mem hs
  have h := D.chart_collar q (schoenfliesBoundaryParam s) ⟨ht.1.le, ht.2⟩
  rw [B.shiftedSchoenflies_side_eq_neg_one d D] at h
  simpa only [shiftedSchoenfliesRadius, shiftedPunctureCollar, Function.comp_apply,
    shiftCollar, neg_one_mul,
    shift_schoenfliesBoundaryParam hs] using h

theorem shiftedSchoenfliesRadius_inverse
    (D : SchoenfliesData (B.shiftedPunctureCollar d) (1 / 4))
    (Ψ : StandardCapSpace → StandardCapSpace)
    (hleft : ∀ x ∈ ball 0 D.radius, Ψ (D.chart x) = x) (q : UnitTwoSphere)
    {s : ℝ} (hs : s ∈ Ioo (-1 / 8 : ℝ) (1 / 8)) :
    Ψ (B.punctureCollar d (q, s)) =
      B.shiftedSchoenfliesRadius d D s • (D.boundary_map q).1 := by
  rw [← B.shiftedSchoenfliesRadius_chart d D q hs]
  apply hleft
  rw [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs,
    abs_of_pos (B.shiftedSchoenfliesRadius_mem d D hs).1,
    mem_sphere_zero_iff_norm.mp (D.boundary_map q).2, mul_one]
  exact (B.shiftedSchoenfliesRadius_mem d D hs).2

theorem shiftedSchoenfliesRadius_contDiffAt
    (D : SchoenfliesData (B.shiftedPunctureCollar d) (1 / 4))
    (Ψ : StandardCapSpace → StandardCapSpace) (hΨ : ContDiff ℝ ∞ Ψ)
    (hleft : ∀ x ∈ ball 0 D.radius, Ψ (D.chart x) = x) (q : UnitTwoSphere)
    {s : ℝ} (hs : s ∈ Ioo (-1 / 8 : ℝ) (1 / 8)) :
    ContDiffAt ℝ ∞ (B.shiftedSchoenfliesRadius d D) s := by
  have he : ContMDiffAt 𝓘(ℝ, ℝ) (𝓡 3) ∞ (fun t => B.punctureCollar d (q, t)) s :=
    ((B.punctureCollar_contMDiffOn d).contMDiffAt
      ((isOpen_univ.prod isOpen_Ioo).mem_nhds
        ⟨mem_univ _, by linarith [hs.1], by linarith [hs.2]⟩)).comp s
          (contMDiff_const.prodMk contMDiff_id).contMDiffAt
  have hne : Ψ (B.punctureCollar d (q, s)) ≠ 0 := by
    rw [B.shiftedSchoenfliesRadius_inverse d D Ψ hleft q hs]
    apply norm_pos_iff.mp
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (B.shiftedSchoenfliesRadius_mem d D hs).1,
      mem_sphere_zero_iff_norm.mp (D.boundary_map q).2, mul_one]
    exact (B.shiftedSchoenfliesRadius_mem d D hs).1
  have hn : ContDiffAt ℝ ∞ (fun t => ‖Ψ (B.punctureCollar d (q, t))‖) s :=
    (contDiffAt_norm ℝ hne).comp s (hΨ.contDiffAt.comp s he.contDiffAt)
  apply hn.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds hs] with t ht
  rw [B.shiftedSchoenfliesRadius_inverse d D Ψ hleft q ht, norm_smul, Real.norm_eq_abs,
    abs_of_pos (B.shiftedSchoenfliesRadius_mem d D ht).1,
    mem_sphere_zero_iff_norm.mp (D.boundary_map q).2, mul_one]

theorem shiftedSchoenfliesRadius_strictAntiOn
    (D : SchoenfliesData (B.shiftedPunctureCollar d) (1 / 4)) :
    StrictAntiOn (B.shiftedSchoenfliesRadius d D) (Ioo (-1 / 8 : ℝ) (1 / 8)) := by
  intro a ha b hb hab
  have hta := schoenfliesBoundaryParam_mem ha
  have htb := schoenfliesBoundaryParam_mem hb
  exact D.radial_strictMono ⟨htb.1.le, htb.2⟩ ⟨hta.1.le, hta.2⟩
    (schoenfliesBoundaryParam_strictAntiOn ha hb hab)

private noncomputable def radialHeightInverse
    (D : SchoenfliesData (B.shiftedPunctureCollar d) (1 / 4)) (q : UnitTwoSphere)
    (r : ℝ) : ℝ :=
  ‖B.inverse ((B.punctureChart d).symm (D.chart (r • (D.boundary_map q).1)))‖ - 1

private theorem original_radial_mem_ball {s : ℝ}
    (hs : s ∈ Ioo (-1 / 8 : ℝ) (1 / 8)) (q : UnitTwoSphere) :
    (1 + s) • q.1 ∈ ball 0 2 := by
  rw [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith [hs.1]),
    mem_sphere_zero_iff_norm.mp q.2, mul_one]
  linarith [hs.2]

private theorem original_radial_nonzero {s : ℝ}
    (hs : s ∈ Ioo (-1 / 8 : ℝ) (1 / 8)) (q : UnitTwoSphere) :
    (1 + s) • q.1 ≠ 0 := by
  apply norm_pos_iff.mp
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith [hs.1]),
    mem_sphere_zero_iff_norm.mp q.2, mul_one]
  linarith [hs.1]

private theorem radialHeightInverse_left
    (D : SchoenfliesData (B.shiftedPunctureCollar d) (1 / 4)) (q : UnitTwoSphere)
    {s : ℝ} (hs : s ∈ Ioo (-1 / 8 : ℝ) (1 / 8)) :
    B.radialHeightInverse d D q (B.shiftedSchoenfliesRadius d D s) = s := by
  unfold radialHeightInverse
  rw [B.shiftedSchoenfliesRadius_chart d D q hs, punctureCollar,
    (B.punctureChart d).left_inv
      ((B.map_mem_punctureChart_source_iff d (original_radial_mem_ball hs q)).mpr
        (original_radial_nonzero hs q)), B.left_inverse (original_radial_mem_ball hs q)]
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith [hs.1]),
    mem_sphere_zero_iff_norm.mp q.2, mul_one]
  ring

private theorem radialHeightInverse_contDiffAt
    (D : SchoenfliesData (B.shiftedPunctureCollar d) (1 / 4)) (q : UnitTwoSphere)
    {s : ℝ} (hs : s ∈ Ioo (-1 / 8 : ℝ) (1 / 8)) :
    ContDiffAt ℝ ∞ (B.radialHeightInverse d D q) (B.shiftedSchoenfliesRadius d D s) := by
  let r := B.shiftedSchoenfliesRadius d D s
  have hr := B.shiftedSchoenfliesRadius_mem d D hs
  have hball : r • (D.boundary_map q).1 ∈ ball (0 : StandardCapSpace) D.radius := by
    rw [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos hr.1,
      mem_sphere_zero_iff_norm.mp (D.boundary_map q).2, mul_one]
    exact hr.2
  have hc : ContMDiffAt 𝓘(ℝ, ℝ) (𝓡 3) ∞
      (fun t : ℝ => D.chart (t • (D.boundary_map q).1)) r :=
    (D.chart_smooth.contDiffAt (isOpen_ball.mem_nhds hball)).contMDiffAt.comp r
      (contMDiff_id.smul contMDiff_const).contMDiffAt
  have heq : (B.punctureChart d).symm (D.chart (r • (D.boundary_map q).1)) =
      B.map ((1 + s) • q.1) := by
    rw [B.shiftedSchoenfliesRadius_chart d D q hs, punctureCollar,
      (B.punctureChart d).left_inv
        ((B.map_mem_punctureChart_source_iff d (original_radial_mem_ball hs q)).mpr
          (original_radial_nonzero hs q))]
  have hbi : ContMDiffAt (𝓡 3) (𝓡 3) ∞ B.inverse
      ((B.punctureChart d).symm (D.chart (r • (D.boundary_map q).1))) := by
    rw [heq]
    exact B.inverse_smooth.contMDiffAt
      (B.chartRegion_open.mem_nhds (mem_image_of_mem _ (original_radial_mem_ball hs q)))
  have hi := hbi.comp r ((B.punctureChart_symm_contMDiff d).contMDiffAt.comp r hc)
  have hne : B.inverse ((B.punctureChart d).symm
      (D.chart (r • (D.boundary_map q).1))) ≠ 0 := by
    rw [heq, B.left_inverse (original_radial_mem_ball hs q)]
    exact original_radial_nonzero hs q
  exact ((contDiffAt_norm ℝ hne).comp r hi.contDiffAt).sub contDiffAt_const

theorem shiftedSchoenfliesRadius_deriv_neg
    (D : SchoenfliesData (B.shiftedPunctureCollar d) (1 / 4))
    (Ψ : StandardCapSpace → StandardCapSpace) (hΨ : ContDiff ℝ ∞ Ψ)
    (hleft : ∀ x ∈ ball 0 D.radius, Ψ (D.chart x) = x) (q : UnitTwoSphere)
    {s : ℝ} (hs : s ∈ Ioo (-1 / 8 : ℝ) (1 / 8)) :
    deriv (B.shiftedSchoenfliesRadius d D) s < 0 := by
  have hρ := (B.shiftedSchoenfliesRadius_contDiffAt d D Ψ hΨ hleft q hs).differentiableAt
    (by simp)
  have hh := (B.radialHeightInverse_contDiffAt d D q hs).differentiableAt (by simp)
  have hevent : B.radialHeightInverse d D q ∘ B.shiftedSchoenfliesRadius d D =ᶠ[𝓝 s] id := by
    filter_upwards [isOpen_Ioo.mem_nhds hs] with t ht
    exact B.radialHeightInverse_left d D q ht
  have hcomp := deriv_comp s hh hρ
  rw [hevent.deriv_eq, deriv_id] at hcomp
  have hne : deriv (B.shiftedSchoenfliesRadius d D) s ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at hcomp
    exact one_ne_zero hcomp
  have hnonpos := (B.shiftedSchoenfliesRadius_strictAntiOn d D).antitoneOn.derivWithin_nonpos
    (x := s)
  rw [derivWithin_of_isOpen isOpen_Ioo hs] at hnonpos
  exact lt_of_le_of_ne hnonpos hne

end PoincareConjecture.SurgeryBallEmbedding
