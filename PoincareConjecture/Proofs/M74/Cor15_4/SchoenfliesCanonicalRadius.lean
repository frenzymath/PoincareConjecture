import PoincareConjecture.Proofs.M74.Cor15_4.SchoenfliesRadiusInverse
import PoincareConjecture.Proofs.M74.Mathlib.ReciprocalRadiusExtension










set_option autoImplicit false

open Set Metric Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.SurgeryBallEmbedding

open M74 M25.Topology3D

variable {A : GeneralizedSliceCarrier.{u}} (B : SurgeryBallEmbedding A)
  (d : Diffeomorph (𝓡 3) (𝓡 3) A.carrier ThreeSphere ∞)




theorem exists_schoenfliesCanonicalRadius
    (D : SchoenfliesData (B.shiftedPunctureCollar d) (1 / 4))
    (Ψ : StandardCapSpace → StandardCapSpace) (hΨ : ContDiff ℝ ∞ Ψ)
    (hleft : ∀ x ∈ ball 0 D.radius, Ψ (D.chart x) = x) (q : UnitTwoSphere) :
    ∃ (f : OpenPartialHomeomorph ℝ ℝ) (k a ε : ℝ),
      0 < k ∧ 0 < a ∧ a < D.radial (1 / 2) ∧ 0 < ε ∧ ε < 1 / 16 ∧
      f.source = Ioo 0 (D.radial (1 / 2)) ∧ f.target = Ioi 0 ∧
      ContDiffOn ℝ ∞ f f.source ∧ ContDiffOn ℝ ∞ f.symm f.target ∧
      (∀ r ∈ Ioo (0 : ℝ) a, f r = k * r) ∧
      (∀ s ∈ Ioo (0 : ℝ) ε, f (B.shiftedSchoenfliesRadius d D s) = 1 / s) := by
  let ρ := B.shiftedSchoenfliesRadius d D
  let e := B.shiftedSchoenfliesRadiusChart d D Ψ hΨ hleft q
  let R := D.radial (1 / 2)
  let a0 := ρ (1 / 16)
  have hρ0 : ρ 0 = R := B.shiftedSchoenfliesRadius_zero d D
  have hm : StrictAntiOn ρ (Ioo (-1 / 8 : ℝ) (1 / 8)) :=
    B.shiftedSchoenfliesRadius_strictAntiOn d D
  have ha0 : 0 < a0 := (B.shiftedSchoenfliesRadius_mem d D (by norm_num)).1
  have ha0R : a0 < R := by
    rw [← hρ0]
    exact hm (by norm_num) (by norm_num) (by norm_num)
  have hRhi : R < ρ (-1 / 16) := by
    rw [← hρ0]
    exact hm (by norm_num) (by norm_num) (by norm_num)
  have hRt : R ∈ e.target := ⟨ha0R, hRhi⟩
  have hsub : Ioo a0 R ⊆ e.target := fun _ hr => ⟨hr.1, hr.2.trans hRhi⟩
  have hσ : ContDiffOn ℝ ∞ e.symm (Ioo a0 R) :=
    (B.shiftedSchoenfliesRadiusChart_symm_contDiffOn d D Ψ hΨ hleft q).mono hsub
  have hpos : ∀ r ∈ Ioo a0 R, 0 < e.symm r := by
    intro r hr
    have hx : e.symm r ∈ Ioo (-1 / 16 : ℝ) (1 / 16) := e.map_target (hsub hr)
    by_contra h
    have hle := hm.antitoneOn
      (show e.symm r ∈ Ioo (-1 / 8 : ℝ) (1 / 8) by
        constructor <;> linarith [hx.1, hx.2])
      (by norm_num : (0 : ℝ) ∈ Ioo (-1 / 8 : ℝ) (1 / 8)) (le_of_not_gt h)
    change ρ 0 ≤ e (e.symm r) at hle
    rw [e.right_inv (hsub hr), hρ0] at hle
    exact (not_le_of_gt hr.2) hle
  have hder : ∀ r ∈ Ioo a0 R, deriv e.symm r < 0 := fun r hr =>
    B.shiftedSchoenfliesRadiusChart_symm_deriv_neg d D Ψ hΨ hleft q (hsub hr)
  have hzero : e.symm R = 0 := B.shiftedSchoenfliesRadiusChart_symm_boundary d D Ψ hΨ hleft q
  let a := (2 * a0 + R) / 3
  let b := (a0 + 2 * R) / 3
  have ha : a0 < a := by dsimp [a]; linarith
  have hab : a < b := by dsimp [a, b]; linarith
  have hbR : b < R := by dsimp [b]; linarith
  obtain ⟨k, f, hk, hfs, hft, hff, hfi, hflin, hfout⟩ :=
    exists_reciprocalRadiusChart e.symm ha0 ha hab hbR hσ hpos hder
      (e.symm.continuousAt hRt) hzero
  have hρcont : ContinuousAt ρ 0 :=
    (B.shiftedSchoenfliesRadius_contDiffAt d D Ψ hΨ hleft q (by norm_num)).continuousAt
  have hnearb : ∀ᶠ s in 𝓝 (0 : ℝ), b < ρ s :=
    hρcont.eventually (isOpen_Ioi.mem_nhds (hρ0.symm ▸ hbR))
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp hnearb
  let ε := min δ (1 / 32 : ℝ)
  have hε : 0 < ε := lt_min hδ (by norm_num)
  have hεsmall : ε < 1 / 16 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  refine ⟨f, k, a, ε, hk, ha0.trans ha, hab.trans hbR, hε, hεsmall,
    hfs, hft, hff, hfi, hflin, ?_⟩
  intro s hs
  have hsJ : s ∈ Ioo (-1 / 16 : ℝ) (1 / 16) :=
    ⟨by linarith [hs.1], hs.2.trans hεsmall⟩
  have hsI : s ∈ Ioo (-1 / 8 : ℝ) (1 / 8) := by
    constructor <;> linarith [hsJ.1, hsJ.2]
  have hbs : b < ρ s := by
    apply hδsub
    rw [mem_ball_zero_iff, Real.norm_eq_abs, abs_of_pos hs.1]
    exact hs.2.trans_le (min_le_left _ _)
  have hsR : ρ s < R := by
    rw [← hρ0]
    exact hm (by norm_num) hsI hs.1
  rw [hfout _ ⟨hbs, hsR⟩]
  change 1 / e.symm (e s) = 1 / s
  rw [e.left_inv hsJ]

end PoincareConjecture.SurgeryBallEmbedding
