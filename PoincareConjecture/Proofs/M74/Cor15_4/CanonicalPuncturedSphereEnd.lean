import PoincareConjecture.Proofs.M74.Cor15_4.SchoenfliesCanonicalRadius
import PoincareConjecture.Proofs.M74.Cor15_4.SchoenfliesExteriorBall
import PoincareConjecture.Proofs.M74.Cor15_4.CollarAbsorptionRadial










set_option autoImplicit false

open Set Metric Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.SurgeryBallEmbedding

open M74 M25.Topology3D

variable {A : GeneralizedSliceCarrier.{u}} (B : SurgeryBallEmbedding A)
  (d : Diffeomorph (𝓡 3) (𝓡 3) A.carrier ThreeSphere ∞)

include d in



theorem exists_canonicalPuncturedSphereEnd (hS : SchoenfliesService)
    (hD : DiffSphereIsotopyService) :
    ∃ (E : Diffeomorph (𝓡 3) (𝓡 3)
      (⟨B.closedBallᶜ, B.closedBall_closed.isOpen_compl⟩ : TopologicalSpace.Opens A.carrier)
      StandardCapSpace ∞) (ε : ℝ), 0 < ε ∧ ∃ hε1 : ε < 1,
        ∀ (q : UnitTwoSphere) (s : ℝ) (hs : s ∈ Ioo (0 : ℝ) ε),
          E ⟨B.map ((1 + s) • q.1), B.radial_mem_complement q
            ⟨by linarith [hs.1], by linarith [hs.2]⟩⟩ = (1 / s) • q.1 := by
  obtain ⟨D⟩ := hS (B.shiftedPunctureCollar d) (B.shiftedPunctureCollar_isCollarEmbedding d)
    (1 / 4) (by norm_num) (by norm_num)
  obtain ⟨Ψ, hΨon, hleft⟩ := D.chart_inverse
  rw [B.shiftedSchoenflies_chart_image_univ d D] at hΨon
  have hΨ : ContDiff ℝ ∞ Ψ := contDiffOn_univ.mp hΨon
  obtain ⟨v, hv⟩ := exists_norm_eq StandardCapSpace (by norm_num : (0 : ℝ) ≤ 1)
  let q0 : UnitTwoSphere := ⟨v, mem_sphere_zero_iff_norm.mpr hv⟩
  obtain ⟨I⟩ := hD D.boundary_map
  obtain ⟨f, k, a, ε0, hk, ha, haR, hε0, hε016, hfs, hft, hff, hfi, hflin, hfend⟩ :=
    B.exists_schoenfliesCanonicalRadius d D Ψ hΨ hleft q0
  let R := D.radial (1 / 2)
  have hR : 0 < R := D.radial_pos _ (by norm_num)
  have hquarter : 0 < R / 4 := by positivity
  have hquarterhalf : R / 4 < R / 2 := by linarith
  let K := radialDiffeomorph I q0 hquarter hquarterhalf
  have hK : ∀ x, ‖K x‖ = ‖x‖ := radialDiffeomorph_norm I q0 hquarter hquarterhalf
  let KB := restrictDiffeomorphBall K hK R
  let T := radialBallDiffeomorph f hfs hft hff hfi ha haR.le hk hflin
  let C := B.schoenfliesExteriorBall d D Ψ hΨ hleft
  let E := (C.trans KB.symm).trans T
  let ρ := B.shiftedSchoenfliesRadius d D
  have hρ0 : ρ 0 = R := B.shiftedSchoenfliesRadius_zero d D
  have hρcont : ContinuousAt ρ 0 :=
    (B.shiftedSchoenfliesRadius_contDiffAt d D Ψ hΨ hleft q0 (by norm_num)).continuousAt
  have hρhalf0 : R / 2 < ρ 0 := by rw [hρ0]; linarith
  have hevent : ∀ᶠ s in 𝓝 (0 : ℝ), R / 2 < ρ s :=
    hρcont.eventually (isOpen_Ioi.mem_nhds hρhalf0)
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp hevent
  let ε := min δ ε0
  have hε : 0 < ε := lt_min hδ hε0
  have hε016 : ε < 1 / 16 := (min_le_right _ _).trans_lt hε016
  have hε1 : ε < 1 := by linarith
  refine ⟨E, ε, hε, hε1, ?_⟩
  intro q s hs
  have hs0 : s ∈ Ioo (0 : ℝ) ε0 := ⟨hs.1, hs.2.trans_le (min_le_right _ _)⟩
  have hsI : s ∈ Ioo (-1 / 8 : ℝ) (1 / 8) := by
    constructor <;> linarith [hs.1, hs.2, hε016]
  have hρpos : 0 < ρ s := (B.shiftedSchoenfliesRadius_mem d D hsI).1
  have hρhalf : R / 2 < ρ s := by
    apply hδsub
    rw [mem_ball_zero_iff, Real.norm_eq_abs, abs_of_pos hs.1]
    exact hs.2.trans_le (min_le_left _ _)
  have houter : K (ρ s • q.1) = ρ s • (D.boundary_map q).1 :=
    radialDiffeomorph_pos_smul I q0 q hquarter hquarterhalf hρhalf.le
  have hinverse : K.symm (ρ s • (D.boundary_map q).1) = ρ s • q.1 := by
    rw [← houter, K.symm_apply_apply]
  change radiusVector f (K.symm (Ψ (B.punctureChart d (B.map ((1 + s) • q.1))))) =
    (1 / s) • q.1
  rw [show Ψ (B.punctureChart d (B.map ((1 + s) • q.1))) =
      ρ s • (D.boundary_map q).1 from B.shiftedSchoenfliesRadius_inverse d D Ψ hleft q hsI,
    hinverse]
  have hn : ‖ρ s • q.1‖ = ρ s := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hρpos,
      mem_sphere_zero_iff_norm.mp q.2, mul_one]
  rw [radiusVector, hn, hfend s hs0, smul_smul, div_mul_cancel₀ _ hρpos.ne']

end PoincareConjecture.SurgeryBallEmbedding
