import PoincareConjecture.Definitions.Ch15.SurgeryTopology
import PoincareConjecture.Proofs.M38.SmoothChart

set_option autoImplicit false

open Set Topology Metric
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M38

theorem exists_surgeryBall_in_open (A : GeneralizedSliceCarrier.{u})
    (p : A.carrier) {O : Set A.carrier} (hO : IsOpen O) (hp : p ∈ O) :
    ∃ B : SurgeryBallEmbedding A, B.map 0 = p ∧
      B.map '' Metric.ball 0 2 ⊆ O ∧ B.closedBall ⊆ O := by
  let c := chartAt StandardCapSpace p
  have hcp : p ∈ c.source := mem_chart_source _ p
  have hV : IsOpen (c.target ∩ c.symm ⁻¹' O) := c.symm.isOpen_inter_preimage hO
  have hpoint : c p ∈ c.target ∩ c.symm ⁻¹' O := by
    refine ⟨c.map_source hcp, ?_⟩
    change c.symm (c p) ∈ O
    rwa [c.left_inv hcp]
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds hpoint)
  let a : ℝ := r / 4
  have ha : 0 < a := by dsimp only [a]; positivity
  let L : StandardCapSpace → StandardCapSpace := fun z => c p + a • z
  let R : StandardCapSpace → StandardCapSpace := fun z => a⁻¹ • (z - c p)
  have hL : ContMDiff (𝓡 3) (𝓡 3) ∞ L :=
    contMDiff_iff_contDiff.mpr (contDiff_const.add (contDiff_id.const_smul a))
  have hR : ContMDiff (𝓡 3) (𝓡 3) ∞ R :=
    contMDiff_iff_contDiff.mpr ((contDiff_id.sub contDiff_const).const_smul a⁻¹)
  have hLV {z : StandardCapSpace} (hz : z ∈ Metric.ball 0 2) :
      L z ∈ c.target ∩ c.symm ⁻¹' O := by
    apply hball
    have hz' : ‖z‖ < 2 := by simpa only [Metric.mem_ball, dist_zero_right] using hz
    change dist (c p + a • z) (c p) < r
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos ha]
    calc
      a * ‖z‖ < a * 2 := mul_lt_mul_of_pos_left hz' ha
      _ < r := by dsimp only [a]; linarith
  let f : StandardCapSpace → A.carrier := c.symm ∘ L
  let g : A.carrier → StandardCapSpace := R ∘ c
  have hf : ContMDiffOn (𝓡 3) (𝓡 3) ∞ f (Metric.ball 0 2) :=
    contMDiffOn_chart_symm.comp hL.contMDiffOn (fun _ hz => (hLV hz).1)
  have hsource : f '' Metric.ball 0 2 ⊆ c.source := by
    rintro _ ⟨z, hz, rfl⟩
    exact c.map_target (hLV hz).1
  have hg : ContMDiffOn (𝓡 3) (𝓡 3) ∞ g (f '' Metric.ball 0 2) :=
    hR.comp_contMDiffOn (contMDiffOn_chart.mono hsource)
  have hleft : Set.LeftInvOn g f (Metric.ball 0 2) := by
    intro z hz
    change a⁻¹ • (c (c.symm (L z)) - c p) = z
    rw [c.right_inv (hLV hz).1]
    change a⁻¹ • (c p + a • z - c p) = z
    rw [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ ha.ne', one_smul]
  let B : SurgeryBallEmbedding A := {
    map := f
    inverse := g
    map_smooth := hf
    inverse_smooth := hg
    left_inverse := hleft
    right_inverse := by
      rintro _ ⟨z, hz, rfl⟩
      exact congrArg f (hleft hz)
    open_embedding := smooth_left_inverse_openEmbedding Metric.isOpen_ball hf hg hleft }
  have himage : B.map '' Metric.ball 0 2 ⊆ O := by
    rintro _ ⟨z, hz, rfl⟩
    exact (hLV hz).2
  refine ⟨B, ?_, himage, ?_⟩
  · change c.symm (c p + a • 0) = p
    simpa only [smul_zero, add_zero] using c.left_inv hcp
  · exact (Set.image_mono (Metric.closedBall_subset_ball (by norm_num))).trans himage

end PoincareConjecture.M38
