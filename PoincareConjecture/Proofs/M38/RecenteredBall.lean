import PoincareConjecture.Proofs.M38.BallCoordinatePatch
import PoincareConjecture.Proofs.M38.SmoothChart

set_option autoImplicit false

open Set Topology
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M38

theorem exists_surgeryBallAffineSubchart {A : GeneralizedSliceCarrier.{u}}
    (C : SurgeryBallEmbedding A) (p : A.carrier)
    (hpC : p ∈ C.map '' Metric.ball 0 2)
    {O : Set A.carrier} (hO : IsOpen O) (hpO : p ∈ O) :
    ∃ t : ℝ, 0 < t ∧ ∃ D : SurgeryBallEmbedding A,
      (∀ z, D.map z = C.map (C.inverse p + t • z)) ∧
      (∀ y, D.inverse y = t⁻¹ • (C.inverse y - C.inverse p)) ∧
      D.map 0 = p ∧ D.map '' Metric.ball 0 2 ⊆ O := by
  let a : StandardCapSpace := C.inverse p
  have hV : IsOpen (Metric.ball (0 : StandardCapSpace) 2 ∩ C.map ⁻¹' O) :=
    C.map_smooth.continuousOn.isOpen_inter_preimage Metric.isOpen_ball hO
  have haV : a ∈ Metric.ball (0 : StandardCapSpace) 2 ∩ C.map ⁻¹' O :=
    ⟨surgeryBall_inverse_mem C hpC, by
      change C.map (C.inverse p) ∈ O
      rwa [C.right_inverse hpC]⟩
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds haV)
  let t : ℝ := r / 4
  have ht : 0 < t := by dsimp only [t]; positivity
  let L : StandardCapSpace → StandardCapSpace := fun z => a + t • z
  let R : StandardCapSpace → StandardCapSpace := fun z => t⁻¹ • (z - a)
  have hL : ContMDiff (𝓡 3) (𝓡 3) ∞ L :=
    contMDiff_iff_contDiff.mpr (contDiff_const.add (contDiff_id.const_smul t))
  have hR : ContMDiff (𝓡 3) (𝓡 3) ∞ R :=
    contMDiff_iff_contDiff.mpr ((contDiff_id.sub contDiff_const).const_smul t⁻¹)
  have hLV {z : StandardCapSpace} (hz : z ∈ Metric.ball 0 2) :
      L z ∈ Metric.ball (0 : StandardCapSpace) 2 ∩ C.map ⁻¹' O := by
    apply hball
    have hz' : ‖z‖ < 2 := by simpa only [Metric.mem_ball, dist_zero_right] using hz
    change dist (a + t • z) a < r
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos ht]
    exact (mul_lt_mul_of_pos_left hz' ht).trans (by dsimp only [t]; linarith)
  let f : StandardCapSpace → A.carrier := C.map ∘ L
  let g : A.carrier → StandardCapSpace := R ∘ C.inverse
  have hf : ContMDiffOn (𝓡 3) (𝓡 3) ∞ f (Metric.ball 0 2) :=
    C.map_smooth.comp hL.contMDiffOn (fun _ hz => (hLV hz).1)
  have hsource : f '' Metric.ball 0 2 ⊆ C.map '' Metric.ball 0 2 := by
    rintro _ ⟨z, hz, rfl⟩
    exact Set.mem_image_of_mem C.map (hLV hz).1
  have hg : ContMDiffOn (𝓡 3) (𝓡 3) ∞ g (f '' Metric.ball 0 2) :=
    hR.comp_contMDiffOn (C.inverse_smooth.mono hsource)
  have hleft : Set.LeftInvOn g f (Metric.ball 0 2) := by
    intro z hz
    change t⁻¹ • (C.inverse (C.map (L z)) - a) = z
    rw [C.left_inverse (hLV hz).1]
    change t⁻¹ • (a + t • z - a) = z
    rw [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ ht.ne', one_smul]
  let D : SurgeryBallEmbedding A := {
    map := f
    inverse := g
    map_smooth := hf
    inverse_smooth := hg
    left_inverse := hleft
    right_inverse := by
      rintro _ ⟨z, hz, rfl⟩
      exact congrArg f (hleft hz)
    open_embedding := smooth_left_inverse_openEmbedding Metric.isOpen_ball hf hg hleft }
  refine ⟨t, ht, D, (fun _ => rfl), (fun _ => rfl), ?_, ?_⟩
  · change C.map (C.inverse p + t • 0) = p
    simpa only [smul_zero, add_zero] using C.right_inverse hpC
  · rintro _ ⟨z, hz, rfl⟩
    exact (hLV hz).2

end PoincareConjecture.M38
