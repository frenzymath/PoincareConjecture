import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryNormalCoordinates
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Normed.Ring.Units












noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Function
open scoped Topology ContDiff

namespace PoincareConjecture

private theorem exists_local_inverse
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : E → E} {s : Set E} (hs : IsOpen s) (hf : ContDiffOn ℝ ∞ f s)
    {x : E} (hx : x ∈ s) (B : E ≃L[ℝ] E)
    (hd : HasFDerivAt f (B : E →L[ℝ] E) x) :
    ∃ H : OpenPartialHomeomorph E E, H.source ⊆ s ∧ x ∈ H.source ∧
      (H : E → E) = f ∧ ContDiffOn ℝ ∞ H H.source ∧
      ContDiffOn ℝ ∞ H.symm H.target := by
  have hfx := hf.contDiffAt (hs.mem_nhds hx)
  let H0 := hfx.toOpenPartialHomeomorph f hd (by simp)
  have hxH : x ∈ H0.source := hfx.mem_toOpenPartialHomeomorph_source hd (by simp)
  let t : Set E := (s ∩ H0.source) ∩ (fderiv ℝ f) ⁻¹' {L : E →L[ℝ] E | IsUnit L}
  have ht : IsOpen t := by
    apply ContinuousOn.isOpen_inter_preimage
    · exact (hf.continuousOn_fderiv_of_isOpen hs (by exact_mod_cast le_top)).mono
        inter_subset_left
    · exact hs.inter H0.open_source
    · exact Units.isOpen
  have hxt : x ∈ t := by
    refine ⟨⟨hx, hxH⟩, ?_⟩
    change IsUnit (fderiv ℝ f x)
    rw [hd.fderiv]
    exact ⟨B.toUnit, rfl⟩
  let H := H0.restrOpen t ht
  refine ⟨H, fun y hy => hy.2.1.1, ⟨hxH, hxt⟩, rfl,
    hf.mono (fun y hy => hy.2.1.1), ?_⟩
  intro y hy
  have hys := H.map_target hy
  have hyf : H.symm y ∈ s := hys.2.1.1
  have hyu : IsUnit (fderiv ℝ f (H.symm y)) := hys.2.2
  have hd' : HasFDerivAt f
      (ContinuousLinearEquiv.ofUnit hyu.unit : E →L[ℝ] E) (H.symm y) := by
    convert ((hf.contDiffAt (hs.mem_nhds hyf)).differentiableAt (by simp)).hasFDerivAt
      using 1
    exact ContinuousLinearMap.ext fun z => by
      simp [ContinuousLinearEquiv.ofUnit, IsUnit.unit_spec]
  exact (H.contDiffAt_symm hy hd' (hf.contDiffAt (hs.mem_nhds hyf))).contDiffWithinAt





theorem m64_exists_smooth_metric_normal_chart {n : ℕ}
    {c : ℝ → EuclideanSpace ℝ (Fin (n + 1))} {I : Set ℝ}
    (hI : IsOpen I) (h0 : 0 ∈ I) (hc : ContDiffOn ℝ ∞ c I)
    {U : Set (EuclideanSpace ℝ (Fin (n + 1)))} (hU : IsOpen U)
    (G : EuclideanSpace ℝ (Fin (n + 1)) →
      EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ]
        EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] ℝ)
    (hG : ContDiffOn ℝ ∞ G U) (hcU : MapsTo c I U)
    (hpos : ∀ t ∈ I, 0 < G (c t) (deriv c t) (deriv c t)) :
    ∃ H : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin (n + 1)))
        (EuclideanSpace ℝ (Fin (n + 1))),
      0 ∈ H.source ∧ H.target ⊆ U ∧ H 0 = c 0 ∧
      ContDiffOn ℝ ∞ H H.source ∧ ContDiffOn ℝ ∞ H.symm H.target ∧
      (∀ t : ℝ, H (EuclideanSpace.single 0 t) = c t) ∧
      (∀ t ∈ I, fderiv ℝ H (EuclideanSpace.single 0 t)
        (EuclideanSpace.single 0 1) = deriv c t) ∧
      (∀ t ∈ I, ∀ z : EuclideanSpace ℝ (Fin (n + 1)), z 0 = 0 →
        G (c t) (deriv c t) (fderiv ℝ H (EuclideanSpace.single 0 t) z) = 0) ∧
      ∀ t : ℝ, EuclideanSpace.single 0 t ∈ H.source →
        H.symm (c t) = EuclideanSpace.single 0 t := by
  let E := EuclideanSpace ℝ (Fin (n + 1))
  obtain ⟨F, B, hF, hd, haxis, htangent, hnormal⟩ :=
    m64_exists_smooth_metric_normal_coordinates hI h0 hc G hG hcU hpos
  let V : Set E := {z : E | z 0 ∈ I}
  have hV : IsOpen V := hI.preimage
    (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin (n + 1))).continuous
  let S := V ∩ F ⁻¹' U
  have hS : IsOpen S := hF.continuousOn.isOpen_inter_preimage hV hU
  have hF0 : F 0 = c 0 := by
    have hz : (EuclideanSpace.single 0 0 : E) = 0 := by ext i; simp
    simpa only [hz] using haxis 0
  have h0S : (0 : E) ∈ S := ⟨h0, by simpa only [mem_preimage, hF0] using hcU h0⟩
  obtain ⟨H, hHS, hH0, hHF, hHs, hHis⟩ :=
    exists_local_inverse hS (hF.mono inter_subset_left) h0S B hd
  refine ⟨H, hH0, ?_, ?_, hHs, hHis, ?_, ?_, ?_, ?_⟩
  · intro y hy
    have hh := (hHS (H.map_target hy)).2
    change F (H.symm y) ∈ U at hh
    rwa [← hHF, H.right_inv hy] at hh
  · rw [hHF, hF0]
  · simpa only [hHF] using haxis
  · simpa only [hHF] using htangent
  · simpa only [hHF] using hnormal
  · intro t ht
    rw [← haxis t, ← hHF]
    exact H.left_inv ht

end PoincareConjecture
