import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallTopology
import Mathlib.Analysis.Normed.Module.Convex

set_option autoImplicit false

open Set Metric

namespace Set

variable {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup X] [NormedSpace ℝ X] {d b : Set X}

theorem IsFinitePLBallPair.exists_preconnected_sdiff_neighborhood
    (hd : IsFinitePLBallPair E d b) {p : X} (hpd : p ∈ d)
    {U : Set X} (hU : IsOpen U) (hpU : p ∈ U) :
    ∃ V : Set X, IsOpen V ∧ p ∈ V ∧ V ⊆ U ∧ IsPreconnected ((d \ b) ∩ V) := by
  obtain ⟨_, C, hC, hcv, _, e, _, heb⟩ := hd
  let z : C := e ⟨p, hpd⟩
  let O : Set C := e.symm ⁻¹' ((Subtype.val : d → X) ⁻¹' U)
  have hO : IsOpen O := (hU.preimage continuous_subtype_val).preimage e.symm.continuous
  have hzO : z ∈ O := by simpa [O, z] using hpU
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hO z hzO
  have hrel : IsOpen (e ⁻¹' ball z ε) := isOpen_ball.preimage e.continuous
  obtain ⟨W, hW, hWeq⟩ := isOpen_induced_iff.mp hrel
  have hWmem (x : d) : (x : X) ∈ W ↔ e x ∈ ball z ε := Set.ext_iff.mp hWeq x
  have hpW : p ∈ W := (hWmem ⟨p, hpd⟩).mpr (mem_ball_self hε)
  let V := W ∩ U
  let I : Set C := (Subtype.val : C → E) ⁻¹' (interior C ∩ ball (z : E) ε)
  have hIimage : (Subtype.val : C → E) '' I = interior C ∩ ball (z : E) ε :=
    image_preimage_eq_of_subset (by
      rintro x ⟨hx, _⟩
      exact ⟨⟨x, interior_subset hx⟩, rfl⟩)
  have hI : IsPreconnected I := by
    apply Topology.IsInducing.subtypeVal.isPreconnected_image.mp
    rw [hIimage]
    exact (hcv.interior.inter (convex_ball _ _)).isPreconnected
  let g : C → X := fun y => e.symm y
  have hg : Continuous g := continuous_subtype_val.comp e.symm.continuous
  have hgI : g '' I = (d \ b) ∩ V := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hyint : (y : E) ∈ interior C := hy.1
      have hyball : y ∈ ball z ε := hy.2
      have hnotb : (e.symm y : X) ∉ b := by
        intro hb
        have hfront := (heb (e.symm y)).mp hb
        rw [e.apply_symm_apply] at hfront
        exact hfront.2 hyint
      refine ⟨⟨(e.symm y).property, hnotb⟩, ?_, hball hyball⟩
      exact (hWmem (e.symm y)).mpr (by simpa using hyball)
    · rintro ⟨⟨hxd, hxb⟩, hxW, hxU⟩
      let y : C := e ⟨x, hxd⟩
      have hyint : (y : E) ∈ interior C := by
        by_contra hni
        exact hxb ((heb ⟨x, hxd⟩).mpr ⟨subset_closure y.property, hni⟩)
      refine ⟨y, ⟨hyint, (hWmem ⟨x, hxd⟩).mp hxW⟩, ?_⟩
      simp [g, y]
  refine ⟨V, hW.inter hU, ⟨hpW, hpU⟩, inter_subset_right, ?_⟩
  rw [← hgI]
  exact hI.image g hg.continuousOn

end Set
