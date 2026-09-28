import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.StrongNeckLocality
import PoincareConjecture.Proofs.M34.Mathlib.RoundCylinderParametrizedJets
import PoincareConjecture.Definitions.Ch11.SingularLimits

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M34

theorem generalizedCylinderPullback_roundCylinderTensorSmoothOn
    {G : GeneralizedRicciFlowData.{u}} {C : GeneralizedSliceCarrier.{u}}
    {origin scale : ℝ} {K : Set ℝ} {U : Set C.carrier}
    (e : GeneralizedFlowCylinder G C origin scale K U) (hU : IsOpen U)
    {epsilon : ℝ} {coordinate : RoundCylinderSpace → C.carrier}
    (hcoordinate : ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ coordinate
      (univ ×ˢ Ioo (-epsilon⁻¹) epsilon⁻¹))
    (hcapture : MapsTo coordinate (univ ×ˢ Ioo (-epsilon⁻¹) epsilon⁻¹) U)
    {s : ℝ} (hs : s ∈ K) :
    RoundCylinderTensorSmoothOn epsilon (generalizedCylinderPullback e coordinate s) := by
  have hcomp := (e.forward_smooth s hs).comp hcoordinate hcapture
  have hsmooth := roundCylinderTensorSmoothOn_smul_pullback
    (G.metric (origin + s / scale)) hcomp scale
  apply hsmooth.congr_cylinder
  intro z hz v w
  have hφ := (hcoordinate.contMDiffAt
    ((isOpen_univ.prod isOpen_Ioo).mem_nhds ⟨mem_univ _, hz⟩)).mdifferentiableAt (by simp)
  have he := ((e.forward_smooth s hs).contMDiffAt
    (hU.mem_nhds (hcapture ⟨mem_univ _, hz⟩))).mdifferentiableAt (by simp)
  simp only [generalizedCylinderPullback, dif_pos hs]
  change scale * (G.metric (origin + s / scale)).inner (e.forward s hs (coordinate z))
      (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ((e.forward s hs) ∘ coordinate) z v)
      (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ((e.forward s hs) ∘ coordinate) z w) =
    scale * (G.metric (origin + s / scale)).inner (e.forward s hs (coordinate z))
      ((mfderiv (𝓡 3) (𝓡 3) (e.forward s hs) (coordinate z))
        (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) coordinate z v))
      ((mfderiv (𝓡 3) (𝓡 3) (e.forward s hs) (coordinate z))
        (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) coordinate z w))
  rw [mfderiv_comp z he hφ]
  rfl

end PoincareConjecture.M34
