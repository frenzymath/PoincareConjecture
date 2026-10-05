import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Lifetime.CanonicalGeometry.StrongNeckLocality
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Analysis.Coordinates.RoundCylinderParametrizedJets
import PoincareLib.Geometry.RicciFlow.Surgery.Singular.Geometry

/-!
# Smoothness of actual captured generalized cylinder pullbacks

The actual forward map composed with the cylinder coordinate gives an
ordinary metric pullback. Its derivative chain rule is precisely the
frozen generalized pullback. Source: Morgan-Tian Theorem 12.28,
pp. 323-324, and the source-smoothness step of the owned derivation.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareMT.M34

/-- A smooth coordinate whose actual image is captured gives the
frozen coefficient smoothness of the generalized pullback at every
included time, including either endpoint. -/
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

end PoincareMT.M34
