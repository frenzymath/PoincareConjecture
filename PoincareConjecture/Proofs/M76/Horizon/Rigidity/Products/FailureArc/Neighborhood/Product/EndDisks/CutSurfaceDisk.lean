import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Product.EndDisks.CutSurfaceLinks
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surfaces.Caps.OneBoundaryDisk

set_option autoImplicit false
open Set Geometry Geometry.SimplicialComplex
open PreAbstractSimplicialComplex.ModTwoCochains PoincareConjecture.M76.Dehn

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]

theorem closedFaceComplement_isFinitePLBallPair_of_circle_interface
    (K N : SimplicialComplex ℝ E) (hK : K.faces.Finite) (hNK : N ≤ K)
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, t.card = 3 ∧ s ⊆ t)
    (hNpure : ∀ s ∈ N.faces, ∃ t ∈ N.faces, t.card = 3 ∧ s ⊆ t)
    (hcofaces : ∀ s ∈ K.faces, s.card = 2 →
      {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ s ⊆ t}.ncard = 2)
    (hlinks : ∀ v ∈ K.vertices, IsConnected (K.link v).space)
    (hconn : IsConnected (K.closedFaceComplement N).space)
    (hKcount : K.surfaceEulerCount = 0) (hNcount : N.surfaceEulerCount = -1)
    (gamma : Metric.sphere (0 : Fin 2 → ℝ) 1 ≃ₜ
      (N ⊓ K.closedFaceComplement N).space) (hgamma : gamma.IsFinitePL) :
    IsFinitePLBallPair (ℝ × ℝ) (K.closedFaceComplement N).space
      (N ⊓ K.closedFaceComplement N).space := by
  obtain ⟨hC,hCpure,hClinks,hCboundary⟩ :=
    K.closedFaceComplement_incidence_of_circle_interface N hK hNK hpure hNpure
      hcofaces hlinks gamma hgamma
  have hLcount := (Annuli.circle_incidence (N ⊓ K.closedFaceComplement N)
    (hK.subset (fun _ hs ↦ hNK hs.1)) gamma hgamma).2.2.2.2
  have hcount : (K.closedFaceComplement N).surfaceEulerCount = 1 := by
    have heuler := K.closedFaceComplement_euler N hK hNK
    rw [hKcount,hNcount,hLcount] at heuler
    omega
  exact Annuli.isFinitePLBallPair_of_one_boundary_count_one
    (K.closedFaceComplement N) (N ⊓ K.closedFaceComplement N)
    hC hCpure (by convert hClinks using 1; congr!)
    hconn hcount inf_le_right gamma hgamma hCboundary

end Geometry.SimplicialComplex
