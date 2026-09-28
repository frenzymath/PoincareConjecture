import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.SmoothDomain.Interior
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.Interior.Connected








set_option autoImplicit false

open Set
open scoped Manifold ContDiff

namespace Poincare.Manifold

theorem nonempty_smoothDomain_interior
    {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) M]
    [IsManifold (𝓡 (n + 1)) ∞ M] [PreconnectedSpace M] [NoncompactSpace M]
    {K : Set M} [ChartedSpace (EuclideanHalfSpace (n + 1)) K]
    [IsManifold (𝓡∂ (n + 1)) ∞ K]
    (hK : IsCompact K) (hconn : IsConnected K)
    (hemb : _root_.Manifold.IsSmoothEmbedding (𝓡∂ (n + 1)) (𝓡 (n + 1)) ∞
      (Subtype.val : K → M)) : Nonempty (SmoothDomain (n + 1) (interior K)) := by
  let : ConnectedSpace K := isConnected_iff_connectedSpace.mp hconn
  have himage := image_interior_of_isSmoothEmbedding hemb
  have hcl : closure (interior K) = K := by
    rw [← himage, hK.isClosed.isClosedEmbedding_subtypeVal.closure_image_eq,
      (dense_manifoldInterior (I := 𝓡∂ (n + 1)) (M := K)).closure_eq,
      image_univ, Subtype.range_val]
  have hi : IsConnected (interior K) := by
    rw [← himage]
    exact (isPathConnected_manifoldInterior (I := 𝓡∂ (n + 1)) (M := K)).isConnected.image
      _ continuous_subtype_val.continuousOn
  have hb : ((𝓡∂ (n + 1)).boundary K).Nonempty := by
    by_contra h
    have hinner : (𝓡∂ (n + 1)).interior K = univ := by
      rw [← compl_empty_iff, ModelWithCorners.compl_interior]
      exact not_nonempty_iff_eq_empty.mp h
    have hiK : interior K = K := by
      simpa only [hinner, image_univ, Subtype.range_val] using himage.symm
    have hopen : IsOpen K := hiK ▸ isOpen_interior
    have hKu : K = univ := (show IsClopen K from ⟨hK.isClosed, hopen⟩).eq_univ hconn.nonempty
    exact (not_compactSpace_iff.mpr ‹NoncompactSpace M›) (isCompact_univ_iff.mp (hKu ▸ hK))
  have ho : IsOpen (interior K) := isOpen_interior
  generalize hΩ : interior K = Ω at *
  cases hcl
  exact ⟨⟨ho, hi, hK, inferInstance, inferInstance, hemb, himage, hb⟩⟩

end Poincare.Manifold
