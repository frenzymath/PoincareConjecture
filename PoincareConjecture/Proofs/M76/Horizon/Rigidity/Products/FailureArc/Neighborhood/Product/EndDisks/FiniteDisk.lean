import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Product.EndDisks.FiniteInterface
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Product.EndDisks.CutSurfaceDisk
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Product.EndDisks.Purity.RelativeClosure

set_option autoImplicit false
open Set Geometry Topology Metric

namespace PoincareConjecture.M76.Dehn.Annuli.ProductEndDisks

theorem original_model_complementary_disk
    {X E V ι : Type*} [TopologicalSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [DecidableEq E]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {e : ι → OpenPartialHomeomorph X V}
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V)
    (K N : SimplicialComplex ℝ E) (hK : K.faces.Finite) (hNK : N ≤ K)
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, t.card = 3 ∧ s ⊆ t)
    (hcofaces : ∀ s ∈ K.faces, s.card = 2 →
      {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ s ⊆ t}.ncard = 2)
    (hlinks : ∀ v ∈ K.vertices, IsConnected (K.link v).space)
    (hKcount : K.surfaceEulerCount = 0) (hNcount : N.surfaceEulerCount = -1)
    {S Q A : Set X} (H : K.space ≃ₜ S) (a : E → X)
    (ha : PolyhedralPLInCharts e a K.space)
    (haval : ∀ x : K.space, a x = (H x : X)) (O : Set S)
    (hO : IsOpen O) (hconn : IsConnected Oᶜ)
    (hN : N.space = K.space ∩ a ⁻¹' Q)
    (hclosure : closure O = (Subtype.val : S → X) ⁻¹' Q)
    (hinterior : interior (closure O) = O)
    (hfrontier : frontier (closure O) = (Subtype.val : S → X) ⁻¹' A)
    (c : (Fin 2 → ℝ) → X) (hc : PolyhedralPLInCharts e c (sphere 0 1))
    (hci : InjOn c (sphere 0 1)) (hcS : MapsTo c (sphere 0 1) S)
    (hcA : c '' sphere 0 1 = A) :
    IsFinitePLBallPair (ℝ × ℝ) (K.closedFaceComplement N).space
        (N ⊓ K.closedFaceComplement N).space ∧
      PolyhedralPLInCharts e a (K.closedFaceComplement N).space ∧
      InjOn a (K.closedFaceComplement N).space ∧
      a '' (K.closedFaceComplement N).space = (Subtype.val : S → X) '' Oᶜ ∧
      a '' (N ⊓ K.closedFaceComplement N).space = A ∧
      ∃ γ : sphere (0 : Fin 2 → ℝ) 1 ≃ₜ (N ⊓ K.closedFaceComplement N).space,
        γ.IsFinitePL ∧ ∀ z, a (γ z) = c z := by
  classical
  have hOpre : (Subtype.val : S → X) ⁻¹' ((Subtype.val : S → X) '' O) = O :=
    preimage_image_eq _ Subtype.val_injective
  have hNpure := pure_of_original_open_closure K K N hK hNK hpure rfl H a haval
    (hOpre.symm ▸ hO) (by rw [hOpre]; exact hclosure) hN
  obtain ⟨hC,hT⟩ := closedComplement_original_carriers K N hK hNK H a haval O hN
    hclosure hinterior hfrontier
  have hCconn : IsConnected (K.closedFaceComplement N).space := by
    rw [hC]
    exact isConnected_original_model_carrier K H a haval hconn
  obtain ⟨γ,hγ,hγval⟩ := exists_original_finitePL_rim_model hcompat K
    (N ⊓ K.closedFaceComplement N) H a ha haval hT c hc hci hcS hcA
  have hball := K.closedFaceComplement_isFinitePLBallPair_of_circle_interface N hK hNK
    hpure hNpure hcofaces hlinks hCconn hKcount hNcount γ hγ
  have hCK := SimplicialComplex.space_subset_of_le (K.closedFaceComplement_le N)
  have hai : InjOn a K.space := by
    intro x hx y hy hxy
    exact congrArg Subtype.val (H.injective (Subtype.ext
      ((haval ⟨x,hx⟩).symm.trans (hxy.trans (haval ⟨y,hy⟩)))))
  refine ⟨hball,ha.restrict_finite _ (K.closedFaceComplement_finite N hK) hCK,
    hai.mono hCK,?_,?_,γ,hγ,hγval⟩
  · rw [hC]
    exact original_model_carrier_image K H a haval (by
      rintro y ⟨z,_,rfl⟩; exact z.property)
  · rw [hT]
    apply original_model_carrier_image K H a haval
    rw [← hcA]
    exact image_subset_iff.mpr hcS

end PoincareConjecture.M76.Dehn.Annuli.ProductEndDisks
