import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Descent.Source.InteriorCharts
import PoincareConjecture.Proofs.M76.Mathlib.AffineHyperplaneCoordinates









set_option autoImplicit false

open Set Metric Geometry Topology

namespace PoincareConjecture.M76.Dehn.ProtectedAnnulus

local notation "V1" => (Fin 1 → ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V" => (V1 × V2)



theorem exists_interior_source_parameters (x : source)
    (hxr : (x : V).1 ∉ sphere (0 : V1) 1) :
    ∃ (q : OpenPartialHomeomorph source V2) (O : Set V) (F : V → V2),
      x ∈ q.source ∧ IsOpen O ∧ q.source = Subtype.val ⁻¹' O ∧
      O ⊆ ball (0 : V1) 1 ×ˢ (univ : Set V2) ∧
      (∀ y : source, q y = F y) ∧ LocallyPiecewiseAffineOn F O ∧
      LocallyPiecewiseAffineOn (fun z ↦ (q.symm z : V)) q.target := by
  obtain ⟨H, B, hxH, _, hB, hHO, hHPL, hHiPL, hsource⟩ :=
    exists_interior_source_chart x.property hxr
  obtain ⟨a, r, hra, har, ha⟩ := B.toAffineMap.exists_zeroLevel_coordinates
    hB (F := V2) (by simp [Module.finrank_prod])
  let ell : V →ᴬ[ℝ] ℝ := ⟨B.toAffineMap, B.continuous_of_finiteDimensional⟩
  have himage : H.IsImage source {z | ell z = 0} :=
    fun {y} hy ↦ (hsource y hy).symm
  obtain ⟨q, hqs, hqt, hqval, hqinv⟩ :=
    H.exists_affine_hypersurface_chart ell himage a r hra har ha x
  have hF : LocallyPiecewiseAffineOn (r ∘ H) H.source :=
    ((locallyPiecewiseAffineOn_affine r isOpen_univ).comp hHPL).mono H.open_source
      (fun _ hz ↦ ⟨hz, mem_univ _⟩)
  have hi : LocallyPiecewiseAffineOn (H.symm ∘ a) q.target :=
    (hHiPL.comp (locallyPiecewiseAffineOn_affine a isOpen_univ)).mono q.open_target
      (fun z hz ↦ ⟨mem_univ _, hqt.subset hz⟩)
  exact ⟨q, H.source, r ∘ H, hqs.symm.subset hxH, H.open_source, hqs, hHO,
    hqval, hF, hi.congr (fun z hz ↦ (hqinv z hz).symm)⟩

end PoincareConjecture.M76.Dehn.ProtectedAnnulus
