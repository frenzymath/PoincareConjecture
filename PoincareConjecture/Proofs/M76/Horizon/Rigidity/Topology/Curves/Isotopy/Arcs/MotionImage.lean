import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Curves.Isotopy.Disks.SupportedExtension
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLImageTriangulation



set_option autoImplicit false
open Set Geometry unitInterval

namespace PoincareConjecture.M76.Dehn

theorem finitePL_curve_after_joint_motion {q : ℝ → ℝ × ℝ}
    (hq : FinitePiecewiseAffineOn q (Icc 0 1))
    (H : I → (ℝ × ℝ) ≃ₜ (ℝ × ℝ)) (F : (ℝ × (ℝ × ℝ)) → ℝ × ℝ)
    (hF : ∀ K : SimplicialComplex ℝ (ℝ × ℝ), K.faces.Finite →
      FinitePiecewiseAffineOn F (Icc (0 : ℝ) 1 ×ˢ K.space))
    (hv : ∀ t : I, ∀ x : ℝ × ℝ, F ((t : ℝ), x) = H t x) (t : I) :
    FinitePiecewiseAffineOn (fun x => H t (q x)) (Icc 0 1) := by
  obtain ⟨K, hK, hKs⟩ := hq.exists_finite_triangulation_image
  have hqcopy := hq
  obtain ⟨L, hL, hLs, _⟩ := hqcopy
  have ht : FinitePiecewiseAffineOn (fun _ : ℝ => (t : ℝ)) (Icc 0 1) :=
    ⟨L, hL, hLs, L.affineOnFaces_affine (ContinuousAffineMap.const ℝ ℝ (t : ℝ))⟩
  have hc := (hF K hK).comp (ht.prod_mk hq) (show MapsTo (fun x => ((t : ℝ), q x))
      (Icc (0 : ℝ) 1) (Icc (0 : ℝ) 1 ×ˢ K.space) from fun x hx =>
    ⟨t.property, hKs.symm ▸ mem_image_of_mem q hx⟩)
  simpa only [Function.comp_def, hv] using hc

end PoincareConjecture.M76.Dehn
