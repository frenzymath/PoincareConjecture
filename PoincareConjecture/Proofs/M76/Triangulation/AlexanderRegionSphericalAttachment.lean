import PoincareConjecture.Proofs.M76.Mathlib.BoundedRegionSphericalFrontier
import PoincareConjecture.Proofs.M76.Mathlib.BoundedRegionSphericalBall
import PoincareConjecture.Proofs.M76.Triangulation.PLDiskSurgeryModels











set_option autoImplicit false

open Set Geometry

namespace Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]






theorem alexander_nested_spherical_ball_attachment {b c d q U V C : Set E}
    (hb : IsFinitePLBallPair (ℝ × ℝ) b q)
    (hc : IsFinitePLBallPair (ℝ × ℝ) c q)
    (hd : IsFinitePLBallPair (ℝ × ℝ) d q)
    (hbc : b ∩ c = q) (hbd : b ∩ d = q) (hcd : c ∩ d = q)
    (hV : IsOpen V) (hUV : U ⊆ V) (hUC : closure U ⊆ C)
    (hUf : frontier U = b ∪ d) (hVf : frontier V = c ∪ d)
    (hUB : IsFinitePLBallPair ((ℝ × ℝ) × ℝ) (closure U) (b ∪ d))
    (hVE : IsFinitePLBallPair ((ℝ × ℝ) × ℝ)
      (frontier (C ×ˢ Icc (-1 : ℝ) 1) \ V ×ˢ {1}) ((c ∪ d) ×ˢ {1})) :
    IsFinitePLBallPair ((ℝ × ℝ) × ℝ)
      ((closure U ×ˢ {(1 : ℝ)}) ∪
        (frontier (C ×ˢ Icc (-1 : ℝ) 1) \ V ×ˢ {1})) ((b ∪ c) ×ˢ {1}) := by
  have hUb := hUB.prod_singleton (1 : ℝ)
  have hVb := hVE
  rw [union_prod] at hUb hVb
  have hbd' : (b ×ˢ {(1 : ℝ)}) ∩ (d ×ˢ {1}) = q ×ˢ {1} := by
    ext x
    have hx := Set.ext_iff.mp hbd x.1
    simp only [mem_inter_iff, mem_prod] at *
    tauto
  have hcd' : (c ×ˢ {(1 : ℝ)}) ∩ (d ×ˢ {1}) = q ×ˢ {1} := by
    ext x
    have hx := Set.ext_iff.mp hcd x.1
    simp only [mem_inter_iff, mem_prod] at *
    tauto
  have hinter := alexander_nested_region_inter_cylinderExterior
    hV hUV hUC hUf hVf hbc hd.1
  have hball := hUb.union_of_ball_disk_attachment hVb (hb.prod_singleton (1 : ℝ))
    (hc.prod_singleton (1 : ℝ)) (hd.prod_singleton (1 : ℝ)) hbd' hcd' hinter
  simpa only [union_prod] using hball

end Set
