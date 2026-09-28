import PoincareConjecture.Proofs.M76.Mathlib.BoundedRegionNestedExcision
import PoincareConjecture.Proofs.M76.Mathlib.BoundedRegionSphericalPartition
import PoincareConjecture.Proofs.M76.Triangulation.AlexanderRegionSphericalAttachment












set_option autoImplicit false

open Set Geometry

namespace Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]







theorem alexander_nested_spherical_ball_excision {b c d q U V D : Set E}
    (hdim : Module.finrank ℝ E = 3)
    (hb : IsFinitePLBallPair (ℝ × ℝ) b q)
    (hc : IsFinitePLBallPair (ℝ × ℝ) c q)
    (hd : IsFinitePLBallPair (ℝ × ℝ) d q)
    (hbc : b ∩ c = q) (hbd : b ∩ d = q) (hcd : c ∩ d = q)
    (hU : IsOpen U) (hV : IsOpen V) (hUV : U ⊆ V)
    (hVD : closure V ⊆ interior D)
    (hUf : frontier U = b ∪ d) (hVf : frontier V = c ∪ d)
    (hUB : IsFinitePLBallPair ((ℝ × ℝ) × ℝ) (closure U) (b ∪ d))
    (hVB : IsFinitePLBallPair ((ℝ × ℝ) × ℝ) (closure V) (c ∪ d))
    (hUE : IsFinitePLBallPair ((ℝ × ℝ) × ℝ)
      (frontier (D ×ˢ Icc (-1 : ℝ) 1) \ U ×ˢ {1}) ((b ∪ d) ×ˢ {1}))
    (hVE : IsFinitePLBallPair ((ℝ × ℝ) × ℝ)
      (frontier (D ×ˢ Icc (-1 : ℝ) 1) \ V ×ˢ {1}) ((c ∪ d) ×ˢ {1})) :
    IsFinitePLBallPair ((ℝ × ℝ) × ℝ)
      (closure (closure V \ closure U) ×ˢ {(1 : ℝ)}) ((b ∪ c) ×ˢ {1}) := by
  let S := frontier (D ×ˢ Icc (-1 : ℝ) 1)
  have hUD : closure U ⊆ D := (closure_mono hUV).trans (hVD.trans interior_subset)
  have hVD' : closure V ⊆ D := hVD.trans interior_subset
  have hUb := hUB.prod_singleton (1 : ℝ)
  have hVb := hVB.prod_singleton (1 : ℝ)
  have hUi := hUE
  have hVo := hVE
  rw [union_prod] at hUb hVb hUi hVo
  have hbd' : (b ×ˢ {(1 : ℝ)}) ∩ (d ×ˢ {1}) = q ×ˢ {1} := by
    rw [← inter_prod, hbd]
  have hcd' : (c ×ˢ {(1 : ℝ)}) ∩ (d ×ˢ {1}) = q ×ˢ {1} := by
    rw [← inter_prod, hcd]
  have hsi : (closure U ×ˢ {(1 : ℝ)}) ∩ (S \ U ×ˢ {1}) =
      (b ×ˢ {1}) ∪ (d ×ˢ {1}) := by
    rw [top_face_inter_cylinderExterior hU hUD, hUf, union_prod]
  have hbo : (closure V ×ˢ {(1 : ℝ)}) ∩ (S \ V ×ˢ {1}) =
      (c ×ˢ {1}) ∪ (d ×ˢ {1}) := by
    rw [top_face_inter_cylinderExterior hV hVD', hVf, union_prod]
  have hso : (closure U ×ˢ {(1 : ℝ)}) ∩ (S \ V ×ˢ {1}) = d ×ˢ {1} :=
    alexander_nested_region_inter_cylinderExterior hV hUV hUD hUf hVf hbc hd.1
  have hcover : (closure V ×ˢ {(1 : ℝ)}) ∪ (S \ V ×ˢ {1}) = S :=
    top_face_union_cylinderExterior hVD'
  have hball := hVb.excision_of_nested_spherical_balls hdim hVo hUb hUi
    (hb.prod_singleton (1 : ℝ)) (hc.prod_singleton (1 : ℝ))
    (hd.prod_singleton (1 : ℝ)) hbd' hcd'
    (prod_mono (closure_mono hUV) Subset.rfl)
    (sdiff_subset_sdiff_right (prod_mono hUV Subset.rfl)) hsi hbo hso
    hcover sdiff_subset (prod_mono hVD Subset.rfl)
  have hdiff : (closure V ×ˢ {(1 : ℝ)}) \ (closure U ×ˢ {1}) =
      (closure V \ closure U) ×ˢ {1} := by
    ext x
    simp only [mem_sdiff, mem_prod]
    tauto
  rw [hdiff, closure_prod_eq, isClosed_singleton.closure_eq] at hball
  simpa only [union_prod] using hball

end Set
