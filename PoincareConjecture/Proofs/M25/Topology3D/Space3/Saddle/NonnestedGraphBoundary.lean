import PoincareConjecture.Proofs.M25.Topology3D.Space3.Base.StackOfDiscsFamily











set_option autoImplicit false

open Set Metric
open scoped ContDiff Manifold

namespace PoincareConjecture.M25.Topology3D

namespace PlanarFamilyGraphChart

variable {c : ℝ → UnitCircle → E2} {a b : ℝ}
variable {D : PlanarSchoenfliesFamilyData c a b}
variable (G : PlanarFamilyGraphChart D)



theorem ambientChart_image (u : UnitTwoSphere) (z : ℝ) (X : Set E2) :
    G.ambientChart u '' (X ×ˢ ({z} : Set ℝ)) =
      (heightPlaneCoordinates u).symm '' ((D.chart z '' X) ×ˢ ({z} : Set ℝ)) := by
  ext y
  constructor
  · rintro ⟨p, ⟨hp, hz⟩, rfl⟩
    rcases p with ⟨x, t⟩
    have ht : t = z := by simpa using hz
    subst t
    refine ⟨(D.chart z x, z), ⟨⟨x, hp, rfl⟩, rfl⟩, ?_⟩
    exact (G.ambientChart_apply u (x, z)).symm
  · rintro ⟨p, hp, hpoint⟩
    rcases p with ⟨y, t⟩
    rcases hp with ⟨hy, hz⟩
    rcases hy with ⟨x, hx, hxy⟩
    have ht : t = z := by simpa using hz
    subst t
    refine ⟨(x, z), ⟨hx, rfl⟩, ?_⟩
    rw [G.ambientChart_apply, hxy]
    simpa only [Prod.fst, Prod.snd] using hpoint



theorem ambientChart_boundary_image (u : UnitTwoSphere) (z : ℝ)
    (hz : z ∈ Icc a b) :
    G.ambientChart u '' (sphere (0 : E2) 1 ×ˢ ({z} : Set ℝ)) =
      (heightPlaneCoordinates u).symm '' (range (c z) ×ˢ ({z} : Set ℝ)) := by
  have hcircle : D.chart z '' sphere (0 : E2) 1 = range (c z) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, (D.chart_boundary z hz ⟨x, hx⟩).symm⟩
    · rintro ⟨q, rfl⟩
      exact ⟨q.1, q.2, D.chart_boundary z hz q⟩
  rw [G.ambientChart_image, hcircle]

end PlanarFamilyGraphChart

end PoincareConjecture.M25.Topology3D
