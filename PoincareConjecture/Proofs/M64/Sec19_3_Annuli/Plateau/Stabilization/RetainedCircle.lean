import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Stabilization.RadialLift











set_option autoImplicit false

noncomputable section

open Set
open scoped Manifold ContDiff

namespace PoincareConjecture.M64

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Icc a b)} {circumference auxiliary : ℝ}



theorem auxiliaryCircle_section_retains_original_degree
    (P : M62.CircleProductData F circumference)
    (Q : M62.CircleProductData P.flow auxiliary) (q : Q.circle.Point)
    {c : ℝ → P.charts.Point} (L : M63PositiveDegreeLift P c) :
    ∃ D : M63PositiveDegreeLift P (fun x => (auxiliaryCircleSection Q q (c x)).1),
      D.degree = L.degree ∧ D.lift = L.lift :=
  ⟨L, rfl, rfl⟩



theorem auxiliaryCircle_radial_retained_projection
    (P : M62.CircleProductData F circumference)
    (f : LoopPlane → M) (delta : ℝ) :
    (fun z => (auxiliaryCircleRadialLift P f delta z).1) = f := rfl



theorem auxiliaryCircle_radial_retains_original_circle
    (P : M62.CircleProductData F circumference)
    (Q : M62.CircleProductData P.flow auxiliary)
    (f : LoopPlane → P.charts.Point) (delta : ℝ) :
    (fun z => (auxiliaryCircleRadialLift Q f delta z).1.2) = fun z => (f z).2 := rfl

end PoincareConjecture.M64
