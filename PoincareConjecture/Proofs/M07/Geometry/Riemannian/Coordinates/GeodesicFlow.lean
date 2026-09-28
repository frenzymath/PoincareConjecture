import PoincareConjecture.Proofs.M07.Analysis.ODE.LocalFlow.Smooth
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Geodesic








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped ContDiff

namespace PoincareConjecture

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]


theorem exists_smooth_coordinate_geodesic_flow
    {B : E → E →L[ℝ] E →L[ℝ] ℝ} {U : Set E} (hU : IsOpen U)
    (hB : ContDiffOn ℝ ∞ B U) (hinv : ∀ x ∈ U, (B x).IsInvertible)
    (hsymm : ∀ x ∈ U, ∀ u v, B x u v = B x v u)
    {x : E} (hx : x ∈ U) (v : E) :
    ∃ (V : Set (E × E)) (δ : ℝ) (Φ : (E × E) × ℝ → E × E),
      IsOpen V ∧ (x, v) ∈ V ∧ V ⊆ U ×ˢ univ ∧ 0 < δ ∧
      ContDiffOn ℝ ∞ Φ (V ×ˢ Ioo (-δ) δ) ∧
      (∀ z ∈ V, Φ (z, 0) = z) ∧
      (∀ z ∈ V, ∀ t ∈ Ioo (-δ) δ,
        (Φ (z, t)).1 ∈ U ∧
        HasDerivAt (fun s => Φ (z, s)) (coordinateGeodesicField B (Φ (z, t))) t ∧
        B (Φ (z, t)).1 (Φ (z, t)).2 (Φ (z, t)).2 = B z.1 z.2 z.2) := by
  have hfield : ContDiffOn ℝ ∞ (coordinateGeodesicField B) (U ×ˢ univ) := by
    intro z hz
    exact (contDiffAt_coordinateGeodesicField
      ((hB z.1 hz.1).contDiffAt (hU.mem_nhds hz.1))
      (hinv z.1 hz.1)).contDiffWithinAt
  obtain ⟨V, δ, Φ, hV, hzV, hVU, hδ, hΦ, hinit, hmaps, hderiv⟩ :=
    Poincare.ODE.LocalFlow.exists_smooth_localFlow (hU.prod isOpen_univ) hfield
      (show (x, v) ∈ U ×ˢ univ from ⟨hx, mem_univ _⟩)
  refine ⟨V, δ, Φ, hV, hzV, hVU, hδ, hΦ, hinit, ?_⟩
  intro z hz t ht
  refine ⟨(hmaps z hz t ht).1, hderiv z hz t ht, ?_⟩
  have henergy : ∀ s ∈ Ioo (-δ) δ,
      HasDerivAt (fun r => B (Φ (z, r)).1 (Φ (z, r)).2 (Φ (z, r)).2) 0 s := by
    intro s hs
    have hsU := (hmaps z hz s hs).1
    exact hasDerivAt_coordinate_geodesic_energy
      ((hB _ hsU).contDiffAt (hU.mem_nhds hsU) |>.differentiableAt (by simp))
      (hinv _ hsU) (hsymm _ hsU)
      (hderiv z hz s hs).fst (hderiv z hz s hs).snd
  have hconst := isOpen_Ioo.is_const_of_deriv_eq_zero (convex_Ioo (-δ) δ).isPreconnected
    (fun s hs => (henergy s hs).differentiableAt.differentiableWithinAt)
    (fun s hs => (henergy s hs).deriv) ht
    (show (0 : ℝ) ∈ Ioo (-δ) δ by constructor <;> linarith)
  simpa only [hinit z hz] using hconst

end PoincareConjecture

namespace PoincareConjecture.RiemannianMetric

open scoped Manifold



theorem exists_smooth_chart_geodesic_flow
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) (p : M) (v : EuclideanSpace ℝ (Fin n)) :
    let E := EuclideanSpace ℝ (Fin n)
    let c := extChartAt (𝓡 n) p
    let B := g.pullbackCoefficients c.symm
    ∃ (V : Set (E × E)) (δ : ℝ) (Φ : (E × E) × ℝ → E × E),
      IsOpen V ∧ (c p, v) ∈ V ∧ V ⊆ c.target ×ˢ univ ∧ 0 < δ ∧
      ContDiffOn ℝ ∞ Φ (V ×ˢ Ioo (-δ) δ) ∧
      (∀ z ∈ V, Φ (z, 0) = z) ∧
      (∀ z ∈ V, ∀ t ∈ Ioo (-δ) δ,
        (Φ (z, t)).1 ∈ c.target ∧
        HasDerivAt (fun s => Φ (z, s)) (coordinateGeodesicField B (Φ (z, t))) t ∧
        B (Φ (z, t)).1 (Φ (z, t)).2 (Φ (z, t)).2 = B z.1 z.2 z.2) := by
  exact exists_smooth_coordinate_geodesic_flow (isOpen_extChartAt_target (I := 𝓡 n) p)
    (g.contDiffOn_chartCoefficients p) (fun x hx => g.isInvertible_chartCoefficients p hx)
    (fun x _ u w => g.symm _ _ _) (mem_extChartAt_target p) v

end PoincareConjecture.RiemannianMetric
