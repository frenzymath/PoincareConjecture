import PoincareConjecture.Proofs.M07.Analysis.ODE.CompactTrajectory
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.CompactEnergy
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Geodesic









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

namespace PoincareConjecture.RiemannianMetric



theorem exists_chart_geodesic_continuation
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) (p : M)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsCompact K)
    (hKU : K ⊆ (extChartAt (𝓡 n) p).target)
    {a b : ℝ} (hab : a < b)
    {q w : ℝ → EuclideanSpace ℝ (Fin n)}
    (hqK : ∀ t ∈ Ioo a b, q t ∈ K)
    (hq : ∀ t ∈ Ioo a b, HasDerivAt q (w t) t)
    (hw : ∀ t ∈ Ioo a b, HasDerivAt w
      (-coordinateChristoffel (g.pullbackCoefficients (extChartAt (𝓡 n) p).symm)
        (q t) (w t) (w t)) t) :
    ∃ δ > 0, ∃ q' w' : ℝ → EuclideanSpace ℝ (Fin n),
      EqOn q' q (Ioo a b) ∧ EqOn w' w (Ioo a b) ∧ q' b ∈ K ∧
      ∀ t ∈ Ioo a (b + δ),
        q' t ∈ (extChartAt (𝓡 n) p).target ∧ HasDerivAt q' (w' t) t ∧
        HasDerivAt w'
          (-coordinateChristoffel (g.pullbackCoefficients (extChartAt (𝓡 n) p).symm)
            (q' t) (w' t) (w' t)) t := by
  let E := EuclideanSpace ℝ (Fin n)
  let U := (extChartAt (𝓡 n) p).target
  let B := g.pullbackCoefficients (extChartAt (𝓡 n) p).symm
  have hU : IsOpen U := isOpen_extChartAt_target (I := 𝓡 n) p
  have hB : ContDiffOn ℝ ∞ B U := g.contDiffOn_chartCoefficients p
  have henergy : ∀ t ∈ Ioo a b, HasDerivAt (fun s => B (q s) (w s) (w s)) 0 t := by
    intro t ht
    have htU := hKU (hqK t ht)
    exact hasDerivAt_coordinate_geodesic_energy
      ((hB _ htU).contDiffAt (hU.mem_nhds htU) |>.differentiableAt (by simp))
      (g.isInvertible_chartCoefficients p htU) (fun u v => g.symm _ _ _)
      (hq t ht) (hw t ht)
  obtain ⟨t₀, ht₀⟩ := nonempty_Ioo.mpr hab
  let R := B (q t₀) (w t₀) (w t₀)
  let S : Set (E × E) := {z | z.1 ∈ K ∧ B z.1 z.2 z.2 ≤ R}
  have hS : IsCompact S := g.isCompact_chart_energy_sublevel p hK hKU R
  have hSU : S ⊆ U ×ˢ univ := fun z hz => ⟨hKU hz.1, mem_univ _⟩
  have hmem : ∀ t ∈ Ioo a b, (q t, w t) ∈ S := by
    intro t ht
    refine ⟨hqK t ht, le_of_eq ?_⟩
    exact isOpen_Ioo.is_const_of_deriv_eq_zero (convex_Ioo a b).isPreconnected
      (fun s hs => (henergy s hs).differentiableAt.differentiableWithinAt)
      (fun s hs => (henergy s hs).deriv) ht ht₀
  have hfield : ContDiffOn ℝ ∞ (coordinateGeodesicField B) (U ×ˢ univ) := by
    intro z hz
    exact (contDiffAt_coordinateGeodesicField
      ((hB z.1 hz.1).contDiffAt (hU.mem_nhds hz.1))
      (g.isInvertible_chartCoefficients p hz.1)).contDiffWithinAt
  obtain ⟨δ, hδ, η, heq, hηb, hηU, hη⟩ :=
    Poincare.ODE.exists_continuation_of_compact_trajectory (hU.prod isOpen_univ)
      hS hSU hfield hab hmem (fun t ht => (hq t ht).prodMk (hw t ht))
  exact ⟨δ, hδ, fun t => (η t).1, fun t => (η t).2,
    fun t ht => congrArg Prod.fst (heq ht), fun t ht => congrArg Prod.snd (heq ht),
    hηb.1, fun t ht => ⟨(hηU t ht).1, (hη t ht).fst, (hη t ht).snd⟩⟩

end PoincareConjecture.RiemannianMetric
