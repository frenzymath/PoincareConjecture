import PoincareConjecture.Proofs.M09.CoordinateConnection
import PoincareConjecture.Proofs.M09.SquareChartPairing








set_option autoImplicit false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 800000

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

local notation "V" => EuclideanSpace ℝ (Fin n)

theorem chartVectorField_koszul {g : RiemannianMetric n M} (D : LeviCivitaData g)
    (p : M) (v w u : V) (x : M) (hx : x ∈ (chartAt V p).source) :
    2 * g.inner x (D.connection (chartVectorField p w) x (chartVectorField p v x))
        (chartVectorField p u x) =
      mvfderiv (𝓡 n) (fun y ↦ g.inner y (chartVectorField p w y) (chartVectorField p u y))
          x (chartVectorField p v x) +
        mvfderiv (𝓡 n) (fun y ↦ g.inner y (chartVectorField p v y) (chartVectorField p u y))
          x (chartVectorField p w x) -
        mvfderiv (𝓡 n) (fun y ↦ g.inner y (chartVectorField p v y) (chartVectorField p w y))
          x (chartVectorField p u x) := by
  have hV (a : V) := ((chartVectorField_smooth p a).contMDiffAt
    ((chartAt V p).open_source.mem_nhds hx)).mdifferentiableAt (by simp)
  have h := leviCivita_koszul_at D x (chartVectorField p v) (chartVectorField p w)
    (chartVectorField p u) (hV v) (hV w) (hV u)
  rw [chartVectorField_bracket p v w x hx, chartVectorField_bracket p w u x hx,
    chartVectorField_bracket p v u x hx] at h
  simpa only [map_zero, zero_apply, add_zero, sub_zero] using h

set_option backward.isDefEq.respectTransparency false in
theorem squareChartConnection_eq {J : Set ℝ} (F : RicciFlow n M J)
    (T b : ℝ) (hb : 0 < b) (hwindow : Set.Icc (T - b) T ⊆ J)
    (p : M) (s : ℝ) (hs : s ∈ Set.Ioo (-Real.sqrt b) (Real.sqrt b))
    (y : V) (hy : y ∈ (chartAt V p).target) (v w : V) :
    chartVectorField p (coordinateConnection (squareChartMetric F T p) (s, y) v w)
        ((chartAt V p).symm y) =
      (F.connection (T - s ^ 2)).connection (chartVectorField p w) ((chartAt V p).symm y)
        (chartVectorField p v ((chartAt V p).symm y)) := by
  let x := (chartAt V p).symm y
  let g := F.metric (T - s ^ 2)
  let D := F.connection (T - s ^ 2)
  let C := coordinateConnection (squareChartMetric F T p) (s, y) v w
  have hpair (u : V) :
      g.inner x (chartVectorField p C x) (chartVectorField p u x) =
        g.inner x (D.connection (chartVectorField p w) x (chartVectorField p v x))
          (chartVectorField p u x) := by
    have hΓ := coordinateConnection_pairing (squareChartMetric F T p) (s, y)
      (fun a ha ↦ squareChartMetric_pos F T p (s, y) hy a ha) v w u
    have hk := chartVectorField_koszul D p v w u x ((chartAt V p).map_target hy)
    rw [chartVectorField_at_inverse p v y hy, chartVectorField_at_inverse p w y hy,
      chartVectorField_at_inverse p u y hy] at hk
    rw [← squareChartMetric_space_pairing F T b hb hwindow p s hs y w u v hy,
      ← squareChartMetric_space_pairing F T b hb hwindow p s hs y v u w hy,
      ← squareChartMetric_space_pairing F T b hb hwindow p s hs y v w u hy] at hk
    change g.inner x ((mfderiv (𝓡 n) (𝓡 n) (chartAt V p).symm y) C)
      ((mfderiv (𝓡 n) (𝓡 n) (chartAt V p).symm y) u) = _ at hΓ
    dsimp only [x] at hk ⊢
    rw [chartVectorField_at_inverse p C y hy, chartVectorField_at_inverse p u y hy,
      chartVectorField_at_inverse p v y hy]
    linarith
  let δ : TangentSpace (𝓡 n) x := chartVectorField p C x -
    D.connection (chartVectorField p w) x (chartVectorField p v x)
  obtain ⟨u, hu⟩ := (inverseChartDifferential_bijective p y hy).2 δ
  have hzero : g.inner x δ δ = 0 := by
    have h := hpair u
    have hu' : chartVectorField p u x = δ :=
      (chartVectorField_at_inverse p u y hy).trans hu
    rw [hu'] at h
    change g.inner x (chartVectorField p C x -
      D.connection (chartVectorField p w) x (chartVectorField p v x)) δ = 0
    rw [map_sub (g.inner x), sub_apply, h, sub_self]
  have hδ : δ = 0 := by
    by_contra hne
    exact (ne_of_gt (g.pos x δ hne)) hzero
  exact sub_eq_zero.mp hδ

end PoincareConjecture.Proofs.M09
