import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Geodesic
import PoincareConjecture.Proofs.M09.SquareChartConnection

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

open Filter
open scoped Manifold ContDiff Topology Bundle

namespace PoincareConjecture.M63

open Proofs.M09

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

local notation "E" => EuclideanSpace ℝ (Fin n)

theorem chartCoefficients_derivative_pairing (g : RiemannianMetric n M)
    (p : M) (y u v w : E) (hy : y ∈ (chartAt E p).target) :
    fderiv ℝ (g.pullbackCoefficients (chartAt E p).symm) y w u v =
      mvfderiv (𝓡 n)
        (fun x => g.inner x (chartVectorField p u x) (chartVectorField p v x))
        ((chartAt E p).symm y) (chartVectorField p w ((chartAt E p).symm y)) := by
  let f : M → ℝ := fun x =>
    g.inner x (chartVectorField p u x) (chartVectorField p v x)
  have hf : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) f ((chartAt E p).symm y) :=
    ((chartMetricPairing_smooth g p u v).contMDiffAt
      ((chartAt E p).open_source.mem_nhds ((chartAt E p).map_target hy))).mdifferentiableAt
      (by simp)
  have hchain := mvfderiv_chartVectorField p f y w hy hf
  have heq : (fun z : E => f ((chartAt E p).symm z)) =ᶠ[𝓝 y]
      (fun z => g.pullbackCoefficients (chartAt E p).symm z u v) := by
    filter_upwards [(chartAt E p).open_target.mem_nhds hy] with z hz
    dsimp [f]
    rw [chartVectorField_at_inverse p u z hz, chartVectorField_at_inverse p v z hz]
    rfl
  rw [heq.fderiv_eq] at hchain
  have hB := (g.contDiffAt_pullbackCoefficients
    ((contMDiffOn_chart_symm (I := 𝓡 n) (x := p)).contMDiffAt
      ((chartAt E p).open_target.mem_nhds hy))).differentiableAt (by simp)
  have heval := (hB.hasFDerivAt.clm_apply (hasFDerivAt_const u y)).clm_apply
    (hasFDerivAt_const v y)
  have hcoord : fderiv ℝ
      (fun z => g.pullbackCoefficients (chartAt E p).symm z u v) y w =
      fderiv ℝ (g.pullbackCoefficients (chartAt E p).symm) y w u v := by
    simpa using congrArg (fun L : E →L[ℝ] ℝ => L w) heval.fderiv
  exact hcoord.symm.trans hchain.symm

theorem chartVectorField_coordinateChristoffel {g : RiemannianMetric n M}
    (D : LeviCivitaData g) (p : M) (y : E) (hy : y ∈ (chartAt E p).target)
    (v w : E) :
    chartVectorField p
        (coordinateChristoffel (g.pullbackCoefficients (chartAt E p).symm) y v w)
        ((chartAt E p).symm y) =
      D.connection (chartVectorField p w) ((chartAt E p).symm y)
        (chartVectorField p v ((chartAt E p).symm y)) := by
  let x := (chartAt E p).symm y
  let B := g.pullbackCoefficients (chartAt E p).symm
  let C := coordinateChristoffel B y v w
  have hinv := g.isInvertible_pullbackCoefficients
    (inverseChartDifferential_bijective p y hy).1
  have hpair (u : E) :
      g.inner x (chartVectorField p C x) (chartVectorField p u x) =
        g.inner x (D.connection (chartVectorField p w) x (chartVectorField p v x))
          (chartVectorField p u x) := by
    have hG : B y C u = (2⁻¹ : ℝ) *
        (fderiv ℝ B y v w u + fderiv ℝ B y w u v - fderiv ℝ B y u v w) := by
      simpa [C, coordinateChristoffel, metricKoszulCovector] using
        congrArg (fun L : E →L[ℝ] ℝ => L u)
          (hinv.self_apply_inverse (metricKoszulCovector (fderiv ℝ B y) v w))
    have hk := chartVectorField_koszul D p v w u x ((chartAt E p).map_target hy)
    have hsym : (fun z => g.inner z (chartVectorField p u z) (chartVectorField p v z)) =
        (fun z => g.inner z (chartVectorField p v z) (chartVectorField p u z)) :=
      funext fun z => g.symm z _ _
    dsimp only [B] at hG
    rw [chartCoefficients_derivative_pairing g p y w u v hy,
      chartCoefficients_derivative_pairing g p y u v w hy,
      chartCoefficients_derivative_pairing g p y v w u hy, hsym] at hG
    change g.inner x (mfderiv (𝓡 n) (𝓡 n) (chartAt E p).symm y C)
      (mfderiv (𝓡 n) (𝓡 n) (chartAt E p).symm y u) = _ at hG
    have hframe : g.inner x (chartVectorField p C x) (chartVectorField p u x) =
        g.inner x (mfderiv (𝓡 n) (𝓡 n) (chartAt E p).symm y C)
          (mfderiv (𝓡 n) (𝓡 n) (chartAt E p).symm y u) := by
      rw [chartVectorField_at_inverse p C y hy, chartVectorField_at_inverse p u y hy]
    rw [hframe]
    linarith
  let delta : TangentSpace (𝓡 n) x := chartVectorField p C x -
    D.connection (chartVectorField p w) x (chartVectorField p v x)
  obtain ⟨u, hu⟩ := (inverseChartDifferential_bijective p y hy).2 delta
  have hzero : g.inner x delta delta = 0 := by
    have h := hpair u
    have hu' : chartVectorField p u x = delta :=
      (chartVectorField_at_inverse p u y hy).trans hu
    rw [hu'] at h
    change g.inner x (chartVectorField p C x -
      D.connection (chartVectorField p w) x (chartVectorField p v x)) delta = 0
    rw [map_sub (g.inner x), sub_apply, h, sub_self]
  have hdelta : delta = 0 := by
    by_contra hne
    exact (ne_of_gt (g.pos x delta hne)) hzero
  exact sub_eq_zero.mp hdelta

end PoincareConjecture.M63
