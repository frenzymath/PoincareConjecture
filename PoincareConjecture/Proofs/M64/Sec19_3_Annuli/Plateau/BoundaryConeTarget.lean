import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryConeVectorGreen

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped Topology Manifold ContDiff

namespace PoincareConjecture.M64BoundaryCone

open M65Interior M65Boundary Proofs.M58

theorem coneDiskCoordinates_mem {C : Type*} [NormedAddCommGroup C] [NormedSpace ℝ C]
    {v : ℝ → C} {v0 : C} {r rho : ℝ} (hr : 0 < r)
    (h0 : v0 ∈ closedBall 0 rho)
    (hvb : MapsTo v (Icc (0 : ℝ) Real.pi) (closedBall 0 rho))
    {x z : LoopPlane} (hz : z ∈ closedBall x r ∩ {z | x 1 ≤ z 1}) :
    coneCoordinates r v0 v (polarCoordinates x z).1 (polarCoordinates x z).2 ∈
      closedBall 0 rho := by
  rw [← polarCoordinates_preimage_halfRectangle] at hz
  exact coneCoordinates_mem_closedBall hr h0 (hvb hz.2) hz.1

theorem coneDiskMap_observation {C M : Type*} [NormedAddCommGroup C] [NormedSpace ℝ C]
    {P : C → M} {beta : C → ℝ} {obs : M → LoopPlane} {k : ℝ}
    {v : ℝ → C} {v0 : C} {r rho : ℝ} (hr : 0 < r)
    (h0 : v0 ∈ closedBall 0 rho)
    (hvb : MapsTo v (Icc (0 : ℝ) Real.pi) (closedBall 0 rho))
    (hobs : ∀ y ∈ closedBall 0 rho, obs (P y) = angularPoint (k * beta y))
    {x z : LoopPlane} (hz : z ∈ closedBall x r ∩ {z | x 1 ≤ z 1}) :
    obs (coneDiskMap P r v0 v x z) = angularPoint (k * coneDiskMap beta r v0 v x z) :=
  hobs _ (coneDiskCoordinates_mem hr h0 hvb hz)

theorem coneDiskField_tangent {n m N : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {P : EuclideanSpace ℝ (Fin N) → M} {e : M → EuclideanSpace ℝ (Fin m)}
    {v d : ℝ → EuclideanSpace ℝ (Fin N)} {v0 : EuclideanSpace ℝ (Fin N)}
    {r rho : ℝ} (hr : 0 < r) (hrho : 0 < rho)
    (he : ContMDiff (𝓡 n) (𝓡 m) 1 e)
    (hP : ContMDiffOn (𝓡 N) (𝓡 n) 1 P (ball 0 (2 * rho)))
    (h0 : v0 ∈ closedBall 0 rho)
    (hvb : MapsTo v (Icc (0 : ℝ) Real.pi) (closedBall 0 rho))
    {x z : LoopPlane} (hz : z ∈ closedBall x r ∩ {z | x 1 ≤ z 1}) (i : Fin 2) :
    coneDiskField (e ∘ P) r v0 v d x i z ∈
      range (mfderiv (𝓡 n) (𝓡 m) e (coneDiskMap P r v0 v x z)) := by
  let p := polarCoordinates x z
  let y := coneCoordinates r v0 v p.1 p.2
  have hy : y ∈ ball 0 (2 * rho) :=
    (closedBall_subset_ball (by linarith)) (coneDiskCoordinates_mem hr h0 hvb hz)
  have hPd := (hP.contMDiffAt (isOpen_ball.mem_nhds hy)).mdifferentiableAt one_ne_zero
  have hD : fderiv ℝ (e ∘ P) y =
      (mfderiv (𝓡 n) (𝓡 m) e (P y)).comp (mfderiv (𝓡 N) (𝓡 n) P y) := by
    rw [← mfderiv_eq_fderiv]
    exact mfderiv_comp y ((he (P y)).mdifferentiableAt one_ne_zero) hPd
  refine ⟨r⁻¹ • (angularPoint p.2 i • mfderiv (𝓡 N) (𝓡 n) P y (v p.2 - v0) +
    angularVector p.2 i • mfderiv (𝓡 N) (𝓡 n) P y (d p.2)), ?_⟩
  change _ = r⁻¹ • (angularPoint p.2 i • fderiv ℝ (e ∘ P) y (v p.2 - v0) +
    angularVector p.2 i • fderiv ℝ (e ∘ P) y (d p.2))
  simp only [hD, map_smul, map_add]
  rfl

end PoincareConjecture.M64BoundaryCone
