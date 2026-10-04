import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.ParameterPrismDomain
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Regions.FinitePLBallNormalization
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.General.FinitePLSubsets

/-!
# Complete finite carriers for a cube prism and its boundary

The entire lateral cylinder and both closed caps form the exact
frontier. The finite sphere source is constructed by its own cube
frontier subcomplex. See rigidity042, sections1 and4.
-/

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareMT.M76

local notation "V2" => (Fin 2 → ℝ)
local notation "E" => (V2 × ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "Q" => sphere (0 : V2) 1

/-- The entire parameter boundary with both whole caps retained. -/
def cubePrismBoundary (a b : ℝ) : Set E :=
  (Q ×ˢ Icc a b) ∪ (D ×ˢ ({a, b} : Set ℝ))

/-- The actual prism is a finite PL ball with the whole stated
boundary, including every rim corner. See rigidity042, section1. -/
theorem isFinitePLBallPair_cubePrism {a b : ℝ} (hab : a < b) :
    IsFinitePLBallPair E (D ×ˢ Icc a b) (cubePrismBoundary a b) :=
  (isFinitePLBallPair_unit_cube (ι := Fin 2)).prod (isFinitePLBallPair_Icc hab)

/-- The specified complete parameter boundary is the literal
ambient frontier of the closed prism. See rigidity042, section1. -/
theorem frontier_cubePrism {a b : ℝ} (hab : a ≤ b) :
    frontier (D ×ˢ Icc a b) = cubePrismBoundary a b := by
  rw [frontier_prod_eq, isClosed_closedBall.closure_eq, isClosed_Icc.closure_eq,
    frontier_closedBall _ one_ne_zero, frontier_Icc hab, union_comm]
  rfl

/-- Construct an exact finite triangulation of the entire prism
frontier from the actual convex body. See rigidity042, section1. -/
theorem exists_finite_cubePrismBoundary {a b : ℝ} (hab : a < b) :
    ∃ K : SimplicialComplex ℝ E,
      K.faces.Finite ∧ K.space = cubePrismBoundary a b := by
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKS, _⟩, _⟩, _⟩ :=
    isFinitePLBallPair_cubePrism hab
  have hne : (interior (D ×ˢ Icc a b)).Nonempty := by
    refine ⟨(0, (a + b) / 2), ?_⟩
    rw [interior_prod_eq, interior_closedBall _ one_ne_zero, interior_Icc]
    exact ⟨mem_ball_self zero_lt_one, by linarith, by linarith⟩
  refine ⟨K.frontierSubcomplex (D ×ˢ Icc a b),
    K.frontierSubcomplex_finite _ hK, ?_⟩
  rw [K.frontierSubcomplex_space (isClosed_closedBall.prod isClosed_Icc)
    ((convex_closedBall _ _).prod (convex_Icc a b)) hne hKS,
    frontier_cubePrism hab.le]

/-- Every complete parameter cap has its own actual finite
carrier by affine insertion of its fixed time. See042, section1. -/
theorem exists_finite_cubePrismCap (t : ℝ) :
    ∃ K : SimplicialComplex ℝ E,
      K.faces.Finite ∧ K.space = D ×ˢ ({t} : Set ℝ) := by
  classical
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨J, hJ, hJD, _⟩, _⟩, _⟩ :=
    isFinitePLBallPair_unit_cube (ι := Fin 2)
  let A : V2 →ᴬ[ℝ] E :=
    (ContinuousAffineMap.id ℝ V2).prod (ContinuousAffineMap.const ℝ V2 t)
  have hA : J.AffineOnFaces A := J.affineOnFaces_affine A
  have hi : InjOn A J.space := by
    intro x _ y _ heq
    exact congrArg (fun z : E => z.1) heq
  refine ⟨hA.embeddedImage hi, hA.embeddedImage_finite hi hJ, ?_⟩
  rw [hA.embeddedImage_space hi, hJD]
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨hx, rfl⟩
  · intro hz
    exact ⟨z.1, hz.1, Prod.ext rfl (show t = z.2 from hz.2.symm)⟩

/-- The entire literal cube sphere has a finite triangulation.
It is not obtained by assuming a linear map preserves norms. See042. -/
theorem exists_finite_unitCubeSphere {ι : Type*} [Fintype ι] :
    ∃ K : SimplicialComplex ℝ (ι → ℝ),
      K.faces.Finite ∧ K.space = sphere (0 : ι → ℝ) 1 := by
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKD, _⟩, _⟩, _⟩ :=
    isFinitePLBallPair_unit_cube (ι := ι)
  refine ⟨K.frontierSubcomplex (closedBall (0 : ι → ℝ) 1),
    K.frontierSubcomplex_finite _ hK, ?_⟩
  rw [K.frontierSubcomplex_space isClosed_closedBall (convex_closedBall _ _)
    ⟨0, ball_subset_interior_closedBall (mem_ball_self zero_lt_one)⟩ hKD,
    frontier_closedBall _ one_ne_zero]

end PoincareMT.M76
