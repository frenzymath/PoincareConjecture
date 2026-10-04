import PoincareLib.Topology.Manifold.Smoothing.PrimeReduction.Faces.Cutting.FiniteArcComponentCount
import PoincareLib.Topology.Manifold.Smoothing.PrimeReduction.Tetrahedra.OriginalFaceArcModels
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Regions.FinitePLIntervalBoundary

/-!
# Original normal-face complementary disks and their exact count

The original normal graph constructs its interval family on the same
original simplex. Cutting that family constructs every complementary
disk closure and the exact number of actual connected components.
-/

set_option autoImplicit false

open Set Geometry

namespace PoincareMT.M76

local notation "V3" => (Fin 3 → ℝ)

theorem InCircleFreeNonreturningTriangleGraphPosition.exists_original_face_components
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E] [TopologicalSpace X]
    (K : SimplicialComplex ℝ E) (g : E → X) (hgi : InjOn g K.space)
    {s : Finset E} (hs : s ∈ K.faces) (hs3 : s.card = 3)
    (Q : OpenPartialHomeomorph X V3) (A : E →ᴬ[ℝ] V3)
    (hmap : MapsTo g (convexHull ℝ (s : Set E)) Q.source)
    (hA : EqOn (Q ∘ g) A (convexHull ℝ (s : Set E)))
    {S : Set X} (hposition : InCircleFreeNonreturningTriangleGraphPosition Q S g s A) :
    ∃ (γ : Type) (_ : Finite γ) (d r : γ → Set E),
      (Pairwise fun i j => Disjoint (d i) (d j)) ∧
      g '' (⋃ i, d i) = S ∩ (g '' convexHull ℝ (s : Set E)) ∧
      (⋃ i, d i) ⊆ convexHull ℝ (s : Set E) ∧
      (∀ i, IsFinitePLBallPair ℝ (d i) (r i) ∧
        r i = d i ∩ intrinsicFrontier ℝ (convexHull ℝ (s : Set E)) ∧
        ∀ a : Finset E, a ⊆ s → a.card = 2 → ¬ r i ⊆ convexHull ℝ (a : Set E)) ∧
      Finite (ConnectedComponents (convexHull ℝ (s : Set E) \ ⋃ i, d i : Set E)) ∧
      Nat.card (ConnectedComponents (convexHull ℝ (s : Set E) \ ⋃ i, d i : Set E)) =
        Nat.card γ + 1 ∧
      ∀ x ∈ convexHull ℝ (s : Set E) \ ⋃ i, d i,
        IsFinitePLBallPair (ℝ × ℝ)
          (closure (connectedComponentIn (convexHull ℝ (s : Set E) \ ⋃ i, d i) x))
          (closure (connectedComponentIn (convexHull ℝ (s : Set E) \ ⋃ i, d i) x) ∩
            (intrinsicFrontier ℝ (convexHull ℝ (s : Set E)) ∪ ⋃ i, d i)) := by
  classical
  obtain ⟨γ, hγ, d, r, hdis, hphysical, hsub, harcs⟩ :=
    hposition.exists_normal_arc_family_on_original_face K g hgi hs Q A hmap hA
  let : Finite γ := hγ
  choose p q hpq hr using fun i => (harcs i).1.exists_boundary_eq_pair
  have htriangle := isFinitePLBallPair_independent_triangle s (K.indep hs) hs3
  obtain ⟨hfinite, hcount, hregions⟩ := finite_proper_arc_component_count htriangle d p q
    (fun i => hr i ▸ (harcs i).1) hpq (fun i x hx => hsub (mem_iUnion.mpr ⟨i, hx⟩))
    (fun i => (hr i).symm.trans (harcs i).2.1) hdis
  exact ⟨γ, hγ, d, r, hdis, hphysical, hsub, harcs, hfinite, hcount, hregions⟩

end PoincareMT.M76
