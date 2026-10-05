import PoincareLib.Topology.Manifold.Smoothing.Rigidity.IndexOne.Hierarchy.Cuts.Ball
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Regions.OriginalBallBoundaryExtension

/-!
# Extend the whole marked cut frontier over its complementary prism

Original irreducibility constructs the actual cut ball. Its prescribed
boundary extension retains both complete physical disk faces and the entire
retained cylinder, in the same original atlas.
-/

set_option autoImplicit false
open Set Metric Geometry

namespace PoincareMT.M76.OriginalDiskProduct

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "W" => (V2 × ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "Q" => sphere (0 : V2) 1

/-- Construct the complete original-atlas prism parametrization from the
actual marked cylinder and original irreducibility. Every boundary value
is the prescribed one; neither a ball nor an extension is supplied. -/
theorem exists_marked_cut_prism_extension
    {X ι : Type*} [TopologicalSpace X] [T2Space X] [PreconnectedSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {N : Set X} {j : V2 → X}
    (P : OriginalDiskProduct e N j) (hI : IsPLIrreducible e N) (hN : IsCompact N)
    (hopen : IsOpen ((Subtype.val : N → X) ⁻¹' P.openStrip))
    (q : W → X) {l u : ℝ} (hlu : l < u)
    (hlower : ∀ z ∈ Q, q (z, l) = P.map (z, (1 / 2 : ℝ)))
    (hupper : ∀ z ∈ Q, q (z, u) = P.map (z, -(1 / 2 : ℝ)))
    (hq : PolyhedralPLInCharts e q (Q ×ˢ Icc l u))
    (hqi : InjOn q (Q ×ˢ Icc l u))
    (himage : q '' (Q ×ˢ Icc l u) = frontier N \ P.openStrip) :
    ∃ (H : (D ×ˢ Icc l u : Set W) ≃ₜ P.cutCarrier) (f : W → X),
      PolyhedralPLInCharts e f (D ×ˢ Icc l u) ∧
      (∀ z : (D ×ˢ Icc l u : Set W), f z = (H z : X)) ∧
      EqOn f (P.markedCutFrontierMap q l u) (cubePrismBoundary l u) ∧
      (∀ z : (D ×ˢ Icc l u : Set W),
        f z ∈ frontier P.cutCarrier ↔ (z : W) ∈ cubePrismBoundary l u) ∧
      (∀ z ∈ D, f (z, l) = P.map (z, (1 / 2 : ℝ))) ∧
      (∀ z ∈ D, f (z, u) = P.map (z, -(1 / 2 : ℝ))) ∧
      ∀ z ∈ Q, ∀ t ∈ Icc l u, f (z, t) = q (z, t) := by
  obtain ⟨b⟩ := P.nonempty_cut_ball_of_marked_cylinder hI hN hopen q hlu
    hlower hupper hq hqi himage
  obtain ⟨Hb, hHbval, _, _, _, hboundaryPL, _⟩ :=
    P.exists_marked_cut_frontier_sphere hI.1 hN hopen q hlu hlower hupper hq hqi himage
  obtain ⟨K, hK, hKB⟩ := exists_finite_cubePrismBoundary hlu
  obtain ⟨H, f, hf, hvalue, hboundary, hmem⟩ :=
    b.exists_prescribed_boundary_extension hI.1.compatible
      (isFinitePLBallPair_cubePrism hlu) K hK hKB Hb
      (P.markedCutFrontierMap q l u) hboundaryPL hHbval
  refine ⟨H, f, hf, hvalue, hboundary, hmem, ?_, ?_, ?_⟩
  · intro z hz
    have hb : (z, l) ∈ cubePrismBoundary l u := Or.inr ⟨hz, by simp⟩
    exact (hboundary hb).trans (P.markedCutFrontierMap_lower q l u z)
  · intro z hz
    have hb : (z, u) ∈ cubePrismBoundary l u := Or.inr ⟨hz, by simp⟩
    exact (hboundary hb).trans (P.markedCutFrontierMap_upper q hlu z)
  · intro z hz t ht
    have hb : (z, t) ∈ cubePrismBoundary l u := Or.inl ⟨hz, ht⟩
    exact (hboundary hb).trans (P.markedCutFrontierMap_lateral q hlu hlower hupper (z, t) hz)

end PoincareMT.M76.OriginalDiskProduct
