import PoincareConjecture.Proofs.M76.Rigidity.OriginalBallBoundaryExtension
import PoincareConjecture.Proofs.M76.Rigidity.MeridianCutFrontierHomeomorph









set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76.OriginalDiskProduct

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "E" => (V2 × ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "Q" => sphere (0 : V2) 1
local notation "I" => Icc (-1 : ℝ) 1
local notation "L" => hamiltonLowerPeriodLattice (Fin 1)
local notation "X" => LatticeHandleAmbient (Fin 2) (Fin 1) L
local notation "R" => latticeHandleDomain (Fin 2) (Fin 1) L
local notation "p" => (4 * (128 : ℝ))

variable {ι : Type*} {e : ι → OpenPartialHomeomorph X V3} {j : V2 → X}




theorem exists_meridianCutPrism_extension (P : OriginalDiskProduct e R j)
    (he : PLDomain e R) (hR : IsCompact R)
    (hopen : IsOpen ((Subtype.val : R → X) ⁻¹' P.openStrip))
    {a : ℝ} (ha : 0 < a) (hasmall : a ≤ 1 / 2)
    (hmark : ∀ z ∈ Q, ∀ t ∈ I,
      P.map (z, t) = hamiltonMeridianCutAmbientMap (z, a * t))
    (hC : PolyhedralPLInCharts e hamiltonMeridianCutAmbientMap
      (Q ×ˢ Icc (a / 2) (p - a / 2)))
    (b : ChartwisePLBall e P.cutCarrier (frontier P.cutCarrier)) :
    ∃ (H : (D ×ˢ Icc (a / 2) (p - a / 2) : Set E) ≃ₜ P.cutCarrier)
      (u : E → X),
      PolyhedralPLInCharts e u (D ×ˢ Icc (a / 2) (p - a / 2)) ∧
      (∀ z : (D ×ˢ Icc (a / 2) (p - a / 2) : Set E), u z = (H z : X)) ∧
      EqOn u (P.meridianCutFrontierMap a) (cubePrismBoundary (a / 2) (p - a / 2)) ∧
      (∀ z : (D ×ˢ Icc (a / 2) (p - a / 2) : Set E),
        u z ∈ frontier P.cutCarrier ↔ (z : E) ∈ cubePrismBoundary (a / 2) (p - a / 2)) ∧
      (∀ z ∈ D, u (z, a / 2) = P.map (z, 1 / 2)) ∧
      (∀ z ∈ D, u (z, p - a / 2) = P.map (z, -(1 / 2))) ∧
      ∀ z ∈ Q, ∀ t ∈ Icc (a / 2) (p - a / 2),
        u (z, t) = hamiltonMeridianCutAmbientMap (z, t) := by
  have hgap : a / 2 < p - a / 2 := by norm_num at hasmall ⊢; linarith
  obtain ⟨Hb, hHbval⟩ := P.exists_meridianCutFrontier_homeomorph he hR hopen
    ha hasmall hmark hC
  obtain ⟨K, hK, hKB⟩ := exists_finite_cubePrismBoundary hgap
  obtain ⟨H, u, hu, hvalue, hboundary, hmem⟩ :=
    b.exists_prescribed_boundary_extension he.compatible
      (isFinitePLBallPair_cubePrism hgap) K hK hKB Hb
      (P.meridianCutFrontierMap a) (P.polyhedral_meridianCutFrontierMap he hgap hmark hC)
      hHbval
  refine ⟨H, u, hu, hvalue, hboundary, hmem, ?_, ?_, ?_⟩
  · intro z hz
    have hb : (z, a / 2) ∈ cubePrismBoundary (a / 2) (p - a / 2) :=
      Or.inr ⟨hz, by simp⟩
    exact (hboundary hb).trans (P.meridianCutFrontierMap_lower a z)
  · intro z hz
    have hb : (z, p - a / 2) ∈ cubePrismBoundary (a / 2) (p - a / 2) :=
      Or.inr ⟨hz, by simp⟩
    exact (hboundary hb).trans (P.meridianCutFrontierMap_upper hgap z)
  · intro z hz t ht
    have hb : (z, t) ∈ cubePrismBoundary (a / 2) (p - a / 2) := Or.inl ⟨hz, ht⟩
    exact (hboundary hb).trans (P.meridianCutFrontierMap_lateral hgap hmark (z, t) hz)

end PoincareConjecture.M76.OriginalDiskProduct
