import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Neighborhood.Product.MarkedBall.Construction
import PoincareLib.Topology.Manifold.Smoothing.PrimeReduction.Coordinates.BallModelCoordinates

/-! # Glue an actual annulus and its two prescribed caps into a cut ball -/

set_option autoImplicit false
open Set Metric Geometry Topology

namespace PoincareMT.M76.Dehn.Annuli.ProductConstruction

local notation "P2" => (ℝ × ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "I" => Icc (0 : ℝ) 1
local notation "Disk" => closedBall (0 : P2) 1
local notation "Rim" => sphere (0 : P2) 1

theorem exists_final_marked_ball_product
    {X ι E₁ : Type*} [TopologicalSpace X] [T2Space X]
    [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [FiniteDimensional ℝ E₁]
    {e : ι → OpenPartialHomeomorph X V3} {B : Set X}
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    {c₁ q₁ : Set E₁} (hc₀ : IsFinitePLBallPair P2 Disk Rim)
    (hc₁ : IsFinitePLBallPair P2 c₁ q₁)
    {a : P2 × ℝ → X} (ha : PolyhedralPLInCharts e a (Rim ×ˢ I))
    (hai : InjOn a (Rim ×ˢ I)) {g₀ : P2 → X} {g₁ : E₁ → X}
    (hg₀ : PolyhedralPLInCharts e g₀ Disk) (hg₁ : PolyhedralPLInCharts e g₁ c₁)
    (hi₀ : InjOn g₀ Disk) (hi₁ : InjOn g₁ c₁)
    (hbottom : ∀ z ∈ Rim, a (z,0) = g₀ z)
    {K : SimplicialComplex ℝ (P2 × ℝ)} (hK : K.faces.Finite) (hKs : K.space = Rim ×ˢ I)
    {S : Set X} (ball : ChartwisePLBall e B S)
    (hS : S = a '' (Rim ×ˢ I) ∪ (g₀ '' Disk ∪ g₁ '' c₁))
    (htoprim : g₁ '' q₁ = a '' (Rim ×ˢ {(1 : ℝ)}))
    (hcontact : (g₁ '' c₁) ∩ (a '' (Rim ×ˢ I)) = g₁ '' q₁)
    (hbase : (g₀ '' Disk) ∩ (a '' (Rim ×ˢ I)) = a '' (Rim ×ˢ {(0 : ℝ)}))
    (hdis : Disjoint (g₁ '' c₁) (g₀ '' Disk)) :
    ∃ H : (Disk ×ˢ I : Set (P2 × ℝ)) ≃ₜ B,
      ∃ k : P2 × ℝ → X, PolyhedralPLInCharts e k (Disk ×ˢ I) ∧
        (∀ p : (Disk ×ˢ I : Set (P2 × ℝ)), k p = (H p : X)) ∧
        IsEmbedding (fun p : (Disk ×ˢ I : Set (P2 × ℝ)) ↦ k p) ∧
        k '' (Disk ×ˢ I) = B ∧ (∀ z ∈ Disk, k (z,0) = g₀ z) ∧
        EqOn k a (Rim ×ˢ I) ∧
        (∀ p ∈ Disk ×ˢ I, k p ∈ g₁ '' c₁ ↔ p.2 = 1) := by
  have hS' : ChartwisePLBall e B
      (a '' (Rim ×ˢ I) ∪ (g₀ '' Disk ∪ g₁ '' c₁)) := by
    rw [← hS]
    exact ball
  obtain ⟨H,k,hk,hkv,hki,hkimage,hbottomk,hann,hside⟩ :=
    MarkedBall.exists_original_product hcompat hc₀ hc₁ K hK hKs ha hai
      hg₀ hg₁ hi₀ hi₁ hbottom hS' htoprim hcontact hbase hdis
  exact ⟨H,k,hk,hkv,hki,hkimage,hbottomk,hann,hside.1⟩

end PoincareMT.M76.Dehn.Annuli.ProductConstruction
