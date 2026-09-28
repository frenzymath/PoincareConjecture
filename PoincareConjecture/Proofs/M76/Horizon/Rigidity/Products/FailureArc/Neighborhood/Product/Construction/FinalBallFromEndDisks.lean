import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Product.MarkedBall.PrescribedDisk
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Product.AnnularParameter.PairDisk
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Product.AnnularParameter.PairCylinder
import PoincareConjecture.Proofs.M76.Rigidity.InwardCollarCoordinates



set_option autoImplicit false
open Set Metric Geometry Topology

namespace PoincareConjecture.M76.Dehn.Annuli.ProductConstruction

local notation "P2" => (ℝ × ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "I" => Icc (0 : ℝ) 1
local notation "Disk" => closedBall (0 : P2) 1
local notation "Rim" => sphere (0 : P2) 1



theorem exists_final_ball_product_of_end_disk_images
    {E₀ E₁ X ι : Type*}
    [NormedAddCommGroup E₀] [NormedSpace ℝ E₀] [FiniteDimensional ℝ E₀]
    [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [FiniteDimensional ℝ E₁]
    [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3}
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    {c₀ q₀ : Set E₀} {c₁ q₁ : Set E₁}
    (hc₀ : IsFinitePLBallPair P2 c₀ q₀) (hc₁ : IsFinitePLBallPair P2 c₁ q₁)
    {a : P2 × ℝ → X}
    (ha : PolyhedralPLInCharts e a (Rim ×ˢ I)) (hai : InjOn a (Rim ×ˢ I))
    {g₀ : E₀ → X} {g₁ : E₁ → X}
    (hg₀ : PolyhedralPLInCharts e g₀ c₀) (hg₁ : PolyhedralPLInCharts e g₁ c₁)
    (hi₀ : InjOn g₀ c₀) (hi₁ : InjOn g₁ c₁)
    (hbottom : a '' (Rim ×ˢ {(0 : ℝ)}) = g₀ '' q₀)
    (htop : g₁ '' q₁ = a '' (Rim ×ˢ {(1 : ℝ)}))
    (hbase : (g₀ '' c₀) ∩ (a '' (Rim ×ˢ I)) = g₀ '' q₀)
    (hcontact : (g₁ '' c₁) ∩ (a '' (Rim ×ˢ I)) = g₁ '' q₁)
    (hdis : Disjoint (g₁ '' c₁) (g₀ '' c₀))
    {B : Set X}
    (ball : ChartwisePLBall e B (a '' (Rim ×ˢ I) ∪ (g₀ '' c₀ ∪ g₁ '' c₁))) :
    ∃ (H : (Disk ×ˢ I : Set (P2 × ℝ)) ≃ₜ B) (k : P2 × ℝ → X),
      PolyhedralPLInCharts e k (Disk ×ˢ I) ∧
      (∀ p : (Disk ×ˢ I : Set (P2 × ℝ)), k p = (H p : X)) ∧
      IsEmbedding (fun p : (Disk ×ˢ I : Set (P2 × ℝ)) => k p) ∧
      k '' (Disk ×ˢ I) = B ∧ EqOn k a (Rim ×ˢ I) ∧
      k '' (Disk ×ˢ {(0 : ℝ)}) = g₀ '' c₀ ∧
      (∀ p ∈ Disk ×ˢ I, k p ∈ g₁ '' c₁ ↔ p.2 = 1) ∧
      ∀ p ∈ Disk ×ˢ I, k p ∈ a '' (Rim ×ˢ I) ↔ p.1 ∈ Rim := by
  obtain ⟨L, hL, hLs⟩ := AnnularParameter.exists_pair_rim_triangulation
  have hf : PolyhedralPLInCharts e (fun z => a (z, 0)) Rim := by
    exact hLs ▸ PolyhedralPLInCharts.finite_product_slice L hL
      (hLs.symm ▸ ha) (by norm_num)
  have hfi : InjOn (fun z => a (z, 0)) Rim := by
    intro x hx y hy hxy
    exact congrArg Prod.fst (hai ⟨hx, by norm_num⟩ ⟨hy, by norm_num⟩ hxy)
  have hfiImage : (fun z => a (z, 0)) '' Rim = g₀ '' q₀ := by
    rw [← hbottom]
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨(z, 0), ⟨hz, rfl⟩, rfl⟩
    · rintro ⟨⟨z, t⟩, ⟨hz, ht⟩, rfl⟩
      exact ⟨z, hz, congrArg a (Prod.ext rfl (show 0 = t from ht.symm))⟩
  obtain ⟨g, hg, hi, himage, hrim⟩ := MarkedBall.exists_disk_with_prescribed_rim
    hcompat AnnularParameter.pairDisk_isFinitePLBallPair hc₀ L hL hLs
    hf hfi hg₀ hi₀ hfiImage
  have hball : ChartwisePLBall e B (a '' (Rim ×ˢ I) ∪ (g '' Disk ∪ g₁ '' c₁)) := by
    rw [himage]
    exact ball
  obtain ⟨K, hK, hKs, _⟩ := AnnularParameter.pairCylinderCoordinates_finitePL
  obtain ⟨H, k, hk, hkv, hki, hkimage, hkbottom, hann, hktop, _, hkside⟩ :=
    MarkedBall.exists_original_product hcompat AnnularParameter.pairDisk_isFinitePLBallPair
      hc₁ K hK hKs ha hai hg hg₁ hi hi₁ (fun z hz => (hrim hz).symm) hball
      htop hcontact (by rw [himage, hbase, hbottom]) (by rw [himage]; exact hdis)
  refine ⟨H, k, hk, hkv, hki, hkimage, hann, ?_, hktop, hkside⟩
  rw [← himage]
  ext x
  constructor
  · rintro ⟨⟨z, t⟩, ⟨hz, ht⟩, rfl⟩
    have ht' : t = 0 := ht
    subst t
    exact ⟨z, hz, (hkbottom z hz).symm⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨(z, 0), ⟨hz, rfl⟩, hkbottom z hz⟩

end PoincareConjecture.M76.Dehn.Annuli.ProductConstruction
