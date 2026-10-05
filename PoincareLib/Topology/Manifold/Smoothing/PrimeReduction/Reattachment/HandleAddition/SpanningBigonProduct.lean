import PoincareLib.Topology.Manifold.Smoothing.PrimeReduction.Reattachment.HandleAddition.SpanningBigonCornerDomain
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Intersections.Boundary.UnionDisk.Product

/-! # A constructed original product of the actual spanning bigon

The occupied sphere side and its corner domain are constructed before the
normal product. Its whole lateral boundary lies in precisely the two old
sheets; its interior avoids both. The given disk parameter is retained.
-/

set_option autoImplicit false
open Set Metric Geometry
namespace PoincareMT.M76
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Disk" => closedBall (0 : V2) 1
local notation "Rim" => sphere (0 : V2) 1
local notation "I" => Icc (-1 : ℝ) 1

theorem ChartwisePLSphere.exists_original_bigon_product
    {ι κ α F : Type*} [Fintype ι] [Fintype κ]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (L : Submodule ℤ (κ → ℝ)) [DiscreteTopology L]
    {e : α → OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) V3}
    {S E O : Set (LatticeHandleAmbient ι κ L)}
    (s : ChartwisePLSphere e S)
    (he : PLDomain e (latticeHandleDomain ι κ L))
    (hE : IsCompact E) (heE : PLDomain e E)
    (hdim : Fintype.card ι + Fintype.card κ = 3)
    (hSR : S ⊆ interior (latticeHandleDomain ι κ L))
    (hcross : ∀ x ∈ S ∩ frontier E, ∃ H : OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) V3,
      x ∈ H.source ∧ H x = 0 ∧
      (∀ i, (e i).symm.trans H ∈ piecewiseAffineGroupoid V3) ∧
      (∀ y ∈ H.source, y ∈ S ↔ H y 1 = 0) ∧
      ∀ y ∈ H.source, y ∈ frontier E ↔ H y 0 = 0)
    {d U C : Set F} (hd : IsFinitePLBallPair (ℝ × ℝ) d (U ∪ C))
    {f : F → LatticeHandleAmbient ι κ L}
    (hf : PolyhedralPLInCharts e f d) (hfi : InjOn f d) (hfE : MapsTo f d E)
    (hfront : (f '' d) ∩ frontier E = f '' U)
    (hsphere : (f '' d) ∩ S = f '' C)
    (hO : IsOpen O) (hfO : f '' d ⊆ O) :
    ∃ (N : Set (LatticeHandleAmbient ι κ L)) (H : Disk ≃ₜ d)
      (j : V2 → LatticeHandleAmbient ι κ L) (P : OriginalDiskProduct e N j),
      IsCompact N ∧ PLDomain e N ∧ N ⊆ E ∧
      frontier N = N ∩ (frontier E ∪ S) ∧
      H.IsFinitePL ∧ (∀ z : Disk, j z = f (H z)) ∧
      (∀ z : Disk, (z : V2) ∈ Rim ↔ (H z : F) ∈ U ∪ C) ∧
      MapsTo P.map (Disk ×ˢ I) O ∧
      P.map '' (Disk ×ˢ {(0 : ℝ)}) = f '' d ∧
      (∀ z ∈ Disk ×ˢ I, P.map z ∈ frontier E ∪ S ↔ z.1 ∈ Rim) ∧
      (∀ z : Disk, j z ∈ frontier E ↔ (H z : F) ∈ U) ∧
      (∀ z : Disk, j z ∈ S ↔ (H z : F) ∈ C) ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
        IsOpen ((Subtype.val : N → _) ⁻¹' (P.map '' (Disk ×ˢ Ioo (-ε) ε))) ∧
        IsOpen ((Subtype.val : frontier N → _) ⁻¹' (P.map '' (Rim ×ˢ Ioo (-ε) ε))) := by
  obtain ⟨N, hN, heN, hNE, hfN, hproper, hNfront⟩ :=
    s.exists_original_bigon_corner_domain L he hE heE hdim hSR hcross
      hd hf hfi hfE hfront hsphere
  obtain ⟨H, j, P, hH, hj, hHrim, hPO, _, hcenter, hopen⟩ :=
    Dehn.Annuli.exists_original_finite_proper_disk_product hN heN hd hf hfi hfN hproper hO hfO
  have hmark {T : Set (LatticeHandleAmbient ι κ L)} {W : Set F}
      (hWd : W ⊆ d) (hcontact : f '' d ∩ T = f '' W) (z : Disk) :
      j z ∈ T ↔ (H z : F) ∈ W := by
    rw [hj z]
    constructor
    · intro hz
      obtain ⟨w, hw, heq⟩ := hcontact.subset ⟨⟨H z, (H z).property, rfl⟩, hz⟩
      exact hfi (hWd hw) (H z).property heq ▸ hw
    · intro hz
      exact (hcontact.symm.subset ⟨H z, hz, rfl⟩).2
  refine ⟨N, H, j, P, hN, heN, hNE, hNfront, hH, hj, hHrim, hPO, hcenter,
    ?_, hmark (subset_union_left.trans hd.1) hfront,
    hmark (subset_union_right.trans hd.1) hsphere, hopen⟩
  intro z hz
  have hh : P.map z ∈ frontier N ↔ P.map z ∈ frontier E ∪ S := by
    rw [hNfront]
    exact and_iff_right (P.inside hz)
  exact hh.symm.trans (P.proper z hz)

end PoincareMT.M76

