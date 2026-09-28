import PoincareConjecture.Proofs.M76.Triangulation.HamiltonLowerOriginalWallCore
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonLowerBrownCap

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [Nonempty κ]

local notation "V" => ((ι → ℝ) × (κ → ℝ))
local notation "W" => LatticeHandleAmbient ι κ (hamiltonLowerPeriodLattice κ)
local notation "V3" => (Fin 3 → ℝ)

theorem HamiltonLowerLatticeImmersion.exists_original_marked_brown_cap
    (I : HamiltonLowerLatticeImmersion κ)
    (hdim : Fintype.card ι + Fintype.card κ = 3)
    (h : OpenPartialHomeomorph V V3)
    (hsource : closedBall (0 : ι → ℝ) 1 ×ˢ (univ : Set (κ → ℝ)) ⊆ h.source)
    {N : Set V} (hN : IsOpen N)
    (hboundary : sphere (0 : ι → ℝ) 1 ×ˢ (univ : Set (κ → ℝ)) ⊆ N)
    (hPL : LocallyPiecewiseAffineOn h (h.source ∩ N))
    (wall : ∀ (U : TopologicalSpace.Opens W)
      (charts : Set (OpenPartialHomeomorph U V3)),
      HasWallCompactCore (fun c : charts => (c : OpenPartialHomeomorph U V3)))
    (brown : HasBrownLocallyFlatSphereBalls) :
    ∃ a b : ℝ, 0 < a ∧ a < 1 ∧ 1 < b ∧
      ∃ U : TopologicalSpace.Opens W,
        (U : Set W) =
          (ball (0 : ι → ℝ) b ×ˢ {hamiltonLowerLatticePuncture κ}ᶜ) ∪
            ({x : ι → ℝ | a < ‖x‖ ∧ ‖x‖ < b} ×ˢ univ) ∧
        ∃ (hU : Nonempty U)
          (d : V → OpenPartialHomeomorph W V3)
          (charts : Set (OpenPartialHomeomorph U V3))
          (c : OpenPartialHomeomorph U V3) (K S : Set U)
          (c0 : OpenPartialHomeomorph W V3) (D : Set W),
          let e := fun j : charts => (j : OpenPartialHomeomorph U V3)
          let R := (Subtype.val : U → W) ⁻¹'
            latticeHandleDomain ι κ (hamiltonLowerPeriodLattice κ)
          StandardLatticeHandleAtlas ι κ (hamiltonLowerPeriodLattice κ) d ∧
          PLDomain e R ∧ c ∈ charts ∧ IsCompact K ∧ K ⊆ R ∧ PLDomain e K ∧
          S ⊆ interior R ∧ Nonempty (ChartwisePLSphere e S) ∧
          Disjoint (frontier R) S ∧ frontier K = frontier R ∪ S ∧
          frontier ((Subtype.val : R → U) ⁻¹' K) = (Subtype.val : R → U) ⁻¹' S ∧
          (Subtype.val : R → U) ⁻¹' frontier R ⊆
            interior ((Subtype.val : R → U) ⁻¹' K) ∧
          (∀ x ∈ closedBall (0 : ι → ℝ) 1 ×ˢ closedBall (0 : κ → ℝ) 2,
            ∃ (z : U) (hzR : z ∈ R), (z : W) = (x.1, QuotientAddGroup.mk x.2) ∧
              z ∈ c.source ∧ c z = h x ∧
                (⟨z, hzR⟩ : R) ∈ interior ((Subtype.val : R → U) ⁻¹' K)) ∧
          (∀ (j : charts) i,
            (((d i).subtypeRestr hU).restr
              {z : U | a < ‖(z : W).1‖ ∧ ‖(z : W).1‖ < b}).symm.trans (e j) ∈
                piecewiseAffineGroupoid V3) ∧
          (∀ x : ι → ℝ, (x, hamiltonLowerLatticePuncture κ) ∈ c0.source) ∧
          D = latticeHandleDomain ι κ (hamiltonLowerPeriodLattice κ) \
            ((Subtype.val : U → W) '' ((Subtype.val : R → U) ''
              interior ((Subtype.val : R → U) ⁻¹' K))) ∧
          IsCompact D ∧ D ⊆ interior (latticeHandleDomain ι κ (hamiltonLowerPeriodLattice κ)) ∧
          frontier D = (Subtype.val : U → W) '' S ∧ D ⊆ c0.source ∧
          (∀ y : U, y ∈ interior R → ((y : W) ∈ D ↔ y ∉ interior K)) ∧
          ((Subtype.val : U → W) '' K) ∪ D =
            latticeHandleDomain ι κ (hamiltonLowerPeriodLattice κ) ∧
          ((Subtype.val : U → W) '' K) ∩ D = (Subtype.val : U → W) '' S ∧
          IsUnitBallPair V3 D ((Subtype.val : U → W) '' S) := by
  classical
  obtain ⟨a, b, ha, ha1, hb, U, hUeq, hU, d, charts, c, K, S,
    hd, he, hc, hK, hKR, heK, hSint, hs, hdis, hfrontK, hrelative,
    hretain, hcore, hcollar, c0, hc0, hcapc⟩ :=
    I.exists_original_marked_wall_core hdim h hsource hN hboundary hPL wall
  let : Nonempty U := hU
  let : Fact (0 < 4 * (128 : ℝ)) := ⟨by norm_num⟩
  let T := ((κ → ℝ) ⧸ (hamiltonLowerPeriodLattice κ).toAddSubgroup)
  let : CompactSpace T := (hamiltonLowerLatticePiEquiv κ).symm.compactSpace
  let H := latticeHandleDomain ι κ (hamiltonLowerPeriodLattice κ)
  let R : Set U := (Subtype.val : U → W) ⁻¹' H
  let D := H \ ((Subtype.val : U → W) '' ((Subtype.val : R → U) ''
    interior ((Subtype.val : R → U) ⁻¹' K)))
  have hH : IsCompact H := (isCompact_closedBall (0 : ι → ℝ) 1).prod isCompact_univ
  have hHU : frontier H ⊆ (U : Set W) := by
    intro x hx
    have hHS : frontier H = sphere (0 : ι → ℝ) 1 ×ˢ univ := by
      simp only [H, latticeHandleDomain, frontier_prod_univ_eq, frontier_closedBall _ one_ne_zero]
    have hnorm : ‖x.1‖ = 1 := by
      simpa only [mem_sphere, dist_zero_right] using (hHS.subset hx).1
    rw [hUeq]
    exact Or.inr ⟨⟨by simpa only [hnorm] using ha1, by simpa only [hnorm] using hb⟩,
      mem_univ _⟩
  obtain ⟨hD, hDint, hfrontD, hDlocal⟩ :=
    PLDomain.relative_wall_missing_side hH hHU hK heK hSint hfrontK hretain
  obtain ⟨s⟩ := hs
  have hball := PLDomain.brown_relative_wall_complement brown hH hHU hK heK
    hSint hfrontK hretain s c0 hcapc
  have hcover : ((Subtype.val : U → W) '' K) ∪ D = H := by
    apply Subset.antisymm
    · intro x hx
      rcases hx with ⟨y, hy, rfl⟩ | hx
      · exact hKR hy
      · exact hx.1
    · intro x hx
      by_cases hxD : x ∈ D
      · exact Or.inr hxD
      · have hi : x ∈ (Subtype.val : U → W) '' ((Subtype.val : R → U) ''
            interior ((Subtype.val : R → U) ⁻¹' K)) := by
          by_contra hn
          exact hxD ⟨hx, hn⟩
        obtain ⟨y, ⟨z, hz, rfl⟩, rfl⟩ := hi
        have hzK : z ∈ (Subtype.val : R → U) ⁻¹' K := interior_subset hz
        exact Or.inl ⟨(z : U), hzK, rfl⟩
  have hmeet : ((Subtype.val : U → W) '' K) ∩ D = (Subtype.val : U → W) '' S := by
    apply Subset.antisymm
    · rintro x ⟨⟨y, hy, rfl⟩, hyD⟩
      let z : R := ⟨y, hKR hy⟩
      have hzf : z ∈ frontier ((Subtype.val : R → U) ⁻¹' K) := by
        refine ⟨subset_closure hy, ?_⟩
        intro hi
        exact hyD.2 ⟨y, ⟨z, hi, rfl⟩, rfl⟩
      have hyS : y ∈ S := hrelative.subset hzf
      exact ⟨y, hyS, rfl⟩
    · rintro x ⟨y, hy, rfl⟩
      have hyR : y ∈ R := interior_subset (hSint hy)
      let z : R := ⟨y, hyR⟩
      have hzf : z ∈ frontier ((Subtype.val : R → U) ⁻¹' K) := hrelative.symm.subset hy
      have hyK : y ∈ K :=
        (hK.isClosed.preimage
          (continuous_subtype_val : Continuous (Subtype.val : R → U))).frontier_subset hzf
      refine ⟨⟨y, hyK, rfl⟩, hyR, ?_⟩
      rintro ⟨w, ⟨v, hv, hvw⟩, hwy⟩
      have hvz : v = z := Subtype.ext
        (Subtype.ext ((congrArg Subtype.val hvw).trans hwy))
      exact hzf.2 (hvz ▸ hv)
  exact ⟨a, b, ha, ha1, hb, U, hUeq, hU, d, charts, c, K, S, c0, D,
    hd, he, hc, hK, hKR, heK, hSint, ⟨s⟩, hdis, hfrontK, hrelative,
    hretain, hcore, hcollar, hc0, rfl, hD, hDint, hfrontD, hcapc,
    hDlocal, hcover, hmeet, hball⟩

end PoincareConjecture.M76
