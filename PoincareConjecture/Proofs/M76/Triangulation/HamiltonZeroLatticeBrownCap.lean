import PoincareConjecture.Proofs.M76.Triangulation.HamiltonZeroLatticeWallCore
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonWallComplementBall
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonStandardAtlasExistence

set_option autoImplicit false

open Set Metric

namespace PoincareConjecture.M76

local notation "W" => LatticeHandleAmbient (Fin 0) (Fin 3) hamiltonZeroPeriodLattice
local notation "Y" => ((Set.singleton hamiltonZeroHandlePuncture)ᶜ : Set W)
local notation "V3" => (Fin 3 → ℝ)

theorem exists_zero_lattice_marked_brown_cap
    (h : OpenPartialHomeomorph CubeShell.Ambient V3) (hsource : h.source = univ)
    (wall : ∀ e : Y → OpenPartialHomeomorph Y V3, HasWallCompactCore e)
    (brown : HasBrownLocallyFlatSphereBalls) (A : Set Y) (hA : IsCompact A) :
    ∃ (f : W → CubeShell.Ambient) (e : Y → OpenPartialHomeomorph Y V3)
      (r : ℝ) (i : Y) (K : Set Y),
      IsLocalHomeomorphOn f Y ∧ PLDomain e univ ∧
      IsCompact K ∧ PLDomain e K ∧ Nonempty (ChartwisePLSphere e (frontier K)) ∧
      A ⊆ interior K ∧
      IsUnitBallPair V3 (interior ((Subtype.val : Y → W) '' K))ᶜ
        ((Subtype.val : Y → W) '' frontier K) ∧
      0 < r ∧ r ≤ 1 / 64 ∧
      (∀ j, EqOn (e j) (fun x : Y => h (f x)) (e j).source) ∧
      ∀ x : V3, ‖x‖ ≤ r →
        ∃ z : Y, (z : W) = (0, QuotientAddGroup.mk x) ∧
          z ∈ interior K ∧ z ∈ (e i).source ∧ e i z = h (CubeShell.vector x) := by
  let : Fact (0 < 4 * (16 : ℝ)) := ⟨by norm_num⟩
  let : T2Space W := hamiltonZeroHandleProductEquiv.isEmbedding.t2Space
  let : CompactSpace W := hamiltonZeroHandleProductEquiv.symm.compactSpace
  have hY : IsOpen Y := isClosed_singleton.isOpen_compl
  obtain ⟨d, hdcover, _, _⟩ := exists_standard_lattice_coordinate_cover
    (Fin 0) (Fin 3) hamiltonZeroPeriodLattice (by simp)
  obtain ⟨j, hj⟩ := hdcover hamiltonZeroHandlePuncture
  let c := d j
  have hcY : c.sourceᶜ ⊆ Y := by
    intro x hx
    change x ≠ hamiltonZeroHandlePuncture
    intro heq
    exact hx (heq.symm ▸ hj)
  let A0 : Set Y := (Subtype.val : Y → W) ⁻¹' c.sourceᶜ
  have hA0image : (Subtype.val : Y → W) '' A0 = c.sourceᶜ :=
    image_preimage_eq_of_subset (by
      intro x hx
      exact ⟨⟨x, hcY hx⟩, rfl⟩)
  have hA0 : IsCompact A0 := Topology.IsEmbedding.subtypeVal.isCompact_iff.mpr (by
    rw [hA0image]
    exact c.open_source.isClosed_compl.isCompact)
  obtain ⟨f, e, r, i, K, hf, he, hK, hKD, hs, hretain,
      hr, hr64, heq, hretained⟩ :=
    exists_zero_lattice_marked_wall_core h hsource wall (A ∪ A0) (hA.union hA0)
  have hc : (interior ((Subtype.val : Y → W) '' K))ᶜ ⊆ c.source := by
    intro x hx
    by_contra hn
    let y : Y := ⟨x, hcY hn⟩
    have hy : y ∈ interior K := hretain (Or.inr hn)
    exact hx (hY.isOpenMap_subtype_val.image_interior_subset K ⟨y, hy, rfl⟩)
  obtain ⟨s⟩ := hs
  have hcap := hKD.brown_complement_ball_of_chart brown hY hK s c hc
  exact ⟨f, e, r, i, K, hf, he, hK, hKD, ⟨s⟩,
    fun x hx => hretain (Or.inl hx), hcap, hr, hr64, heq, hretained⟩

end PoincareConjecture.M76
