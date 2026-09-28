import PoincareConjecture.Proofs.M76.Triangulation.HamiltonZeroLatticePuncturedAtlas
import Mathlib.Topology.EMetricSpace.Paracompact











set_option autoImplicit false

open Set Metric

namespace PoincareConjecture.M76

local notation "W" => LatticeHandleAmbient (Fin 0) (Fin 3) hamiltonZeroPeriodLattice
local notation "Y" => ((Set.singleton hamiltonZeroHandlePuncture)ᶜ : Set W)
local notation "V3" => (Fin 3 → ℝ)



instance hamiltonZeroLatticePunctureT2 : T2Space Y := by
  let : Fact (0 < 4 * (16 : ℝ)) := ⟨by norm_num⟩
  exact hamiltonZeroPunctureModelEquiv.isEmbedding.t2Space



instance hamiltonZeroLatticePunctureParacompact : ParacompactSpace Y := by
  let : Fact (0 < 4 * (16 : ℝ)) := ⟨by norm_num⟩
  exact hamiltonZeroPunctureModelEquiv.isClosedEmbedding.paracompactSpace






theorem exists_zero_lattice_marked_wall_core
    (h : OpenPartialHomeomorph CubeShell.Ambient V3) (hsource : h.source = univ)
    (wall : ∀ e : Y → OpenPartialHomeomorph Y V3, HasWallCompactCore e)
    (A : Set Y) (hA : IsCompact A) :
    ∃ (f : W → CubeShell.Ambient) (e : Y → OpenPartialHomeomorph Y V3)
      (r : ℝ) (i : Y) (K : Set Y),
      IsLocalHomeomorphOn f Y ∧ PLDomain e univ ∧
      IsCompact K ∧ PLDomain e K ∧ Nonempty (ChartwisePLSphere e (frontier K)) ∧
      A ⊆ interior K ∧ 0 < r ∧ r ≤ 1 / 64 ∧
      (∀ j, EqOn (e j) (fun x : Y => h (f x)) (e j).source) ∧
      ∀ x : V3, ‖x‖ ≤ r →
        ∃ z : Y, (z : W) = (0, QuotientAddGroup.mk x) ∧
          z ∈ interior K ∧ z ∈ (e i).source ∧ e i z = h (CubeShell.vector x) := by
  obtain ⟨f, e, hf, he, hconn, hend, heq, r, i, hr, hr64, hretained⟩ :=
    exists_zero_lattice_punctured_PL_domain h hsource
  have hquotient (x : V3) (hx : ‖x‖ ≤ r) :
      (0, QuotientAddGroup.mk x) ∈ ({hamiltonZeroHandlePuncture}ᶜ : Set W) := by
    obtain ⟨z, hz, _, _⟩ := hretained x hx
    rw [← hz]
    exact z.property
  let q : closedBall (0 : V3) r → Y := fun x =>
    ⟨(0, QuotientAddGroup.mk (x : V3)),
      hquotient x (mem_closedBall_zero_iff.mp x.property)⟩
  have hq : Continuous q := by
    apply Topology.IsEmbedding.subtypeVal.continuous_iff.mpr
    change Continuous (fun x : closedBall (0 : V3) r =>
      ((0 : Fin 0 → ℝ), QuotientAddGroup.mk (x : V3)))
    exact continuous_const.prodMk (QuotientAddGroup.continuous_mk.comp continuous_subtype_val)
  have hcompact : IsCompact (A ∪ range q) := hA.union (isCompact_range hq)
  obtain ⟨K, S, hK, _, hKD, _, hS, _, hfront, hretain, _⟩ :=
    wall e univ he hconn (by simpa only [frontier_univ] using isCompact_empty)
      hend (A ∪ range q) hcompact (subset_univ _)
  have hinside : A ∪ range q ⊆ interior K := by
    let u : ↥(univ : Set ↥Y) ≃ₜ ↥Y := Homeomorph.Set.univ ↥Y
    intro x hx
    have hx' : (⟨x, mem_univ x⟩ : ↥(univ : Set ↥Y)) ∈
        interior ((Subtype.val : ↥(univ : Set ↥Y) → ↥Y) ⁻¹' K) :=
      hretain (Or.inl hx)
    change (⟨x, mem_univ x⟩ : ↥(univ : Set ↥Y)) ∈
      interior ((u : ↥(univ : Set ↥Y) → ↥Y) ⁻¹' K) at hx'
    rw [← u.preimage_interior K] at hx'
    exact hx'
  have hsphere : Nonempty (ChartwisePLSphere e (frontier K)) := by
    simp only [frontier_univ, empty_union] at hfront
    rw [hfront]
    exact hS
  refine ⟨f, e, r, i, K, hf, he, hK, hKD, hsphere,
    fun x hx => hinside (Or.inl hx), hr, hr64, heq, ?_⟩
  intro x hx
  obtain ⟨z, hz, hzi, hzformula⟩ := hretained x hx
  refine ⟨z, hz, hinside (Or.inr ?_), hzi, hzformula⟩
  exact ⟨⟨x, mem_closedBall_zero_iff.mpr hx⟩, Subtype.ext hz.symm⟩

end PoincareConjecture.M76
