import PoincareConjecture.Proofs.M25.Topology3D.Space3.Decomposition.FamilyCutHistory
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Decomposition.NativeCapCore
import Mathlib.Topology.Order.IntermediateValue










set_option autoImplicit false

open Set Metric
open scoped ContDiff Manifold InnerProductSpace

namespace PoincareConjecture.M25.Topology3D


theorem FamilyCutState.component_cut_side
    {P : SurgeryCapProfile} {u : UnitTwoSphere}
    {r : ℕ} {cut : Fin r → ℝ} {D : ℝ}
    {m0 : Fin r → ℕ}
    {B : (k : Fin r) → Fin (m0 k) → BallNeighborhoodChart E2 E2}
    {Phi : Fin r → ℝ → Diffeomorph 𝓘(ℝ, E2) 𝓘(ℝ, E2) E2 E2 ∞}
    {n : ℕ} {psi : Fin n → UnitTwoSphere × ℝ → E3}
    (S : FamilyCutState P u r cut D m0 B Phi n psi)
    (k : Fin r) (hk : S.count k = 0) :
    ∀ i : Fin n,
      (∀ q : UnitTwoSphere, cut k < ⟪(u : E3), psi i (q, 0)⟫_ℝ) ∨
        (∀ q : UnitTwoSphere, ⟪(u : E3), psi i (q, 0)⟫_ℝ < cut k) := by
  classical
  have hdim : 1 < Module.rank ℝ E3 :=
    Module.one_lt_rank_of_one_lt_finrank (by simp [E3])
  let : ConnectedSpace UnitTwoSphere :=
    Subtype.connectedSpace (isConnected_sphere hdim (0 : E3) (by norm_num))
  intro i
  let f : UnitTwoSphere → ℝ := fun q => ⟪(u : E3), psi i (q, 0)⟫_ℝ
  have hf : Continuous f :=
    (InnerProductSpace.toDual ℝ E3 (u : E3)).continuous.comp
      (collar_central_contMDiff (psi i) (S.embedding i)).continuous
  have hne (q : UnitTwoSphere) : f q ≠ cut k := by
    intro hq
    have hgap := S.height_gap_of_count_eq_zero k hk i q
    change S.width k ≤ |f q - cut k| at hgap
    rw [hq, sub_self, abs_zero] at hgap
    exact (not_le_of_gt (S.width_pos k)) hgap
  change (∀ q : UnitTwoSphere, cut k < f q) ∨ (∀ q : UnitTwoSphere, f q < cut k)
  by_cases habove : ∀ q : UnitTwoSphere, cut k < f q
  · exact Or.inl habove
  · right
    push Not at habove
    obtain ⟨p, hp⟩ := habove
    intro q
    by_contra hq
    have hmem : cut k ∈ f '' (univ : Set UnitTwoSphere) :=
      isPreconnected_univ.intermediate_value (mem_univ p) (mem_univ q)
        hf.continuousOn ⟨hp, le_of_not_gt hq⟩
    obtain ⟨z, _hz, heq⟩ := hmem
    exact hne z heq


theorem FamilyCutState.cap_points_on_birth_side
    {P : SurgeryCapProfile} {u : UnitTwoSphere}
    {r : ℕ} {cut : Fin r → ℝ} {D : ℝ}
    {m0 : Fin r → ℕ}
    {B : (k : Fin r) → Fin (m0 k) → BallNeighborhoodChart E2 E2}
    {Phi : Fin r → ℝ → Diffeomorph 𝓘(ℝ, E2) 𝓘(ℝ, E2) E2 E2 ∞}
    {n : ℕ} {psi : Fin n → UnitTwoSphere × ℝ → E3}
    (S : FamilyCutState P u r cut D m0 B Phi n psi)
    (a : Fin S.capCount) (ha : S.count (S.birth a) = 0) :
    ((S.cap a).sign = 1 ∧
      ∀ q : UnitTwoSphere,
        (S.cap a).cutHeight < ⟪(u : E3), psi (S.owner a) (q, 0)⟫_ℝ) ∨
      ((S.cap a).sign = -1 ∧
        ∀ q : UnitTwoSphere,
          ⟪(u : E3), psi (S.owner a) (q, 0)⟫_ℝ < (S.cap a).cutHeight) := by
  let C := S.cap a
  obtain ⟨q, hq⟩ := C.sourceSeam_isConnected.nonempty
  have hy : psi (S.owner a) (q, 0) ∈ C.seam := ⟨q, hq, rfl⟩
  rw [C.seam_eq_image, surgery_cap_equator_image] at hy
  obtain ⟨⟨x, z⟩, ⟨hx, hz⟩, heq⟩ := hy
  have hz' : z = C.cutHeight + C.sign * C.removal := hz
  have hsource : (x, z) ∈ C.tube.source :=
    C.tube_source ⟨mem_closedBall_zero_iff.mpr (mem_sphere_zero_iff_norm.mp hx).le,
      mem_univ _⟩
  have hheight : ⟪(u : E3), psi (S.owner a) (q, 0)⟫_ℝ =
      C.cutHeight + C.sign * C.removal := by
    rw [← heq, C.tube_height _ hsource, hz']
  have hsign : C.sign = 1 ∨ C.sign = -1 := by
    apply abs_eq_abs.mp
    simpa only [abs_one] using C.sign_abs
  have hcut : C.cutHeight = cut (S.birth a) := S.cap_cut a
  rcases S.component_cut_side (S.birth a) ha (S.owner a) with habove | hbelow
  · have hside : ∀ p : UnitTwoSphere,
        C.cutHeight < ⟪(u : E3), psi (S.owner a) (p, 0)⟫_ℝ := by
      rw [hcut]
      exact habove
    refine Or.inl ⟨?_, hside⟩
    rcases hsign with h | h
    · exact h
    · have hh := hside q
      rw [hheight, h] at hh
      linarith [C.removal_pos]
  · have hside : ∀ p : UnitTwoSphere,
        ⟪(u : E3), psi (S.owner a) (p, 0)⟫_ℝ < C.cutHeight := by
      rw [hcut]
      exact hbelow
    refine Or.inr ⟨?_, hside⟩
    rcases hsign with h | h
    · have hh := hside q
      rw [hheight, h] at hh
      linarith [C.removal_pos]
    · exact h

end PoincareConjecture.M25.Topology3D
