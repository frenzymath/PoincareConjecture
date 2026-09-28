import PoincareConjecture.Proofs.M25.Topology3D.Space3.SurgeryCapTag
import PoincareConjecture.Proofs.M25.Topology3D.Space3.BallNeighborhood
import PoincareConjecture.Proofs.M25.Topology3D.Space3.HeightPlaneProjection
import Mathlib.Algebra.BigOperators.Group.Finset.Basic











set_option autoImplicit false

open Set Metric
open scoped ContDiff Manifold Topology InnerProductSpace BigOperators

namespace PoincareConjecture.M25.Topology3D




structure FamilyCutState
    (P : SurgeryCapProfile) (u : UnitTwoSphere)
    (r : ℕ) (cut : Fin r → ℝ) (D : ℝ)
    (m0 : Fin r → ℕ)
    (B : (k : Fin r) → Fin (m0 k) → BallNeighborhoodChart E2 E2)
    (Phi : Fin r → ℝ → Diffeomorph 𝓘(ℝ, E2) 𝓘(ℝ, E2) E2 E2 ∞)
    (n : ℕ) (psi : Fin n → UnitTwoSphere × ℝ → E3) where
  buffer_pos : 0 < D
  buffers_separated : Pairwise (fun a b : Fin r =>
    Disjoint (Icc (cut a - D) (cut a + D))
      (Icc (cut b - D) (cut b + D)))
  planar_disjoint : ∀ k : Fin r, Pairwise (fun a b : Fin (m0 k) =>
    Disjoint (B k a).boundary (B k b).boundary)
  family_smooth : ∀ k : Fin r,
    ContDiff ℝ ∞ (fun p : ℝ × E2 => Phi k p.1 p.2)
  family_inverse : ∀ k : Fin r,
    ContDiff ℝ ∞ (fun p : ℝ × E2 => (Phi k p.1).symm p.2)
  embedding : ∀ i : Fin n, IsCollarEmbedding (psi i)
  central_disjoint : Pairwise (fun i j : Fin n =>
    Disjoint (range (fun q : UnitTwoSphere => psi i (q, 0)))
      (range (fun q : UnitTwoSphere => psi j (q, 0))))
  width : Fin r → ℝ
  width_pos : ∀ k : Fin r, 0 < width k
  width_le : ∀ k : Fin r, width k ≤ D
  count : Fin r → ℕ
  label : (k : Fin r) → Fin (count k) ↪ Fin (m0 k)
  level_eq : ∀ k : Fin r, ∀ z ∈ Ioo (cut k - width k) (cut k + width k),
    ∀ p : E2,
      (heightPlaneCoordinates u).symm (Phi k z p, z) ∈
        (⋃ i : Fin n, range (fun q : UnitTwoSphere => psi i (q, 0))) ↔
          p ∈ (⋃ a : Fin (count k), (B k (label k a)).boundary)
  capCount : ℕ
  owner : Fin capCount → Fin n
  cap : (a : Fin capCount) → SurgeryCapTag (psi (owner a)) u
  birth : Fin capCount → Fin r
  cap_profile : ∀ a : Fin capCount, (cap a).profile = P
  cap_cut : ∀ a : Fin capCount, (cap a).cutHeight = cut (birth a)
  cap_removal : ∀ a : Fin capCount, (cap a).removal ≤ D
  caps_disjoint : Pairwise (fun a b : Fin capCount =>
    Disjoint (cap a).cap (cap b).cap)
  caps_avoid : ∀ a : Fin capCount, ∀ k : Fin r, ∀ y ∈ (cap a).cap,
    width k ≤ |⟪(u : E3), y⟫_ℝ - cut k|



def FamilyCutState.measure
    {P : SurgeryCapProfile} {u : UnitTwoSphere}
    {r : ℕ} {cut : Fin r → ℝ} {D : ℝ}
    {m0 : Fin r → ℕ}
    {B : (k : Fin r) → Fin (m0 k) → BallNeighborhoodChart E2 E2}
    {Phi : Fin r → ℝ → Diffeomorph 𝓘(ℝ, E2) 𝓘(ℝ, E2) E2 E2 ∞}
    {n : ℕ} {psi : Fin n → UnitTwoSphere × ℝ → E3}
    (S : FamilyCutState P u r cut D m0 B Phi n psi) : ℕ :=
  ∑ k : Fin r, S.count k




theorem exists_initial_family_cut_state
    (P : SurgeryCapProfile) (u : UnitTwoSphere)
    (r : ℕ) (cut : Fin r → ℝ) (D : ℝ) (hD : 0 < D)
    (hseparated : Pairwise (fun a b : Fin r =>
      Disjoint (Icc (cut a - D) (cut a + D))
        (Icc (cut b - D) (cut b + D))))
    (m0 : Fin r → ℕ)
    (B : (k : Fin r) → Fin (m0 k) → BallNeighborhoodChart E2 E2)
    (hB : ∀ k : Fin r, Pairwise (fun a b : Fin (m0 k) =>
      Disjoint (B k a).boundary (B k b).boundary))
    (Phi : Fin r → ℝ → Diffeomorph 𝓘(ℝ, E2) 𝓘(ℝ, E2) E2 E2 ∞)
    (hPhi : ∀ k : Fin r,
      ContDiff ℝ ∞ (fun p : ℝ × E2 => Phi k p.1 p.2))
    (hinverse : ∀ k : Fin r,
      ContDiff ℝ ∞ (fun p : ℝ × E2 => (Phi k p.1).symm p.2))
    (n : ℕ) (psi : Fin n → UnitTwoSphere × ℝ → E3)
    (hembed : ∀ i : Fin n, IsCollarEmbedding (psi i))
    (hdisjoint : Pairwise (fun i j : Fin n =>
      Disjoint (range (fun q : UnitTwoSphere => psi i (q, 0)))
        (range (fun q : UnitTwoSphere => psi j (q, 0)))))
    (w : Fin r → ℝ) (hw : ∀ k : Fin r, 0 < w k)
    (hwD : ∀ k : Fin r, w k ≤ D)
    (hlevel : ∀ k : Fin r, ∀ z ∈ Ioo (cut k - w k) (cut k + w k),
      ∀ p : E2,
        (heightPlaneCoordinates u).symm (Phi k z p, z) ∈
          (⋃ i : Fin n, range (fun q : UnitTwoSphere => psi i (q, 0))) ↔
            p ∈ (⋃ a : Fin (m0 k), (B k a).boundary)) :
    ∃ S : FamilyCutState P u r cut D m0 B Phi n psi,
      S.count = m0 ∧ S.width = w ∧ S.capCount = 0 ∧
        (∀ k : Fin r, range (S.label k) = univ) ∧
        S.measure = ∑ k : Fin r, m0 k := by
  let S : FamilyCutState P u r cut D m0 B Phi n psi := {
    buffer_pos := hD
    buffers_separated := hseparated
    planar_disjoint := hB
    family_smooth := hPhi
    family_inverse := hinverse
    embedding := hembed
    central_disjoint := hdisjoint
    width := w
    width_pos := hw
    width_le := hwD
    count := m0
    label := fun _ => Function.Embedding.refl _
    level_eq := hlevel
    capCount := 0
    owner := Fin.elim0
    cap := fun a => Fin.elim0 a
    birth := Fin.elim0
    cap_profile := fun a => Fin.elim0 a
    cap_cut := fun a => Fin.elim0 a
    cap_removal := fun a => Fin.elim0 a
    caps_disjoint := fun a => Fin.elim0 a
    caps_avoid := fun a => Fin.elim0 a }
  refine ⟨S, rfl, rfl, rfl, ?_, rfl⟩
  intro k
  change range (fun a : Fin (m0 k) => a) = univ
  exact range_id

end PoincareConjecture.M25.Topology3D
