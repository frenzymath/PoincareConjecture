import PoincareConjecture.Proofs.M25.Topology3D.Space3.Decomposition.InitialLevelFamily
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Decomposition.FamilyCutState

set_option autoImplicit false

open Set Metric
open scoped ContDiff Manifold Topology InnerProductSpace BigOperators

namespace PoincareConjecture.M25.Topology3D

theorem exists_initial_collar_cut_state
    (hP : PlanarSchoenfliesService)
    (psi : UnitTwoSphere × ℝ → E3) (hpsi : IsCollarEmbedding psi)
    (P : SurgeryCapProfile) (u : UnitTwoSphere)
    (r : ℕ) (cut : Fin r → ℝ) (D : ℝ) (hD : 0 < D)
    (hseparated : Pairwise (fun a b : Fin r =>
      Disjoint (Icc (cut a - D) (cut a + D))
        (Icc (cut b - D) (cut b + D))))
    (hregular : ∀ k : Fin r, ∀ q : UnitTwoSphere,
      ⟪(u : E3), psi (q, 0)⟫_ℝ = cut k →
        mfderiv (𝓡 2) 𝓘(ℝ, ℝ)
          (fun p : UnitTwoSphere => ⟪(u : E3), psi (p, 0)⟫_ℝ) q ≠ 0) :
    ∃ m0 : Fin r → ℕ,
      ∃ B : (k : Fin r) → Fin (m0 k) → BallNeighborhoodChart E2 E2,
        ∃ e : (k : Fin r) → Fin (m0 k) ≃
          ConnectedComponents (collarHeightLevel psi (u : E3) (cut k)),
          (∀ k : Fin r, ∀ a : Fin (m0 k),
            ∃ x : collarHeightLevel psi (u : E3) (cut k),
              ConnectedComponents.mk x = e k a ∧
              (fun p : E2 => (heightPlaneCoordinates u).symm (p, cut k)) ''
                (B k a).boundary =
                  ((↑) : collarHeightLevel psi (u : E3) (cut k) → E3) ''
                    connectedComponent x) ∧
          ∃ d : Fin r → ℝ, (∀ k : Fin r, 0 < d k) ∧
            ∃ Phi : Fin r → ℝ →
              Diffeomorph 𝓘(ℝ, E2) 𝓘(ℝ, E2) E2 E2 ∞,
              (∀ k : Fin r, ∀ p : E2, Phi k (cut k) p = p) ∧
              (∀ k : Fin r, ∀ z : ℝ,
                HasCompactSupport (fun p : E2 => Phi k z p - p)) ∧
              (∀ k : Fin r, ∀ z ∈ Ioo (cut k - d k) (cut k + d k),
                ∀ p : E2,
                  (heightPlaneCoordinates u).symm (Phi k z p, z) ∈
                    psi '' (univ ×ˢ ({0} : Set ℝ)) ↔
                      p ∈ (⋃ a : Fin (m0 k), (B k a).boundary)) ∧
              ∃ S : FamilyCutState P u r cut D m0 B Phi 1
                (fun _ : Fin 1 => psi),
                S.count = m0 ∧
                S.width = (fun k : Fin r => min D (d k / 2)) ∧
                S.capCount = 0 ∧
                (∀ k : Fin r, range (S.label k) = univ) ∧
                S.measure = ∑ k : Fin r, m0 k := by
  classical
  choose m0 B e hB hcomponents d hd Phi hPhi hinverse hidentity hsupport hlevel using
    fun k : Fin r => exists_regular_collar_band_family hP psi hpsi u (cut k) (hregular k)
  let w : Fin r → ℝ := fun k => min D (d k / 2)
  have hw (k : Fin r) : 0 < w k := lt_min hD (half_pos (hd k))
  have hwD (k : Fin r) : w k ≤ D := min_le_left _ _
  have hwd (k : Fin r) : w k < d k :=
    (min_le_right _ _).trans_lt (half_lt_self (hd k))
  have hunion : (⋃ _i : Fin 1, range (fun q : UnitTwoSphere => psi (q, 0))) =
      psi '' (univ ×ˢ ({0} : Set ℝ)) := by
    ext y
    constructor
    · intro hy
      obtain ⟨_i, q, rfl⟩ := mem_iUnion.mp hy
      exact ⟨(q, 0), ⟨mem_univ _, rfl⟩, rfl⟩
    · rintro ⟨⟨q, s⟩, hs, rfl⟩
      have hs0 : s = 0 := hs.2
      subst s
      exact mem_iUnion.mpr ⟨0, q, rfl⟩
  have hdisjoint : Pairwise (fun _i _j : Fin 1 =>
      Disjoint (range (fun q : UnitTwoSphere => psi (q, 0)))
        (range (fun q : UnitTwoSphere => psi (q, 0)))) := by
    intro i j hij
    exact False.elim (hij (Subsingleton.elim i j))
  have hlevel' : ∀ k : Fin r, ∀ z ∈ Ioo (cut k - w k) (cut k + w k), ∀ p : E2,
      (heightPlaneCoordinates u).symm (Phi k z p, z) ∈
        (⋃ _i : Fin 1, range (fun q : UnitTwoSphere => psi (q, 0))) ↔
          p ∈ (⋃ a : Fin (m0 k), (B k a).boundary) := by
    intro k z hz p
    rw [hunion]
    apply hlevel k z
    constructor <;> linarith only [hwd k, hz.1, hz.2]
  obtain ⟨S, hcount, hwidth, hcapCount, hlabels, hmeasure⟩ :=
    exists_initial_family_cut_state P u r cut D hD hseparated m0 B hB Phi hPhi hinverse
      1 (fun _ : Fin 1 => psi) (fun _ => hpsi) hdisjoint w hw hwD hlevel'
  exact ⟨m0, B, e, hcomponents, d, hd, Phi, hidentity, hsupport, hlevel,
    S, hcount, hwidth, hcapCount, hlabels, hmeasure⟩

end PoincareConjecture.M25.Topology3D
