import PoincareConjecture.Proofs.M25.Topology3D.Space3.Decomposition.FamilyCutHistory
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Decomposition.FamilySourceAtlas










set_option autoImplicit false

open Set Metric
open scoped ContDiff Manifold InnerProductSpace

namespace PoincareConjecture.M25.Topology3D


theorem FamilySourceAtlas.exists_terminal_history
    (hP : PlanarSchoenfliesService)
    {original : UnitTwoSphere × ℝ → E3}
    {P : SurgeryCapProfile} {u : UnitTwoSphere}
    {r : ℕ} {cut : Fin r → ℝ} {D : ℝ}
    {m0 : Fin r → ℕ}
    {B : (k : Fin r) → Fin (m0 k) → BallNeighborhoodChart E2 E2}
    {Phi : Fin r → ℝ → Diffeomorph 𝓘(ℝ, E2) 𝓘(ℝ, E2) E2 E2 ∞}
    {n : ℕ} {psi : Fin n → UnitTwoSphere × ℝ → E3}
    {S : FamilyCutState P u r cut D m0 B Phi n psi}
    (A : FamilySourceAtlas original S)
    (K : Set E3) (hK : IsCompact K)
    (hmiss : ∀ k : Fin r, ∀ y ∈ K, ⟪(u : E3), y⟫_ℝ ≠ cut k) :
    ∃ m : ℕ, ∃ phi : Fin m → UnitTwoSphere × ℝ → E3,
      ∃ T : FamilyCutState P u r cut D m0 B Phi m phi,
        ∃ _A' : FamilySourceAtlas original T,
          ∃ history : FamilySurgeryHistory u psi phi,
            T.measure = 0 ∧ (∀ k : Fin r, T.count k = 0) ∧
              history.length = S.measure ∧ m = n + S.measure ∧
              T.capCount = S.capCount + 2 * S.measure ∧
              (∀ k : Fin r, T.width k ≤ S.width k) ∧
              ((⋃ a : Fin S.capCount, (S.cap a).cap) ⊆
                (⋃ b : Fin T.capCount, (T.cap b).cap)) ∧
              ∀ y ∈ K,
                (y ∈ (⋃ i : Fin m, range (fun q : UnitTwoSphere => phi i (q, 0)))) ↔
                  y ∈ (⋃ i : Fin n, range (fun q : UnitTwoSphere => psi i (q, 0))) := by
  classical
  generalize hmeasure : S.measure = M
  induction M using Nat.strong_induction_on generalizing n psi with
  | h M ih =>
    by_cases hzero : ∀ k : Fin r, S.count k = 0
    · have hz : S.measure = 0 := by simp [FamilyCutState.measure, hzero]
      have hMzero : M = 0 := hmeasure.symm.trans hz
      refine ⟨n, psi, S, A, .nil psi, hz, hzero, ?_, by simp [hMzero],
        by simp [hMzero], fun _ => le_rfl, subset_rfl, ?_⟩
      · exact hMzero.symm
      · intro y hy
        rfl
    · push Not at hzero
      obtain ⟨k, hk⟩ := hzero
      obtain ⟨_chosen, j, E, e, hcut, _hprofile, hwidth, _htube,
          hprotected, S', _hcount, hwidth', hdecrease, _hlabels, _hothers,
          hcapCount, gamma, hold, hnew, hunion, houter⟩ :=
        S.exists_surgery_step hP k (Nat.pos_of_ne_zero hk) K hK (hmiss k)
      obtain ⟨A1, _holdAtlas, _hchildAtlas⟩ := A.exists_surgery_step j E e S' gamma
        (fun a => (hold a).2.2.2.2.2.2.2)
        (fun i => ⟨(hnew i).1, (hnew i).2.2⟩)
      have hlt : S'.measure < M := by omega
      obtain ⟨m, phi, T, A', tail, hTzero, hcounts, hlength, hcard, hcaps,
          hwidths, hcapmono, hKeq⟩ := ih S'.measure hlt A1 rfl
      let history : FamilySurgeryHistory u psi phi := .cons psi j E e phi tail
      have hlen : history.length = M := by
        change tail.length + 1 = M
        omega
      refine ⟨m, phi, T, A', history, hTzero, hcounts, hlen, ?_, ?_, ?_, ?_, ?_⟩
      · omega
      · omega
      · intro l
        apply (hwidths l).trans
        rw [hwidth']
        by_cases hl : l = k
        · subst l
          simp only [Function.update_self]
          obtain ⟨_, hc, hck, hkw, _, _⟩ := E.parameter_bounds
          linarith only [hc, hck, hkw, hwidth]
        · simp only [Function.update_of_ne hl, le_refl]
      · apply Subset.trans ?_ hcapmono
        rw [hunion]
        exact subset_union_left
      · intro y hy
        apply (hKeq y hy).trans
        apply houter y
        simpa only [hcut] using hprotected y hy

end PoincareConjecture.M25.Topology3D
