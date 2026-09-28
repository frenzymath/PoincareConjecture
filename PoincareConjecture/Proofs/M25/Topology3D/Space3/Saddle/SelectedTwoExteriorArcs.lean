import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.SelectedWallNoBypass
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.SourceCircleCut
import Mathlib.Tactic

set_option autoImplicit false

open Set Function
open scoped ContDiff Manifold InnerProductSpace

namespace PoincareConjecture.M25.Topology3D

theorem exists_saddle_selected_two_exterior_arcs
    (psi : UnitTwoSphere × ℝ → E3) (hpsi : IsCollarEmbedding psi)
    (u : UnitTwoSphere) (D : SaddlePieceData psi u)
    (R delta : ℝ) (hR : 0 < R) (hdelta : 0 < delta)
    (hdeltaSmall : delta ≤ ((5 * R / 8) ^ 2) / 128)
    (hmorse : {s : ℝ × ℝ | s.1 ^ 2 + s.2 ^ 2 < (2 * R) ^ 2} ⊆ D.morse.target)
    (hcoreBand : ∀ q : UnitTwoSphere,
      |⟪(u : E3), psi (q, 0)⟫_ℝ - ⟪(u : E3), psi (D.point, 0)⟫_ℝ| ≤
        3 * delta → q ∈ D.sourceCore)
    (N : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ))
    (hN : ∀ s : ℝ × ℝ,
      N (N s) = s ∧
      (N s).1 ^ 2 + (N s).2 ^ 2 = s.1 ^ 2 + s.2 ^ 2 ∧
      D.morseSign1 * (N s).1 ^ 2 + D.morseSign2 * (N s).2 ^ 2 =
        s.1 ^ 2 - s.2 ^ 2)
    (q : Fin 2 → UnitCircle → UnitTwoSphere)
    (hq : ∀ j : Fin 2,
      ContMDiff (𝓡 1) (𝓡 2) ∞ (q j) ∧ Function.Injective (q j) ∧
      ∀ theta : UnitCircle, Function.Injective (mfderiv (𝓡 1) (𝓡 2) (q j) theta))
    (hdisjoint : ∀ i j : Fin 2, i ≠ j → Disjoint (range (q i)) (range (q j)))
    (gamma : Fin 2 → unitInterval → UnitTwoSphere)
    (hgamma : ∀ i : Fin 2, Continuous (gamma i) ∧ Function.Injective (gamma i))
    (hgdisjoint : Disjoint (range (gamma 0)) (range (gamma 1)))
    (p : Fin 4 → UnitTwoSphere)
    (hend : ∀ i : Fin 2,
      gamma i 0 = p (finProdFinEquiv (i, (0 : Fin 2))) ∧
      gamma i 1 = p (finProdFinEquiv (i, (1 : Fin 2))))
    (V : Set UnitTwoSphere) :
    let f : UnitTwoSphere → ℝ := fun x => ⟪(u : E3), psi (x, 0)⟫_ℝ
    let c := f D.point
    let rho := 5 * R / 8
    let Dc : Set UnitTwoSphere := D.morse.symm ''
      {s : ℝ × ℝ | s.1 ^ 2 + s.2 ^ 2 ≤ rho ^ 2}
    let La : Set UnitTwoSphere := {x | f x = c - delta}
    let ep : Fin 2 × Fin 2 ≃ Fin 4 := finProdFinEquiv
    (⋃ j : Fin 2, range (q j)) = La →
    (⋃ j : Fin 2, range (q j)) ∩ Dc = ⋃ i : Fin 2, range (gamma i) →
    (⋃ j : Fin 2, range (q j)) ∩ V =
      ⋃ i : Fin 2, gamma i '' Ioo (0 : unitInterval) 1 →
    ∃ (label : Fin 2 ≃ Fin 2) (a v : Fin 2 → ℝ)
      (ends : Fin 2 × Fin 2 ≃ Fin 4) (eta : ℝ),
    let alpha : Fin 2 → ℝ → UnitTwoSphere := fun k t =>
      q (label k) (complexUnitCircleHomeomorph (Circle.exp (a k + v k * t)))
    Function.Injective p ∧ 0 < eta ∧ eta < 1 / 8 ∧
    (∀ i : Fin 2, range (gamma i) ⊆ range (q (label i))) ∧
    (∀ k : Fin 2,
      0 < |v k| ∧ |v k| < 2 * Real.pi ∧
      ContMDiff 𝓘(ℝ, ℝ) (𝓡 2) ∞ (alpha k) ∧
      (∀ t : ℝ, Function.Injective
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 2) (alpha k) t)) ∧
      Set.InjOn (alpha k) (Icc (-eta) (1 + eta)) ∧
      alpha k 0 = p (ends (k, 0)) ∧
      alpha k 1 = p (ends (k, 1)) ∧
      Disjoint (alpha k '' Ioo (0 : ℝ) 1) Dc ∧
      (alpha k '' Icc (0 : ℝ) 1) ∩ Dc =
        {p (ends (k, 0)), p (ends (k, 1))} ∧
      (∀ s ∈ Ioo (-eta) (0 : ℝ), alpha k s ∈ V) ∧
      (∀ s ∈ Ioo (1 : ℝ) (1 + eta), alpha k s ∈ V)) ∧
    Disjoint (alpha 0 '' Icc (-eta) (1 + eta))
      (alpha 1 '' Icc (-eta) (1 + eta)) ∧
    La \ V = ⋃ k : Fin 2, alpha k '' Icc (0 : ℝ) 1 ∧
    La ∩ (Dc \ V) = range p ∧
    ∀ k : Fin 2,
      ({ends (k, 0), ends (k, 1)} : Set (Fin 4)) = {ep (k, 0), ep (k, 1)} := by
  classical
  dsimp only
  intro hlevel hclosed hopen
  let f : UnitTwoSphere → ℝ := fun x => ⟪(u : E3), psi (x, 0)⟫_ℝ
  let c := f D.point
  let rho := 5 * R / 8
  let Dc : Set UnitTwoSphere := D.morse.symm ''
    {s : ℝ × ℝ | s.1 ^ 2 + s.2 ^ 2 ≤ rho ^ 2}
  let La : Set UnitTwoSphere := {x | f x = c - delta}
  change (⋃ j : Fin 2, range (q j)) = La at hlevel
  change (⋃ j : Fin 2, range (q j)) ∩ Dc = ⋃ i : Fin 2, range (gamma i) at hclosed
  have hqLa (j : Fin 2) : range (q j) ⊆ La := by
    intro y hy
    rw [← hlevel]
    exact mem_iUnion.mpr ⟨j, hy⟩
  have hqCompact (j : Fin 2) : IsCompact (range (q j)) :=
    isCompact_range (hq j).1.continuous
  have hcomplement (j : Fin 2) :
      La \ range (q j) = ⋃ k : {k : Fin 2 // k ≠ j}, range (q k.1) := by
    ext y
    constructor
    · rintro ⟨hy, hnot⟩
      rw [← hlevel] at hy
      obtain ⟨k, hk⟩ := mem_iUnion.mp hy
      have hkj : k ≠ j := by
        intro heq
        subst k
        exact hnot hk
      exact mem_iUnion.mpr ⟨⟨k, hkj⟩, hk⟩
    · intro hy
      obtain ⟨k, hk⟩ := mem_iUnion.mp hy
      exact ⟨hqLa k.1 hk, fun hj => disjoint_left.mp (hdisjoint k.1 j k.2) hk hj⟩
  have hcomplementCompact (j : Fin 2) : IsCompact (La \ range (q j)) := by
    rw [hcomplement j]
    exact isCompact_iUnion (fun k => hqCompact k.1)
  have hnoBypass (j : Fin 2) : ¬ Disjoint (range (q j)) Dc := by
    intro hj
    have hempty : range (q j) = ∅ :=
      saddle_selected_wall_no_bypass psi hpsi u D R delta hR hdelta hdeltaSmall
        hmorse hcoreBand N hN (range (q j)) (hqLa j) (hqCompact j)
        (hcomplementCompact j) hj
    have hnonempty : (range (q j)).Nonempty :=
      ⟨q j (circleDirection (0 : E2)), circleDirection (0 : E2), rfl⟩
    exact hnonempty.ne_empty hempty
  obtain ⟨removedParent, arcParent, a, v, ends, eta, hpi, heta, hetaSmall,
      hparent, harcs, harcsDisjoint, harcBypass, hbiff, hcover, hrim, hcard,
      hdifferent, hsame⟩ :=
    exists_saddle_source_circle_cut 2 q hq hdisjoint gamma hgamma hgdisjoint
      p hend V Dc hclosed hopen
  let bypass : Finset (Fin 2) := Finset.univ \ {removedParent 0, removedParent 1}
  change (∀ j : Fin 2, j ∈ bypass ↔ Disjoint (range (q j)) Dc) at hbiff
  have hbempty : bypass = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro j hj
    exact hnoBypass j ((hbiff j).mp hj)
  change bypass.card + (if removedParent 0 = removedParent 1 then 1 else 2) = 2 at hcard
  have hdistinct : removedParent 0 ≠ removedParent 1 := by
    intro heq
    norm_num [hbempty, heq] at hcard
  have hremoved : Injective removedParent := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · rfl
    · exact False.elim (hdistinct hij)
    · exact False.elim (hdistinct hij.symm)
    · rfl
  let label : Fin 2 ≃ Fin 2 := Equiv.ofBijective removedParent
    ⟨hremoved, Finite.surjective_of_injective hremoved⟩
  obtain ⟨harcParent, hpairs⟩ := hdifferent hdistinct
  subst arcParent
  let alpha : Fin 2 → ℝ → UnitTwoSphere := fun k t =>
    q (label k) (complexUnitCircleHomeomorph (Circle.exp (a k + v k * t)))
  have hbunion : (⋃ j ∈ bypass, range (q j)) = (∅ : Set UnitTwoSphere) := by
    rw [hbempty]
    simp
  have hcover' : La \ V = (⋃ k : Fin 2, alpha k '' Icc (0 : ℝ) 1) ∪
      (⋃ j ∈ bypass, range (q j)) := by
    rw [← hlevel]
    exact hcover
  rw [hbunion, union_empty] at hcover'
  have hrim' : La ∩ (Dc \ V) = range p := by
    rw [← hlevel]
    exact hrim
  exact ⟨label, a, v, ends, eta, hpi, heta, hetaSmall, hparent, harcs,
    harcsDisjoint, hcover', hrim', hpairs⟩

end PoincareConjecture.M25.Topology3D
