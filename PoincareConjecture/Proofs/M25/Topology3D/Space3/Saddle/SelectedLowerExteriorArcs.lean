import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.LowerSourceCircles
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.SelectedLowerHyperbola
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.SelectedTwoExteriorArcs

set_option autoImplicit false

open Set Function
open scoped ContDiff Manifold InnerProductSpace Matrix

namespace PoincareConjecture.M25.Topology3D

theorem exists_saddle_selected_lower_exterior_arcs
    (psi : UnitTwoSphere × ℝ → E3) (hpsi : IsCollarEmbedding psi)
    (u : UnitTwoSphere) (D : SaddlePieceData psi u)
    (W : SaddleLowerLevelData D)
    (R delta : ℝ) (hR : 0 < R) (hdelta : 0 < delta)
    (hsmall : delta ≤ (5 * R / 8) ^ 2 / 128)
    (hla : W.level ≤ ⟪(u : E3), psi (D.point, 0)⟫_ℝ - delta)
    (hmorse : {s : ℝ × ℝ | s.1 ^ 2 + s.2 ^ 2 < (2 * R) ^ 2} ⊆
      D.morse.target)
    (hcoreBand : ∀ q : UnitTwoSphere,
      |⟪(u : E3), psi (q, 0)⟫_ℝ - ⟪(u : E3), psi (D.point, 0)⟫_ℝ| ≤
        3 * delta → q ∈ D.sourceCore)
    (N : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ))
    (hN : ∀ s : ℝ × ℝ,
      N (N s) = s ∧
      (N s).1 ^ 2 + (N s).2 ^ 2 = s.1 ^ 2 + s.2 ^ 2 ∧
      D.morseSign1 * (N s).1 ^ 2 + D.morseSign2 * (N s).2 ^ 2 =
        s.1 ^ 2 - s.2 ^ 2) :
    let j : UnitTwoSphere → E3 := fun q => psi (q, 0)
    let f : UnitTwoSphere → ℝ := fun q => ⟪(u : E3), j q⟫_ℝ
    let c := f D.point
    let L := heightPlaneCoordinates u
    let pi := horizontalBandProjection u
    let c0 : Fin 2 → UnitCircle → E2 := fun i theta =>
      pi (j (W.leg i (theta, W.level)))
    let mid := (W.level + (c - delta)) / 2
    let rho := 5 * R / 8
    let m : ℝ × ℝ → UnitTwoSphere := fun s => D.morse.symm (N s)
    let aa := Real.sqrt ((rho ^ 2 - delta) / 2)
    let bb := Real.sqrt ((rho ^ 2 + delta) / 2)
    let sg : Fin 2 → ℝ := ![1, -1]
    let sx : Fin 4 → ℝ := ![1, -1, -1, 1]
    let sy : Fin 4 → ℝ := ![1, 1, -1, -1]
    let vv : unitInterval → ℝ := fun t => aa * (1 - 2 * (t : ℝ))
    let gamma : Fin 2 → unitInterval → UnitTwoSphere := fun i t =>
      m (sg i * vv t, sg i * Real.sqrt ((vv t) ^ 2 + delta))
    let p : Fin 4 → UnitTwoSphere := fun i => m (sx i * aa, sy i * bb)
    let Dc : Set UnitTwoSphere := D.morse.symm ''
      {s : ℝ × ℝ | s.1 ^ 2 + s.2 ^ 2 ≤ rho ^ 2}
    let V : Set UnitTwoSphere := D.morse.symm ''
      {s : ℝ × ℝ | s.1 ^ 2 + s.2 ^ 2 < rho ^ 2}
    let La : Set UnitTwoSphere := {q | f q = c - delta}
    (∀ q : UnitTwoSphere, f q ∈ Icc W.level (c - delta) →
      q ∈ D.sourceCore ∧ mfderiv (𝓡 2) 𝓘(ℝ, ℝ) f q ≠ 0) ∧
    (∀ i : Fin 2, IsPlanarEmbedding (c0 i) ∧ range (c0 i) = (W.disc i).boundary) ∧
    ∃ (d : ℝ)
      (T : ℝ → Diffeomorph 𝓘(ℝ, E2) 𝓘(ℝ, E2) E2 E2 ∞)
      (q : Fin 2 → UnitCircle → UnitTwoSphere)
      (label : Fin 2 ≃ Fin 2) (a v : Fin 2 → ℝ)
      (ends : Fin 2 × Fin 2 ≃ Fin 4) (eta : ℝ),
    let C : Fin 2 → ℝ → UnitCircle → E2 := fun i z theta => T z (c0 i theta)
    let B : ℝ → Fin 2 → BallNeighborhoodChart E2 E2 :=
      fun z i => (W.disc i).mapDiffeomorph (T z)
    let alpha : Fin 2 → ℝ → UnitTwoSphere := fun k t =>
      q (label k) (complexUnitCircleHomeomorph (Circle.exp (a k + v k * t)))
    0 < d ∧ Icc W.level (c - delta) ⊆ Ioo (mid - d) (mid + d) ∧
    ContDiff ℝ ∞ (fun z : ℝ × E2 => T z.1 z.2) ∧
    ContDiff ℝ ∞ (fun z : ℝ × E2 => (T z.1).symm z.2) ∧
    (∀ x : E2, T W.level x = x) ∧
    (∀ z : ℝ, HasCompactSupport (fun x => T z x - x) ∧
      HasCompactSupport (fun x => (T z).symm x - x)) ∧
    (∀ i : Fin 2,
      ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 1)) 𝓘(ℝ, E2) ∞
        (fun z : ℝ × UnitCircle => C i z.1 z.2) ∧
      ∀ z : ℝ, IsPlanarEmbedding (C i z) ∧ range (C i z) = (B z i).boundary) ∧
    (∀ z : ℝ, Disjoint (B z 0).boundary (B z 1).boundary) ∧
    (∀ z ∈ Ioo (mid - d) (mid + d), ∀ x : E2,
      (L.symm (T z x, z) ∈ range j ↔ L.symm (x, W.level) ∈ range j)) ∧
    (∀ z ∈ Ioo (mid - d) (mid + d),
      {x : E2 | L.symm (x, z) ∈ range j} = ⋃ i : Fin 2, (B z i).boundary) ∧
    (∀ z : ℝ,
      (Disjoint (B z 0).closedRegion (B z 1).closedRegion ↔
        Disjoint (W.disc 0).closedRegion (W.disc 1).closedRegion) ∧
      ((B z 0).closedRegion ⊆ (B z 1).inside ↔
        (W.disc 0).closedRegion ⊆ (W.disc 1).inside) ∧
      ((B z 1).closedRegion ⊆ (B z 0).inside ↔
        (W.disc 1).closedRegion ⊆ (W.disc 0).inside)) ∧
    (∀ i : Fin 2,
      ContMDiff (𝓡 1) (𝓡 2) ∞ (q i) ∧ Function.Injective (q i) ∧
      ∀ theta : UnitCircle,
        Function.Injective (mfderiv (𝓡 1) (𝓡 2) (q i) theta)) ∧
    (∀ i k : Fin 2, i ≠ k → Disjoint (range (q i)) (range (q k))) ∧
    (⋃ i : Fin 2, range (q i)) = La ∧
    (∀ (i : Fin 2) (theta : UnitCircle),
      j (q i theta) = L.symm (T (c - delta) (c0 i theta), c - delta)) ∧
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
      ({ends (k, 0), ends (k, 1)} : Set (Fin 4)) =
        {finProdFinEquiv (k, (0 : Fin 2)), finProdFinEquiv (k, (1 : Fin 2))} := by
  classical
  let j : UnitTwoSphere → E3 := fun q => psi (q, 0)
  let f : UnitTwoSphere → ℝ := fun q => ⟪(u : E3), j q⟫_ℝ
  let c := f D.point
  let rho := 5 * R / 8
  let m : ℝ × ℝ → UnitTwoSphere := fun s => D.morse.symm (N s)
  let aa := Real.sqrt ((rho ^ 2 - delta) / 2)
  let bb := Real.sqrt ((rho ^ 2 + delta) / 2)
  let sg : Fin 2 → ℝ := ![1, -1]
  let sx : Fin 4 → ℝ := ![1, -1, -1, 1]
  let sy : Fin 4 → ℝ := ![1, 1, -1, -1]
  let vv : unitInterval → ℝ := fun t => aa * (1 - 2 * (t : ℝ))
  let gamma : Fin 2 → unitInterval → UnitTwoSphere := fun i t =>
    m (sg i * vv t, sg i * Real.sqrt ((vv t) ^ 2 + delta))
  let p : Fin 4 → UnitTwoSphere := fun i => m (sx i * aa, sy i * bb)
  let V : Set UnitTwoSphere := D.morse.symm ''
    {s : ℝ × ℝ | s.1 ^ 2 + s.2 ^ 2 < rho ^ 2}
  let La : Set UnitTwoSphere := {q | f q = c - delta}
  have hac : c - delta < c := by linarith
  obtain ⟨hreg, hc0, d, T, q, hd, hI, hTs, hTi, hT0, hSupp, hC, hDis,
    hMembership, hCover, hCases, hq, hqpair, hqlevel, hqr⟩ :=
    exists_saddle_lower_source_circles psi hpsi u D W (c - delta) hla hac
  change (⋃ i : Fin 2, range (q i)) = La at hqlevel
  obtain ⟨hgamma, hgdis, hgend, hnegative, hnegativeOpen⟩ :=
    saddle_selected_lower_hyperbola_arcs psi u D R delta hR hdelta hsmall hmorse N hN
  obtain ⟨label, a, v, ends, eta, hp, heta, hetaSmall, hparent, harcs,
    haDis, hexterior, hrim, hpairs⟩ :=
    exists_saddle_selected_two_exterior_arcs psi hpsi u D R delta hR hdelta hsmall
      hmorse hcoreBand N hN q hq hqpair gamma hgamma hgdis p hgend V hqlevel
      (by rw [hqlevel]; exact hnegative) (by rw [hqlevel]; exact hnegativeOpen)
  exact ⟨hreg, hc0, d, T, q, label, a, v, ends, eta, hd, hI, hTs, hTi, hT0,
    hSupp, hC, hDis, hMembership, hCover, hCases, hq, hqpair, hqlevel, hqr,
    hp, heta, hetaSmall, hparent, harcs, haDis, hexterior, hrim, hpairs⟩

end PoincareConjecture.M25.Topology3D
