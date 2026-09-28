import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.HyperbolaDiscArcs











set_option autoImplicit false

open Set Function
open scoped ContDiff Manifold InnerProductSpace Matrix

namespace PoincareConjecture.M25.Topology3D




theorem saddle_selected_lower_hyperbola_arcs
    (psi : UnitTwoSphere × ℝ → E3) (u : UnitTwoSphere)
    (D : SaddlePieceData psi u)
    (R delta : ℝ) (hR : 0 < R) (hdelta : 0 < delta)
    (hsmall : delta ≤ (5 * R / 8) ^ 2 / 128)
    (hmorse : {s : ℝ × ℝ | s.1 ^ 2 + s.2 ^ 2 < (2 * R) ^ 2} ⊆
      D.morse.target)
    (N : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ))
    (hN : ∀ s : ℝ × ℝ,
      N (N s) = s ∧
      (N s).1 ^ 2 + (N s).2 ^ 2 = s.1 ^ 2 + s.2 ^ 2 ∧
      D.morseSign1 * (N s).1 ^ 2 + D.morseSign2 * (N s).2 ^ 2 =
        s.1 ^ 2 - s.2 ^ 2) :
    let f : UnitTwoSphere → ℝ := fun q => ⟪(u : E3), psi (q, 0)⟫_ℝ
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
    let Dc : Set UnitTwoSphere := D.morse.symm ''
      {s : ℝ × ℝ | s.1 ^ 2 + s.2 ^ 2 ≤ rho ^ 2}
    let V : Set UnitTwoSphere := D.morse.symm ''
      {s : ℝ × ℝ | s.1 ^ 2 + s.2 ^ 2 < rho ^ 2}
    let La : Set UnitTwoSphere := {q | f q = c - delta}
    (∀ i : Fin 2, Continuous (gamma i) ∧ Function.Injective (gamma i)) ∧
    Disjoint (range (gamma 0)) (range (gamma 1)) ∧
    (∀ i : Fin 2,
      gamma i 0 = p (finProdFinEquiv (i, (0 : Fin 2))) ∧
      gamma i 1 = p (finProdFinEquiv (i, (1 : Fin 2)))) ∧
    La ∩ Dc = ⋃ i : Fin 2, range (gamma i) ∧
    La ∩ V = ⋃ i : Fin 2, gamma i '' Ioo (0 : unitInterval) 1 := by
  classical
  let f : UnitTwoSphere → ℝ := fun q => ⟪(u : E3), psi (q, 0)⟫_ℝ
  let c := f D.point
  let rho := 5 * R / 8
  let r2 : ℝ × ℝ → ℝ := fun s => s.1 ^ 2 + s.2 ^ 2
  let Bc : Set (ℝ × ℝ) := {s | r2 s ≤ rho ^ 2}
  let Bo : Set (ℝ × ℝ) := {s | r2 s < rho ^ 2}
  let m : ℝ × ℝ → UnitTwoSphere := fun s => D.morse.symm (N s)
  let Dc : Set UnitTwoSphere := D.morse.symm '' Bc
  let V : Set UnitTwoSphere := D.morse.symm '' Bo
  let La : Set UnitTwoSphere := {q | f q = c - delta}
  have hrho : 0 < rho := by dsimp [rho]; positivity
  have hdsmall : delta < rho ^ 2 := by
    change delta ≤ rho ^ 2 / 128 at hsmall
    nlinarith [sq_pos_of_pos hrho]
  have hBoBc : Bo ⊆ Bc := by
    intro s hs
    exact (show r2 s < rho ^ 2 from hs).le
  have hNr (s : ℝ × ℝ) : r2 (N s) = r2 s := (hN s).2.1
  have hNs (s : ℝ × ℝ) (hs : s ∈ Bc) : N s ∈ D.morse.target := by
    apply hmorse
    change r2 (N s) < (2 * R) ^ 2
    rw [hNr s]
    change r2 s ≤ rho ^ 2 at hs
    dsimp [rho] at hs
    nlinarith [sq_pos_of_pos hR]
  have hmcont : ContinuousOn m Bc :=
    D.morse.symm.continuousOn.comp N.continuous.continuousOn (fun s hs => hNs s hs)
  have hminj : InjOn m Bc := by
    intro s hs t ht hst
    exact N.injective (D.morse.symm.injOn (hNs s hs) (hNs t ht) hst)
  have hmheight (s : ℝ × ℝ) (hs : s ∈ Bc) :
      f (m s) = c + (s.1 ^ 2 - s.2 ^ 2) := by
    have hh := D.morse_height (m s) (D.morse.map_target (hNs s hs))
    change f (m s) = c + D.morseSign1 * (D.morse (m s)).1 ^ 2 +
      D.morseSign2 * (D.morse (m s)).2 ^ 2 at hh
    have hmrec : D.morse (m s) = N s := D.morse.right_inv (hNs s hs)
    rw [hmrec] at hh
    have hn := (hN s).2.2
    linarith
  have hnormalize (Z : Set (ℝ × ℝ)) (hZ : ∀ s, s ∈ Z ↔ N s ∈ Z) :
      D.morse.symm '' Z = m '' Z := by
    ext q
    constructor
    · rintro ⟨s, hs, rfl⟩
      refine ⟨N s, (hZ s).mp hs, ?_⟩
      change D.morse.symm (N (N s)) = D.morse.symm s
      rw [(hN s).1]
    · rintro ⟨s, hs, rfl⟩
      exact ⟨N s, (hZ s).mp hs, rfl⟩
  have hDc : Dc = m '' Bc := hnormalize Bc (fun s => by
    change r2 s ≤ rho ^ 2 ↔ r2 (N s) ≤ rho ^ 2
    rw [hNr s])
  have hV : V = m '' Bo := hnormalize Bo (fun s => by
    change r2 s < rho ^ 2 ↔ r2 (N s) < rho ^ 2
    rw [hNr s])
  have hcut (Z : Set (ℝ × ℝ)) (hZ : Z ⊆ Bc) :
      La ∩ m '' Z =
        m '' {s : ℝ × ℝ | s.1 ^ 2 - s.2 ^ 2 = -delta ∧ s ∈ Z} := by
    ext q
    constructor
    · rintro ⟨hq, s, hs, rfl⟩
      refine ⟨s, ⟨?_, hs⟩, rfl⟩
      have hh := hmheight s (hZ hs)
      change f (m s) = c - delta at hq
      linarith
    · rintro ⟨s, ⟨ht, hs⟩, rfl⟩
      refine ⟨?_, ⟨s, hs, rfl⟩⟩
      change f (m s) = c - delta
      rw [hmheight s (hZ hs), ht]
      ring
  let aa := Real.sqrt ((rho ^ 2 - delta) / 2)
  let bb := Real.sqrt ((rho ^ 2 + delta) / 2)
  let sg : Fin 2 → ℝ := ![1, -1]
  let sx : Fin 4 → ℝ := ![1, -1, -1, 1]
  let sy : Fin 4 → ℝ := ![1, 1, -1, -1]
  let vv : unitInterval → ℝ := fun t => aa * (1 - 2 * (t : ℝ))
  let lo : Fin 2 → unitInterval → ℝ × ℝ := fun i t =>
    (sg i * vv t, sg i * Real.sqrt ((vv t) ^ 2 + delta))
  let gamma : Fin 2 → unitInterval → UnitTwoSphere := fun i t => m (lo i t)
  let pm : Fin 4 → ℝ × ℝ := fun i => (sx i * aa, sy i * bb)
  let p : Fin 4 → UnitTwoSphere := fun i => m (pm i)
  obtain ⟨hlocal, hldis, hlclosed, hlopen, _, hends⟩ :=
    saddle_hyperbola_disc_arcs rho delta hrho hdelta hdsmall
  have hlo (i : Fin 2) (t : unitInterval) :
      (lo i t).1 ^ 2 - (lo i t).2 ^ 2 = -delta ∧ lo i t ∈ Bc := by
    change lo i t ∈ {s : ℝ × ℝ | s.1 ^ 2 - s.2 ^ 2 = -delta ∧
      s.1 ^ 2 + s.2 ^ 2 ≤ rho ^ 2}
    rw [hlclosed]
    exact mem_iUnion.mpr ⟨i, ⟨t, rfl⟩⟩
  have hgamma (i : Fin 2) : Continuous (gamma i) ∧ Injective (gamma i) := by
    refine ⟨hmcont.comp_continuous (hlocal i).1 (fun t => (hlo i t).2), ?_⟩
    intro s t hst
    exact (hlocal i).2.1 (hminj (hlo i s).2 (hlo i t).2 hst)
  have hgdis : Disjoint (range (gamma 0)) (range (gamma 1)) := by
    apply disjoint_left.mpr
    rintro q ⟨s, rfl⟩ ⟨t, ht⟩
    have heq : lo 1 t = lo 0 s := hminj (hlo 1 t).2 (hlo 0 s).2 ht
    exact disjoint_left.mp hldis ⟨s, rfl⟩ ⟨t, heq⟩
  have hgend (i : Fin 2) :
      gamma i 0 = p (finProdFinEquiv (i, (0 : Fin 2))) ∧
      gamma i 1 = p (finProdFinEquiv (i, (1 : Fin 2))) :=
    ⟨congrArg m (hends i).1, congrArg m (hends i).2.1⟩
  have hnegative : La ∩ Dc = ⋃ i : Fin 2, range (gamma i) := by
    have hh := hcut Bc (Subset.refl Bc)
    rw [← hDc] at hh
    change La ∩ Dc = m '' {s : ℝ × ℝ | s.1 ^ 2 - s.2 ^ 2 = -delta ∧
      s.1 ^ 2 + s.2 ^ 2 ≤ rho ^ 2} at hh
    rw [hlclosed, image_iUnion] at hh
    apply hh.trans
    apply iUnion_congr
    intro i
    change m '' range (lo i) = range (m ∘ lo i)
    exact (Set.range_comp m (lo i)).symm
  have hnegativeOpen : La ∩ V = ⋃ i : Fin 2,
      gamma i '' Ioo (0 : unitInterval) 1 := by
    have hh := hcut Bo hBoBc
    rw [← hV] at hh
    change La ∩ V = m '' {s : ℝ × ℝ | s.1 ^ 2 - s.2 ^ 2 = -delta ∧
      s.1 ^ 2 + s.2 ^ 2 < rho ^ 2} at hh
    rw [hlopen, image_iUnion] at hh
    simpa only [image_image] using hh
  exact ⟨hgamma, hgdis, hgend, hnegative, hnegativeOpen⟩

end PoincareConjecture.M25.Topology3D
