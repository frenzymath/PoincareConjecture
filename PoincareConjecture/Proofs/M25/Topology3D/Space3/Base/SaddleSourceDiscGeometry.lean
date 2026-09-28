import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.HyperbolaDiscArcs

set_option autoImplicit false

open Set Function
open scoped ContDiff Manifold InnerProductSpace Matrix

namespace PoincareConjecture.M25.Topology3D

theorem saddle_source_disc_arc_geometry
    (psi : UnitTwoSphere × ℝ → E3) (u : UnitTwoSphere)
    (D : SaddlePieceData psi u) (R delta : ℝ)
    (N : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ)) (hR : 0 < R) (hd : 0 < delta)
    (hdR : delta ≤ (5 * R / 8) ^ 2 / 128)
    (hmorse : {s : ℝ × ℝ | s.1 ^ 2 + s.2 ^ 2 < (2 * R) ^ 2} ⊆ D.morse.target)
    (hN : ∀ s : ℝ × ℝ, N (N s) = s ∧
      (N s).1 ^ 2 + (N s).2 ^ 2 = s.1 ^ 2 + s.2 ^ 2 ∧
      D.morseSign1 * (N s).1 ^ 2 + D.morseSign2 * (N s).2 ^ 2 =
        s.1 ^ 2 - s.2 ^ 2) :
    let f : UnitTwoSphere → ℝ := fun p => ⟪(u : E3), psi (p, 0)⟫_ℝ
    let c := f D.point
    let r := 5 * R / 8
    let Dc := D.morse.symm '' {s : ℝ × ℝ | s.1 ^ 2 + s.2 ^ 2 ≤ r ^ 2}
    let Do := D.morse.symm '' {s : ℝ × ℝ | s.1 ^ 2 + s.2 ^ 2 < r ^ 2}
    let aa := Real.sqrt ((r ^ 2 - delta) / 2)
    let bb := Real.sqrt ((r ^ 2 + delta) / 2)
    let sx : Fin 4 → ℝ := ![1, -1, -1, 1]
    let sy : Fin 4 → ℝ := ![1, 1, -1, -1]
    let pm : Fin 4 → UnitTwoSphere := fun i => D.morse.symm (N (sx i * aa, sy i * bb))
    let pp : Fin 4 → UnitTwoSphere := fun i => D.morse.symm (N (sx i * bb, sy i * aa))
    let ep : Fin 2 × Fin 2 ≃ Fin 4 := finProdFinEquiv
    let other : Fin 2 → Fin 2 := ![1, 0]
    ∃ gm gp : Fin 2 → unitInterval → UnitTwoSphere,
      (∀ i, Continuous (gm i) ∧ Injective (gm i) ∧
        Continuous (gp i) ∧ Injective (gp i)) ∧
      Disjoint (range (gm 0)) (range (gm 1)) ∧
      Disjoint (range (gp 0)) (range (gp 1)) ∧
      (∀ i, gm i 0 = pm (ep (i, 0)) ∧ gm i 1 = pm (ep (i, 1)) ∧
        gp i 0 = pp (ep (i, 0)) ∧ gp i 1 = pp (ep (other i, 1))) ∧
      {p | f p = c - delta} ∩ Dc = ⋃ i, range (gm i) ∧
      {p | f p = c - delta} ∩ Do = ⋃ i, gm i '' Ioo (0 : unitInterval) 1 ∧
      {p | f p = c + delta} ∩ Dc = ⋃ i, range (gp i) := by
  classical
  let f : UnitTwoSphere → ℝ := fun p => ⟪(u : E3), psi (p, 0)⟫_ℝ
  let c := f D.point
  let r := 5 * R / 8
  let r2 : ℝ × ℝ → ℝ := fun s => s.1 ^ 2 + s.2 ^ 2
  let Bc : Set (ℝ × ℝ) := {s | r2 s ≤ r ^ 2}
  let Bo : Set (ℝ × ℝ) := {s | r2 s < r ^ 2}
  let m : ℝ × ℝ → UnitTwoSphere := fun s => D.morse.symm (N s)
  let Dc : Set UnitTwoSphere := D.morse.symm '' Bc
  let Do : Set UnitTwoSphere := D.morse.symm '' Bo
  have hNr2 (s : ℝ × ℝ) : r2 (N s) = r2 s := (hN s).2.1
  have hr : 0 < r := by dsimp [r]; positivity
  have hdsmall : delta < r ^ 2 := by
    change delta ≤ r ^ 2 / 128 at hdR
    nlinarith [sq_pos_of_pos hr]
  have hBoBc : Bo ⊆ Bc := fun s hs => (show r2 s < r ^ 2 from hs).le
  have hNs (s : ℝ × ℝ) (hs : s ∈ Bc) : N s ∈ D.morse.target := by
    apply hmorse
    change r2 (N s) < (2 * R) ^ 2
    rw [hNr2 s]
    change r2 s ≤ r ^ 2 at hs
    dsimp [r] at hs
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
    rw [D.morse.right_inv (hNs s hs)] at hh
    linarith only [hh, (hN s).2.2]
  have hnormalize (Z : Set (ℝ × ℝ)) (hZ : ∀ s, s ∈ Z ↔ N s ∈ Z) :
      D.morse.symm '' Z = m '' Z := by
    ext p
    constructor
    · rintro ⟨s, hs, rfl⟩
      refine ⟨N s, (hZ s).mp hs, ?_⟩
      change D.morse.symm (N (N s)) = D.morse.symm s
      rw [(hN s).1]
    · rintro ⟨s, hs, rfl⟩
      exact ⟨N s, (hZ s).mp hs, rfl⟩
  have hDc : Dc = m '' Bc := hnormalize Bc (fun s => by
    change r2 s ≤ r ^ 2 ↔ r2 (N s) ≤ r ^ 2; rw [hNr2 s])
  have hDo : Do = m '' Bo := hnormalize Bo (fun s => by
    change r2 s < r ^ 2 ↔ r2 (N s) < r ^ 2; rw [hNr2 s])
  have hcut (z : ℝ) (Z : Set (ℝ × ℝ)) (hZ : Z ⊆ Bc) :
      {p | f p = c + z} ∩ m '' Z =
        m '' {s : ℝ × ℝ | s.1 ^ 2 - s.2 ^ 2 = z ∧ s ∈ Z} := by
    ext p
    constructor
    · rintro ⟨hp, s, hs, rfl⟩
      refine ⟨s, ⟨?_, hs⟩, rfl⟩
      have hh := hmheight s (hZ hs)
      change f (m s) = c + z at hp
      linarith
    · rintro ⟨s, ⟨ht, hs⟩, rfl⟩
      refine ⟨?_, ⟨s, hs, rfl⟩⟩
      change f (m s) = c + z
      rw [hmheight s (hZ hs), ht]
  let aa := Real.sqrt ((r ^ 2 - delta) / 2)
  let sg : Fin 2 → ℝ := ![1, -1]
  let vv : unitInterval → ℝ := fun t => aa * (1 - 2 * (t : ℝ))
  let lo : Fin 2 → unitInterval → ℝ × ℝ := fun i t =>
    (sg i * vv t, sg i * Real.sqrt ((vv t) ^ 2 + delta))
  let hi : Fin 2 → unitInterval → ℝ × ℝ := fun i t =>
    (sg i * Real.sqrt ((vv t) ^ 2 + delta), sg i * vv t)
  obtain ⟨hlocal, hldis, hlclosed, hlopen, huclosed, hends⟩ :=
    saddle_hyperbola_disc_arcs r delta hr hd hdsmall
  have hlo (i : Fin 2) (t : unitInterval) : lo i t ∈ Bc := by
    have hh : lo i t ∈ {s : ℝ × ℝ | s.1 ^ 2 - s.2 ^ 2 = -delta ∧
        s.1 ^ 2 + s.2 ^ 2 ≤ r ^ 2} := by
      rw [hlclosed]
      exact mem_iUnion.mpr ⟨i, ⟨t, rfl⟩⟩
    exact hh.2
  have hhi (i : Fin 2) (t : unitInterval) : hi i t ∈ Bc := by
    have hh : hi i t ∈ {s : ℝ × ℝ | s.1 ^ 2 - s.2 ^ 2 = delta ∧
        s.1 ^ 2 + s.2 ^ 2 ≤ r ^ 2} := by
      rw [huclosed]
      exact mem_iUnion.mpr ⟨i, ⟨t, rfl⟩⟩
    exact hh.2
  have hudis : Disjoint (range (hi 0)) (range (hi 1)) := by
    apply disjoint_left.mpr
    rintro x ⟨s, rfl⟩ ⟨t, ht⟩
    have hh : lo 1 t = lo 0 s := congrArg Prod.swap ht
    exact disjoint_left.mp hldis ⟨s, rfl⟩ ⟨t, hh⟩
  let gm : Fin 2 → unitInterval → UnitTwoSphere := fun i t => m (lo i t)
  let gp : Fin 2 → unitInterval → UnitTwoSphere := fun i t => m (hi i t)
  refine ⟨gm, gp, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    refine ⟨hmcont.comp_continuous (hlocal i).1 (hlo i), ?_,
      hmcont.comp_continuous (hlocal i).2.2.1 (hhi i), ?_⟩
    · intro s t hst
      exact (hlocal i).2.1 (hminj (hlo i s) (hlo i t) hst)
    · intro s t hst
      exact (hlocal i).2.2.2 (hminj (hhi i s) (hhi i t) hst)
  · apply disjoint_left.mpr
    rintro x ⟨s, rfl⟩ ⟨t, ht⟩
    exact disjoint_left.mp hldis ⟨s, rfl⟩ ⟨t, hminj (hlo 1 t) (hlo 0 s) ht⟩
  · apply disjoint_left.mpr
    rintro x ⟨s, rfl⟩ ⟨t, ht⟩
    exact disjoint_left.mp hudis ⟨s, rfl⟩ ⟨t, hminj (hhi 1 t) (hhi 0 s) ht⟩
  · intro i
    exact ⟨congrArg m (hends i).1, congrArg m (hends i).2.1,
      congrArg m (hends i).2.2.1, congrArg m (hends i).2.2.2⟩
  · have hh := hcut (-delta) Bc (Subset.refl Bc)
    rw [← hDc] at hh
    change {p | f p = c + -delta} ∩ Dc = m ''
      {s : ℝ × ℝ | s.1 ^ 2 - s.2 ^ 2 = -delta ∧
        s.1 ^ 2 + s.2 ^ 2 ≤ r ^ 2} at hh
    rw [hlclosed, image_iUnion] at hh
    simp only [← sub_eq_add_neg] at hh
    exact hh.trans (iUnion_congr (fun i => (Set.range_comp m (lo i)).symm))
  · have hh := hcut (-delta) Bo hBoBc
    rw [← hDo] at hh
    change {p | f p = c + -delta} ∩ Do = m ''
      {s : ℝ × ℝ | s.1 ^ 2 - s.2 ^ 2 = -delta ∧
        s.1 ^ 2 + s.2 ^ 2 < r ^ 2} at hh
    rw [hlopen, image_iUnion] at hh
    simpa only [← sub_eq_add_neg, image_image] using hh
  · have hh := hcut delta Bc (Subset.refl Bc)
    rw [← hDc] at hh
    change {p | f p = c + delta} ∩ Dc = m ''
      {s : ℝ × ℝ | s.1 ^ 2 - s.2 ^ 2 = delta ∧
        s.1 ^ 2 + s.2 ^ 2 ≤ r ^ 2} at hh
    rw [huclosed, image_iUnion] at hh
    exact hh.trans (iUnion_congr (fun i => (Set.range_comp m (hi i)).symm))

end PoincareConjecture.M25.Topology3D
