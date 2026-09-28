import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Collars.CircleMarkedScene
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.Tubes.PairedTube
import PoincareConjecture.Proofs.M76.Mathlib.PolyhedralPLDiskExtension









set_option autoImplicit false
open Set Geometry Geometry.SimplicialComplex

namespace PoincareConjecture.M76

open Dehn
local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)
local notation "Idx" => Sum Bool (Fin 3)
local notation "I" => Icc (0 : ℝ) 1

private theorem circle_dualBlock_congr
    (K L : SimplicialComplex ℝ V3) [hK : Fintype K.faces] [hL : Fintype L.faces]
    (h : K = L) (s : Finset V3) : K.barycentricDualBlock s = L.barycentricDualBlock s := by
  subst L
  have hi : hK = hL := Subsingleton.elim _ _
  cases hi
  rfl



theorem exists_coordinate_circle_blocks
    (P : Fin 3 → SimplicialComplex ℝ V3) (hP : ∀ i, (P i).faces.Finite)
    {m : ℕ} (L : Polygon V3 (m + 3)) (hL : L.HasSimplicialEdges)
    (hLi : Function.Injective L) (hPL : (P 2).space = L.boundary ℝ)
    {W : Set V3} (hW : IsOpen W) (hLW : L.boundary ℝ ⊆ W)
    (hisolate : ∀ x ∈ W, x ∈ L.boundary ℝ ↔ x ∈ (P 0).space ∧ x ∈ (P 1).space)
    (hcharts : ∀ x ∈ L.boundary ℝ, ∃ B : OpenPartialHomeomorph V3 V3,
      x ∈ B.source ∧ B ∈ piecewiseAffineGroupoid V3 ∧
      ∀ (i : Fin 2) y, y ∈ B.source → (y ∈ (P i.castSucc).space ↔ B y i.castSucc = 0)) :
    ∃ (N : SimplicialComplex ℝ V3) (M : Idx → SimplicialComplex ℝ V3)
      (n : ℕ) (p : Fin (n + 3) → V3) (hN : N.faces.Finite),
      L.boundary ℝ ⊆ interior N.space ∧ N.space ⊆ W ∧
      (∀ i, M i ≤ N ∧ (M i).faces.Finite ∧
        ∀ f ∈ N.faces, (∀ v ∈ f, v ∈ (M i).vertices) → f ∈ (M i).faces) ∧
      M (.inl false) = N ∧ (M (.inl true)).space = ∅ ∧
      (M (.inr 2)).space = L.boundary ℝ ∧
      (∀ i : Fin 2, (M (.inr i.castSucc)).space = N.space ∩ (P i.castSucc).space) ∧
      Function.Injective p ∧ range p = (M (.inr 2)).vertices ∧
      (∀ s : Finset V3, s ∈ (M (.inr 2)).faces ↔ s.Nonempty ∧
        ∃ j : Fin (n + 3), s ⊆ {p j, p (finRotate (n + 3) j)}) ∧
      letI : Fintype N.faces := hN.fintype
      ∃ (joint : ∀ j : Fin (n + 3), signedTubeDiamond ≃ₜ
          (N.barycentricDualBlock {p j, p (finRotate (n + 3) j)}).space)
        (left right : Fin (n + 3) → Fin 2 → Bool)
        (map : ∀ j : Fin (n + 3), ↥(signedTubeDiamond ×ˢ I) ≃ₜ
          (N.barycentricDualBlock {p j}).space),
        (∀ j, (joint j).IsFinitePL) ∧ (∀ j, (map j).IsFinitePL) ∧
        (∀ j (x : signedTubeDiamond),
          (map j ⟨(x, 0), x.property, le_rfl, zero_le_one⟩ : V3) =
            joint ((finRotate (n + 3)).symm j) (signedTubeDiamondReflection (left j) x)) ∧
        (∀ j (x : signedTubeDiamond),
          (map j ⟨(x, 1), x.property, zero_le_one, le_rfl⟩ : V3) =
            joint j (signedTubeDiamondReflection (right j) x)) ∧
        (∀ j k (x : ↥(signedTubeDiamond ×ˢ I)),
          (x : P2 × ℝ).1 ∈ signedTubeSheet k ↔
            (map j x : V3) ∈ (M (.inr k.castSucc)).space) ∧
        ∀ j (x : ↥(signedTubeDiamond ×ˢ I)),
          (x : P2 × ℝ).1 = (0, 0) ↔ (map j x : V3) ∈ (M (.inr 2)).space := by
  classical
  obtain ⟨N, M, n, p, hN, hLN, hNW, hM, hregEq, hfrEq, harcEq, hsheetEq,
    hpi, hpv, hpf, B, hBW, hB₀⟩ := exists_circle_marked_scene P hP L hL hLi hPL
      hW hLW hisolate hcharts
  let : Fintype N.faces := hN.fintype
  let : ∀ i, Fintype (M i).faces := fun i => (hM i).2.1.fintype
  have hpN : p 0 ∈ N.space := space_subset_of_le (hM (.inr 2)).1
    ((M (.inr 2)).vertices_subset_space (hpv ▸ mem_range_self 0))
  let g : V3 → N.space := fun x => if hx : x ∈ N.space then ⟨x, hx⟩ else ⟨p 0, hpN⟩
  have hg (x : V3) (hx : x ∈ N.space) : (g x : V3) = x := by simp only [g, dif_pos hx]
  let e := fun _ : Unit => OpenPartialHomeomorph.refl V3
  have hgPL : PolyhedralPLInCharts e (fun x => (g x : V3)) N.space :=
    (circle_coordinate_identity_pl N hN).congr (fun x hx => (hg x hx).symm)
  have hreg (x : V3) (hx : x ∈ N.space) :
      x ∈ (M (.inl false)).space ↔ (g x : V3) ∈ (univ : Set V3) := by
    rw [hregEq]
    exact iff_of_true hx (mem_univ _)
  have hfr (x : V3) (_hx : x ∈ N.space) :
      x ∈ (M (.inl true)).space ↔ (g x : V3) ∈ frontier (univ : Set V3) := by
    simp only [hfrEq, frontier_univ, mem_empty_iff_false]
  have harc (x : V3) (hx : x ∈ N.space) :
      x ∈ (M (.inr 2)).space ↔ (g x : V3) ∈ L.boundary ℝ := by rw [harcEq, hg x hx]
  have hsheet (i : Fin 2) (x : V3) (hx : x ∈ N.space) :
      x ∈ (M (.inr i.castSucc)).space ↔ (g x : V3) ∈ (P i.castSucc).space := by
    rw [hsheetEq, hg x hx]
    exact and_iff_right hx
  have hB (v : (M (.inr 2)).vertices) :
      MapsTo (fun x => (g x : V3)) (N.closedStar v).space (B v).source ∧
      (N.closedStar v).AffineOnFaces (fun x => B v (g x)) ∧
      (∀ y ∈ (B v).source, y ∈ L.boundary ℝ ↔ y ∈ (univ : Set V3) ∧ B v y 0 = 0 ∧ B v y 1 = 0) ∧
      ∀ (i : Fin 2) y, y ∈ (B v).source →
        (y ∈ (P i.castSucc).space ↔ y ∈ (univ : Set V3) ∧ B v y i.castSucc = 0) := by
    have hstar : (N.closedStar v).space ⊆ N.space := space_subset_of_le (fun _ hs => hs.1)
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro x hx
      change (g x : V3) ∈ (B v).source
      rw [hg x (hstar hx)]
      exact (hB₀ v).1 hx
    · exact (hB₀ v).2.1.congr (fun x hx => congrArg (B v) (hg x (hstar hx)).symm)
    · intro y hy
      simpa only [mem_univ, true_and] using (hB₀ v).2.2.1 y hy
    · intro i y hy
      simpa only [mem_univ, true_and] using (hB₀ v).2.2.2 i y hy
  have hAR : L.boundary ℝ ⊆ (univ : Set V3) := subset_univ _
  have hAF : (L.boundary ℝ ∩ frontier (univ : Set V3)).Finite := by simp
  obtain ⟨G, eta, hG, hcenter, hquarter⟩ := exists_original_signed_tube_joint_family
    hLN hAR hAF (fun i : Fin 2 => (P i.castSucc).space) N id continuous_id
    (Homeomorph.refl N.space) (fun _ => rfl) g (fun z => hg z z.property) hgPL M
    (fun i => (hM i).1) (fun i => (hM i).2.2) (.inl false) (.inl true) (.inr 2)
    (fun i : Fin 2 => .inr i.castSucc) hreg hfr harc hsheet B (by
      convert hB using 1
      have hdec : (fun a b : V3 => Fintype.decidablePiFintype a b) =
          Classical.decEq _ := Subsingleton.elim _ _
      rw [hdec])
  have hnext (j : Fin (n + 3)) : j ≠ finRotate (n + 3) j := by
    intro h
    have h' : (1 : Fin (n + 3)) = 0 := add_left_cancel
      (show j + 1 = j + 0 by simpa only [finRotate_apply, add_zero] using h.symm)
    have := congrArg Fin.val h'
    norm_num at this
  let vertex (j : Fin (n + 3)) : (M (.inr 2)).vertices := ⟨p j, hpv ▸ mem_range_self j⟩
  let Edge := {s : Finset V3 // s ∈ (M (.inr 2)).faces ∧ s.card = 2}
  let edge (j : Fin (n + 3)) : Edge := ⟨{p j, p (finRotate (n + 3) j)},
    (hpf _).mpr ⟨Finset.insert_nonempty _ _, j, subset_rfl⟩,
    Finset.card_pair (hpi.ne (hnext j))⟩
  have hjointDisj := (N.full_cyclic_dual_contacts (M (.inr 2))
    (hM (.inr 2)).1 (hM (.inr 2)).2.2 p hpi hpv hpf).2.2.2.1
  let incident (j : Fin (n + 3)) (side : Bool) := if side then j else (finRotate (n + 3)).symm j
  have hincident (j : Fin (n + 3)) (side : Bool) : (vertex j : V3) ∈
      (edge (incident j side) : Finset V3) := by
    cases side <;> simp [vertex, edge, incident]
  let sign (j : Fin (n + 3)) (side : Bool) := eta (edge (incident j side)) (vertex j) (hincident j side)
  have hblock (j : Fin (n + 3)) :
      ∃ map : ↥(signedTubeDiamond ×ˢ I) ≃ₜ (N.barycentricDualBlock {p j}).space,
        map.IsFinitePL ∧
        (∀ side (x : signedTubeDiamond),
          (map ⟨(x, if side then 1 else 0), x.property, by cases side <;> norm_num⟩ : V3) =
            G (edge (incident j side)) (signedTubeDiamondReflection (sign j side) x)) ∧
        (∀ k (x : ↥(signedTubeDiamond ×ˢ I)), (x : P2 × ℝ).1 ∈ signedTubeSheet k ↔
          (map x : V3) ∈ (M (.inr k.castSucc)).space) ∧
        ∀ x : ↥(signedTubeDiamond ×ˢ I), (x : P2 × ℝ).1 = (0, 0) ↔
          (map x : V3) ∈ (M (.inr 2)).space := by
    have hne : (finRotate (n + 3)).symm j ≠ j := by
      intro h
      exact hnext j (by simpa only [Equiv.apply_symm_apply] using congrArg (finRotate (n + 3)) h)
    have hdisj := hjointDisj ((finRotate (n + 3)).symm j) j hne
    let s := fun side : Bool => (edge (incident j side) : Finset V3)
    let Gj := fun side : Bool => G (edge (incident j side))
    obtain ⟨b, map, hb, hb0, hb1, hm, hend, haxis, hquarter', haxis', hsheets⟩ :=
      exists_original_local_interior_block_map hLN hAR hAF
        (fun i : Fin 2 => (P i.castSucc).space) N id continuous_id
        (Homeomorph.refl N.space) (fun _ => rfl) g (fun z => hg z z.property) hgPL M
        (fun i => (hM i).1) (fun i => (hM i).2.2) (.inl false) (.inl true) (.inr 2)
        (fun i : Fin 2 => .inr i.castSucc) hreg hfr harc hsheet B (by
          convert hB using 1
          have hdec : (fun a b : V3 => Fintype.decidablePiFintype a b) =
              Classical.decEq _ := Subsingleton.elim _ _
          rw [hdec])
        (vertex j) (by simp) (Or.inl (by simp)) s
        (fun side => (edge (incident j side)).property.1)
        (fun side => (edge (incident j side)).property.2) (hincident j)
        (by simpa only [s, edge, incident, Bool.false_eq_true, ↓reduceIte] using hdisj)
        Gj (fun side => hG (edge (incident j side))) (sign j)
        (fun side => hquarter (edge (incident j side)) (vertex j) (hincident j side))
        (fun side => hcenter (edge (incident j side)))
    have hcarrier := congrArg SimplicialComplex.space
      (circle_dualBlock_congr _ _ hregEq {(vertex j : V3)})
    let map' := map.trans (Homeomorph.setCongr hcarrier)
    refine ⟨map', hm.setCongr rfl hcarrier, hend, hsheets, ?_⟩
    intro x
    exact (haxis' x).trans (and_iff_right (hcarrier ▸ (map x).property))
  choose map hmap hend hsheet' haxis using hblock
  exact ⟨N, M, n, p, hN, hLN, hNW, hM, hregEq, hfrEq, harcEq, hsheetEq,
    hpi, hpv, hpf, (fun j => G (edge j)), (fun j => sign j false),
    (fun j => sign j true), map, (fun j => hG (edge j)), hmap,
    (fun j x => hend j false x), (fun j x => hend j true x), hsheet', haxis⟩

end PoincareConjecture.M76
