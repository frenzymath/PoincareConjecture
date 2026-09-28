import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Boundary.Circles.OrientedJoints
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Boundary.Circles.OrientedVertexStrip
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.Tubes.ModelDualContacts

set_option autoImplicit false
open Set Geometry Geometry.SimplicialComplex AbstractSimplicialComplex

namespace PoincareConjecture.M76.Dehn

local notation "P2" => (ℝ × ℝ)


structure BoundaryCircleBlockData
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [DecidableEq E] (A L : SimplicialComplex ℝ E) [Fintype A.faces]
    {n : ℕ} (p : Fin (n + 3) → E) where
  joint : ∀ j, signedTubeSheet 0 ≃ₜ
    (A.barycentricDualBlock {p j, p (finRotate (n + 3) j)}).space
  jointPL : ∀ j, (joint j).IsFinitePL
  map : ∀ j, ↥(signedTubeSheet 0 ×ˢ Icc (0 : ℝ) 1) ≃ₜ
    (A.barycentricDualBlock {p j}).space
  mapPL : ∀ j, (map j).IsFinitePL
  lower : ∀ j (x : signedTubeSheet 0),
    (map j ⟨(x, 0), x.property, le_rfl, zero_le_one⟩ : E) =
      joint ((finRotate (n + 3)).symm j) x
  upper : ∀ j (x : signedTubeSheet 0),
    (map j ⟨(x, 1), x.property, zero_le_one, le_rfl⟩ : E) = joint j x
  axis : ∀ j (x : ↥(signedTubeSheet 0 ×ˢ Icc (0 : ℝ) 1)),
    (map j x : E) ∈ L.space ↔ x.val.1 = (0, 0)



theorem exists_boundary_circle_blocks
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [DecidableEq E] (A L : SimplicialComplex ℝ E) [Fintype A.faces] [Fintype L.faces]
    (hLA : L ≤ A)
    (hpure : ∀ s ∈ A.faces, ∃ t ∈ A.faces, t.card = 3 ∧ s ⊆ t)
    (hcofaces : ∀ s ∈ A.faces, s.card = 2 →
      {t : Finset E | t ∈ A.faces ∧ t.card = 3 ∧ s ⊆ t}.ncard = 2)
    (hfull : ∀ t ∈ A.faces, (∀ v ∈ t, v ∈ L.vertices) → t ∈ L.faces)
    (hLcard : ∀ s ∈ L.faces, s.card ≤ 2)
    (hlinks : ∀ v ∈ L.vertices, IsConnected (A.link v).space)
    (number : E → ℕ) (sign : Finset E → ZMod 2) (hnumber : InjOn number A.vertices)
    (hcancel : ∀ t ∈ A.faces, t.card = 3 → ∀ u ∈ A.faces, u.card = 3 → t ≠ u →
      ∀ s : Finset E, s.card = 2 → s ⊆ t → s ⊆ u →
        (sign t + boundaryFaceParity number t s) +
          (sign u + boundaryFaceParity number u s) = 1)
    {n : ℕ} (p : Fin (n + 3) → E) (hpi : Function.Injective p)
    (hpv : range p = L.vertices)
    (hpf : ∀ s : Finset E, s ∈ L.faces ↔ s.Nonempty ∧
      ∃ j : Fin (n + 3), s ⊆ {p j, p (finRotate (n + 3) j)}) :
    Nonempty (BoundaryCircleBlockData A L p) := by
  classical
  let next := finRotate (n + 3)
  let edge := fun j => ({p j, p (next j)} : Finset E)
  have hnext (j : Fin (n + 3)) : j ≠ next j := by
    intro h
    have hh : (1 : Fin (n + 3)) = 0 := add_left_cancel
      (show j + 1 = j + 0 by simpa only [next, finRotate_apply, add_zero] using h.symm)
    have := congrArg Fin.val hh
    norm_num at this
  have hprevnext (j : Fin (n + 3)) : next.symm j ≠ next j := by
    intro h
    have hh : j = next (next j) := by rw [← h]; exact (next.apply_symm_apply j).symm
    have h11 : (1 : Fin (n + 3)) + 1 = 2 := by
      apply Fin.ext
      norm_num [Fin.val_add]
    have he : (0 : Fin (n + 3)) = 2 := add_left_cancel
      (show j + 0 = j + 2 by simpa only [next, finRotate_apply, add_zero, add_assoc,
        h11] using hh)
    have := congrArg Fin.val he
    norm_num [Nat.mod_eq_of_lt (show 2 < n + 3 by omega)] at this
  have he (j : Fin (n + 3)) : edge j ∈ L.faces :=
    (hpf _).mpr ⟨Finset.insert_nonempty _ _, j, subset_rfl⟩
  have hbound (s : Finset E) (hs : s ∈ A.faces) : s.card ≤ 3 := by
    obtain ⟨t, _, htc, hst⟩ := hpure s hs
    exact (Finset.card_le_card hst).trans_eq htc
  have hJoint (j : Fin (n + 3)) := exists_oriented_boundary_joint A hbound hcofaces
    number sign hcancel (hpi.ne (hnext j)) (hLA (he j))
  choose t G r ht htn htex htsign hG hr hGr hGmem hrm hrc hGm using hJoint
  let incident := fun (j : Fin (n + 3)) (b : Bool) => if b then j else next.symm j
  let neighbor := fun (j : Fin (n + 3)) (b : Bool) => if b then p (next j) else p (next.symm j)
  have hedgeEq (j : Fin (n + 3)) (b : Bool) : edge (incident j b) = {p j, neighbor j b} := by
    cases b
    · simp [edge, incident, neighbor, Finset.pair_comm]
    · rfl
  have hblock (j : Fin (n + 3)) :
      ∃ H : ↥(signedTubeSheet 0 ×ˢ Icc (0 : ℝ) 1) ≃ₜ (A.barycentricDualBlock {p j}).space,
        H.IsFinitePL ∧
        (∀ b (x : signedTubeSheet 0),
          (H ⟨(x, if b then 1 else 0), x.property, by cases b <;> simp⟩ : E) =
            G (incident j b) x) ∧
        ∀ x : ↥(signedTubeSheet 0 ×ˢ Icc (0 : ℝ) 1),
          (H x : E) ∈ L.space ↔ x.val.1 = (0, 0) := by
    have hvp (b : Bool) : p j ≠ neighbor j b := by
      cases b
      · apply hpi.ne
        intro h
        exact hnext j (by simpa only [Equiv.apply_symm_apply] using (congrArg next h).symm)
      · exact hpi.ne (hnext j)
    have hpne : neighbor j false ≠ neighbor j true := hpi.ne (hprevnext j)
    have hedge (b : Bool) : ({p j, neighbor j b} : Finset E) ∈ L.faces := hedgeEq j b ▸ he _
    have hexhaust (s : Finset E) (hs : s ∈ L.faces) (hps : p j ∈ s) (hsc : s.card = 2) :
        s = {p j, neighbor j false} ∨ s = {p j, neighbor j true} := by
      obtain ⟨k, hsk⟩ := ((hpf s).mp hs).2
      have heq : s = edge k := Finset.eq_of_subset_of_card_le hsk
        (by rw [Finset.card_pair (hpi.ne (hnext k)), hsc])
      have hpj : p j ∈ edge k := heq ▸ hps
      simp only [edge, Finset.mem_insert, Finset.mem_singleton, hpi.eq_iff] at hpj
      rcases hpj with rfl | hj
      · exact Or.inr heq
      · have hk : k = next.symm j := (next.eq_symm_apply).mpr hj.symm
        exact Or.inl (heq.trans (hk ▸ hedgeEq j false))
    let tj := fun b side => t (incident j b) side
    let Gj := fun b => (G (incident j b)).trans (Homeomorph.setCongr
      (congrArg (fun s => (A.barycentricDualBlock s).space) (hedgeEq j b)))
    let rj := fun b side => (r (incident j b) side).trans (Homeomorph.setCongr
      (congrArg (fun s : Finset E => segment ℝ (s.centroid ℝ id) ((tj b side).centroid ℝ id))
        (hedgeEq j b)))
    have htj (b side : Bool) : tj b side ∈ A.faces ∧ (tj b side).card = 3 ∧
        ({p j, neighbor j b} : Finset E) ⊆ tj b side := by
      simpa only [← hedgeEq j b] using ht (incident j b) side
    have htexj (b : Bool) (u : Finset E) (hu : u ∈ A.faces) (huc : u.card = 3)
        (hsu : ({p j, neighbor j b} : Finset E) ⊆ u) : u = tj b false ∨ u = tj b true := by
      apply htex (incident j b) u hu huc
      change edge (incident j b) ⊆ u
      rw [hedgeEq]
      exact hsu
    have htsignj (b side : Bool) : sign (tj b side) + orderedCofaceParity number (tj b side)
        (if b then p j else neighbor j false) (if b then neighbor j true else p j) =
          if side then 1 else 0 := by
      cases b
      · simpa only [tj, incident, neighbor, Bool.false_eq_true, ↓reduceIte,
          Equiv.apply_symm_apply] using htsign (next.symm j) side
      · exact htsign j side
    have hrj (b side : Bool) : (rj b side).IsFinitePL :=
      (hr (incident j b) side).setCongr rfl _
    have hGrj (b side : Bool) (x : signedTubeRadius 0 side) :
        (Gj b ⟨x, by cases side; exact Or.inl x.property; exact Or.inr x.property⟩ : E) = rj b side x :=
      hGr (incident j b) side x
    have hrmj (b side : Bool) : (rj b side ⟨(0, 0), left_mem_segment ℝ _ _⟩ : E) =
        ({p j, neighbor j b} : Finset E).centroid ℝ id := by
      exact ((hrm (incident j b) side _).mpr rfl).trans (congrArg (fun s => s.centroid ℝ id) (hedgeEq j b))
    have hrcj (b side : Bool) :
        (rj b side ⟨signedTubeCorner 0 side, right_mem_segment ℝ _ _⟩ : E) = (tj b side).centroid ℝ id :=
      (hrc (incident j b) side _).mpr rfl
    exact exists_oriented_boundary_vertex_strip A L hLA hpure hcofaces hfull hLcard
      number sign hnumber hcancel (p j) (neighbor j) hvp hpne hedge
      (hlinks (p j) (hpv ▸ mem_range_self j)) hexhaust tj htj htexj htsignj
      Gj rj hrj hGrj hrmj hrcj
  choose H hH hHE hHA using hblock
  exact ⟨{ joint := G
           jointPL := hG
           map := H
           mapPL := hH
           lower := fun j x => hHE j false x
           upper := fun j x => hHE j true x
           axis := hHA }⟩

end PoincareConjecture.M76.Dehn
