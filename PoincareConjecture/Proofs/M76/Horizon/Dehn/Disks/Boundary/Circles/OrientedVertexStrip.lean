import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Boundary.Circles.OrientedVertexCut
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Boundary.Circles.LocalStripMaps

set_option autoImplicit false
open Set Geometry Geometry.SimplicialComplex AbstractSimplicialComplex

namespace PoincareConjecture.M76.Dehn

local notation "P2" => (ℝ × ℝ)



theorem exists_oriented_boundary_vertex_strip
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [DecidableEq E] (A L : SimplicialComplex ℝ E) [Fintype A.faces] [Fintype L.faces]
    (hLA : L ≤ A)
    (hpure : ∀ s ∈ A.faces, ∃ t ∈ A.faces, t.card = 3 ∧ s ⊆ t)
    (hcofaces : ∀ s ∈ A.faces, s.card = 2 →
      {t : Finset E | t ∈ A.faces ∧ t.card = 3 ∧ s ⊆ t}.ncard = 2)
    (hfull : ∀ t ∈ A.faces, (∀ v ∈ t, v ∈ L.vertices) → t ∈ L.faces)
    (hLcard : ∀ s ∈ L.faces, s.card ≤ 2)
    (number : E → ℕ) (sign : Finset E → ZMod 2) (hnumber : InjOn number A.vertices)
    (hcancel : ∀ t ∈ A.faces, t.card = 3 → ∀ u ∈ A.faces, u.card = 3 → t ≠ u →
      ∀ s : Finset E, s.card = 2 → s ⊆ t → s ⊆ u →
        (sign t + boundaryFaceParity number t s) +
          (sign u + boundaryFaceParity number u s) = 1)
    (v : E) (p : Bool → E) (hvp : ∀ j, v ≠ p j) (hpne : p false ≠ p true)
    (hedge : ∀ j, ({v, p j} : Finset E) ∈ L.faces)
    (hlink : IsConnected (A.link v).space)
    (hexhaust : ∀ s ∈ L.faces, v ∈ s → s.card = 2 →
      s = {v, p false} ∨ s = {v, p true})
    (t : Bool → Bool → Finset E)
    (ht : ∀ j b, t j b ∈ A.faces ∧ (t j b).card = 3 ∧ ({v, p j} : Finset E) ⊆ t j b)
    (htex : ∀ j u, u ∈ A.faces → u.card = 3 → ({v, p j} : Finset E) ⊆ u →
      u = t j false ∨ u = t j true)
    (htsign : ∀ j b, sign (t j b) + orderedCofaceParity number (t j b)
      (if j then v else p false) (if j then p true else v) = if b then 1 else 0)
    (J : ∀ j, signedTubeSheet 0 ≃ₜ (A.barycentricDualBlock {v, p j}).space)
    (r : ∀ j b, signedTubeRadius 0 b ≃ₜ
      segment ℝ (({v, p j} : Finset E).centroid ℝ id) ((t j b).centroid ℝ id))
    (hr : ∀ j b, (r j b).IsFinitePL)
    (hJr : ∀ j b (x : signedTubeRadius 0 b),
      (J j ⟨x, by cases b; exact Or.inl x.property; exact Or.inr x.property⟩ : E) = r j b x)
    (hrm : ∀ j b, (r j b ⟨(0, 0), left_mem_segment ℝ _ _⟩ : E) =
      ({v, p j} : Finset E).centroid ℝ id)
    (hrc : ∀ j b, (r j b ⟨signedTubeCorner 0 b, right_mem_segment ℝ _ _⟩ : E) =
      (t j b).centroid ℝ id) :
    ∃ H : ↥(signedTubeSheet 0 ×ˢ Icc (0 : ℝ) 1) ≃ₜ (A.barycentricDualBlock {v}).space,
      H.IsFinitePL ∧
      (∀ j (x : signedTubeSheet 0),
        (H ⟨(x, if j then 1 else 0), x.property, by cases j <;> simp⟩ : E) = J j x) ∧
      ∀ x : ↥(signedTubeSheet 0 ×ˢ Icc (0 : ℝ) 1),
        (H x : E) ∈ L.space ↔ x.val.1 = (0, 0) := by
  classical
  let s := fun j => ({v, p j} : Finset E)
  let V := (A.barycentricDualBlock {v}).space
  let Z := V ∩ L.space
  let m := fun j => (s j).centroid ℝ id
  let c := fun j b => (t j b).centroid ℝ id
  let D := fun j b => segment ℝ (m j) (c j b)
  obtain ⟨hm, hZ, U, F, hU, hF, hZU, _, _, hFU, hFI, hDU⟩ :=
    exists_oriented_boundary_vertex_cut A L hLA hpure hcofaces hfull hLcard
      number sign hnumber hcancel v p hvp hpne hedge hlink hexhaust t ht htex htsign
  obtain ⟨z, hz, hz0, hz1⟩ := hZ.exists_unitInterval_chart_with_endpoints hm
  have hmc (j b : Bool) : m j ≠ c j b := by
    intro h
    have he := congrArg Subtype.val (A.faceCentroid_injective
      (a₁ := ⟨s j, hLA (hedge j)⟩) (a₂ := ⟨t j b, (ht j b).1⟩) h)
    have hsize := congrArg Finset.card he
    rw [Finset.card_pair (hvp j), (ht j b).2.1] at hsize
    omega
  have hD (j b : Bool) : IsFinitePLBallPair ℝ (D j b) {m j, c j b} := by
    have h := isFinitePLBallPair_affine_interval (show (0 : ℝ) < 1 from zero_lt_one)
      (ContinuousAffineMap.lineMap (m j) (c j b)) (AffineMap.lineMap_injective ℝ (hmc j b)).injOn
    simpa only [D, ContinuousAffineMap.coe_lineMap_eq, AffineMap.lineMap_apply_zero,
      AffineMap.lineMap_apply_one, ← segment_eq_image_lineMap] using h
  have hDJ (j b : Bool) : D j b ⊆ (A.barycentricDualBlock (s j)).space := by
    intro y hy
    let x := (r j b).symm ⟨y, hy⟩
    have hx : (J j ⟨x, by cases b; exact Or.inl x.property; exact Or.inr x.property⟩ : E) = y :=
      (hJr j b x).trans (congrArg Subtype.val ((r j b).apply_symm_apply _))
    exact hx ▸ (J j ⟨x, by cases b; exact Or.inl x.property; exact Or.inr x.property⟩).property
  have hsne : s false ≠ s true := by
    intro he
    have hp : p false ∈ s true := he ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    rcases Finset.mem_insert.mp hp with h | h
    · exact hvp false h.symm
    · exact hpne (Finset.mem_singleton.mp h)
  have hdis := boundary_circle_joints_disjoint A L hfull hLcard
    (hedge false) (hedge true) (Finset.card_pair (hvp false)) (Finset.card_pair (hvp true)) hsne
  have hDis (b : Bool) : Disjoint (D false b) (D true b) := hdis.mono (hDJ false b) (hDJ true b)
  obtain ⟨H, hH, _, hHE, hHZ, _⟩ := exists_boundary_vertex_strip_from_halves
    V Z F U D m c hF hZ hU hZU hD hDU hm hmc hDis hFU hFI z hz hz0 hz1 r hr hrm hrc
  refine ⟨H, hH, ?_, ?_⟩
  · intro j x
    rcases x.property with hx | hx
    · exact (hHE j false ⟨x, hx⟩).trans (hJr j false ⟨x, hx⟩).symm
    · exact (hHE j true ⟨x, hx⟩).trans (hJr j true ⟨x, hx⟩).symm
  · intro x
    exact (show (H x : E) ∈ L.space ↔ (H x : E) ∈ Z from
      (and_iff_right (H x).property).symm).trans (hHZ x)

end PoincareConjecture.M76.Dehn
