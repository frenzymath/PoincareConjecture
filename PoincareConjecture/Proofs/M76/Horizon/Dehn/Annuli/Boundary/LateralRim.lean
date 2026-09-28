import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Boundary.Circles.BoundaryCircleAnnulus
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.SourceDiskBoundary

set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76.Dehn

local notation "P2" => (ℝ × ℝ)

theorem signedTubeSheet_zero_coordinates (x : P2) :
    x ∈ signedTubeSheet 0 ↔ x.1 = 0 ∧ x.2 ∈ Icc (-1 : ℝ) 1 := by
  constructor
  · rintro (hx | hx)
    all_goals
      obtain ⟨a, b, ha, hb, hab, hval⟩ := hx
      have hfst := congrArg Prod.fst hval
      have hsnd := congrArg Prod.snd hval
      norm_num [signedTubeCorner] at hfst hsnd
      exact ⟨hfst.symm, by constructor <;> linarith⟩
  · rintro ⟨hx, hy⟩
    have hd : x ∈ signedTubeDiamond := by
      rw [signedTubeDiamond_coordinate_iff, hx]
      simpa using abs_le.mpr hy
    exact (signedTubeSheet_coordinate_iff x hd 0).mpr hx

theorem signedTubeSheet_zero_ball :
    IsFinitePLBallPair ℝ (signedTubeSheet 0) {(0, -1), (0, 1)} := by
  let f : ℝ →L[ℝ] P2 := (0 : ℝ →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ ℝ)
  have hf : Function.Injective f := fun x y h ↦ congrArg Prod.snd h
  have himage : f '' Icc (-1 : ℝ) 1 = signedTubeSheet 0 := by
    ext x
    rw [signedTubeSheet_zero_coordinates]
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨rfl, ht⟩
    · rintro ⟨hx, hy⟩
      exact ⟨x.2, hy, Prod.ext hx.symm rfl⟩
  have h := (isFinitePLBallPair_Icc (show (-1 : ℝ) < 1 by norm_num)).affine_image
    f.toContinuousAffineMap hf.injOn
  change IsFinitePLBallPair ℝ (f '' Icc (-1 : ℝ) 1) (f '' ({-1, 1} : Set ℝ)) at h
  rw [himage, image_pair] at h
  exact h

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]
  {A L : SimplicialComplex ℝ E} [Fintype A.faces]
  {n : ℕ} {p : Fin (n + 3) → E}

theorem BoundaryCircleBlockData.map_mem_vertex_rim_iff
    (D : BoundaryCircleBlockData A L p)
    (hpure : ∀ s ∈ A.faces, ∃ t ∈ A.faces, t.card = 3 ∧ s ⊆ t)
    (hcofaces : ∀ s ∈ A.faces, s.card = 2 →
      {t : Finset E | t ∈ A.faces ∧ t.card = 3 ∧ s ⊆ t}.ncard = 2)
    (hp : ∀ j, p j ∈ A.vertices)
    (hlinks : ∀ j, IsConnected (A.link (p j)).space)
    (j : Fin (n + 3)) (x : ↥(signedTubeSheet 0 ×ˢ Icc (0 : ℝ) 1)) :
    (D.map j x : E) ∈ (A.barycentricSubdivision.link (p j)).space ↔
      x.val.1.2 = -1 ∨ x.val.1.2 = 1 ∨ x.val.2 = 0 ∨ x.val.2 = 1 := by
  have hsource := signedTubeSheet_zero_ball.prod
    (isFinitePLBallPair_Icc (show (0 : ℝ) < 1 from zero_lt_one))
  have htarget := A.isFinitePLBallPair_barycentricDualBlock_vertex hpure hcofaces (hp j) (hlinks j)
  have heq := _root_.Dehn.finitePL_ball_homeomorph_boundary hsource htarget
    (D.map j) (D.mapPL j) x
  have hx := (signedTubeSheet_zero_coordinates x.val.1).mp x.property.1
  simpa only [mem_union, mem_prod, mem_insert_iff, mem_singleton_iff,
    Prod.ext_iff, hx.1, true_and, x.property.1, x.property.2, and_true, or_assoc] using heq

theorem BoundaryCircleBlockData.joint_mem_endpoints_iff
    (D : BoundaryCircleBlockData A L p)
    (hpure : ∀ s ∈ A.faces, ∃ t ∈ A.faces, t.card = 3 ∧ s ⊆ t)
    (hcofaces : ∀ s ∈ A.faces, s.card = 2 →
      {t : Finset E | t ∈ A.faces ∧ t.card = 3 ∧ s ⊆ t}.ncard = 2)
    (hpi : Function.Injective p)
    (hedge : ∀ j, ({p j, p (finRotate (n + 3) j)} : Finset E) ∈ A.faces)
    (j : Fin (n + 3)) :
    ∃ t : Bool → Finset E,
      (∀ b, t b ∈ A.faces ∧ (t b).card = 3 ∧
        ({p j, p (finRotate (n + 3) j)} : Finset E) ⊆ t b) ∧
      t false ≠ t true ∧
      (∀ u ∈ A.faces, u.card = 3 →
        ({p j, p (finRotate (n + 3) j)} : Finset E) ⊆ u → u = t false ∨ u = t true) ∧
      ∀ x : signedTubeSheet 0,
        (D.joint j x : E) ∈ ({(t false).centroid ℝ id, (t true).centroid ℝ id} : Set E) ↔
          x.val.2 = -1 ∨ x.val.2 = 1 := by
  have hbound (s : Finset E) (hs : s ∈ A.faces) : s.card ≤ 3 := by
    obtain ⟨t, _, ht, hst⟩ := hpure s hs
    exact (Finset.card_le_card hst).trans_eq ht
  have hnext : j ≠ finRotate (n + 3) j := by
    intro heq
    have hh : (0 : Fin (n + 3)) = 1 := add_left_cancel
      (show j + 0 = j + 1 by simpa only [finRotate_apply, add_zero] using heq)
    have := congrArg Fin.val hh
    norm_num at this
  obtain ⟨t, ht, hne, hex, hpair, _⟩ := exists_boundary_circle_joint A hbound hcofaces
    (hedge j) (Finset.card_pair (hpi.ne hnext))
  refine ⟨t, ht, hne, hex, ?_⟩
  intro x
  have hx := (signedTubeSheet_zero_coordinates x.val).mp x.property
  simpa only [mem_insert_iff, mem_singleton_iff, Prod.ext_iff, hx.1, true_and] using
    (_root_.Dehn.finitePL_ball_homeomorph_boundary signedTubeSheet_zero_ball hpair
      (D.joint j) (D.jointPL j) x)

end PoincareConjecture.M76.Dehn
