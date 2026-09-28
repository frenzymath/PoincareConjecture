import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Collars.CircleBlocks
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.Tubes.PairedTubeMap

set_option autoImplicit false
open Set Geometry Geometry.SimplicialComplex

namespace PoincareConjecture.M76
open Dehn
local notation "V3" => (Fin 3 → ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)

theorem exists_coordinate_signed_circle_tube
    (P : Fin 3 → SimplicialComplex ℝ V3) (hP : ∀ i, (P i).faces.Finite)
    {m : ℕ} (L : Polygon V3 (m + 3)) (hL : L.HasSimplicialEdges)
    (hLi : Function.Injective L) (hPL : (P 2).space = L.boundary ℝ)
    {W : Set V3} (hW : IsOpen W) (hLW : L.boundary ℝ ⊆ W)
    (hisolate : ∀ x ∈ W, x ∈ L.boundary ℝ ↔ x ∈ (P 0).space ∧ x ∈ (P 1).space)
    (hcharts : ∀ x ∈ L.boundary ℝ, ∃ B : OpenPartialHomeomorph V3 V3,
      x ∈ B.source ∧ B ∈ piecewiseAffineGroupoid V3 ∧
      ∀ (i : Fin 2) y, y ∈ B.source → (y ∈ (P i.castSucc).space ↔ B y i.castSucc = 0)) :
    ∃ (n : ℕ) (closing : Fin 2 → Bool) (sigma : C3 → V3),
      FinitePiecewiseAffineOn sigma (signedTubeDiamond ×ˢ Icc (0 : ℝ) (n + 3)) ∧
      MapsTo sigma (signedTubeDiamond ×ˢ Icc (0 : ℝ) (n + 3)) W ∧
      L.boundary ℝ ⊆ interior (sigma '' (signedTubeDiamond ×ˢ Icc (0 : ℝ) (n + 3))) ∧
      (∀ k (x : ↥(signedTubeDiamond ×ˢ Icc (0 : ℝ) (n + 3))),
        sigma x ∈ (P k.castSucc).space ↔ (x : C3).1 ∈ signedTubeSheet k) ∧
      (∀ x : ↥(signedTubeDiamond ×ˢ Icc (0 : ℝ) (n + 3)),
        sigma x ∈ L.boundary ℝ ↔ (x : C3).1 = (0, 0)) ∧
      (fun t : ℝ ↦ sigma ((0, 0), t)) '' Icc (0 : ℝ) (n + 3) = L.boundary ℝ ∧
      ∀ x y : ↥(signedTubeDiamond ×ˢ Icc (0 : ℝ) (n + 3)),
        sigma x = sigma y ↔ x = y ∨
          ((x : C3).2 = 0 ∧ (y : C3).2 = n + 3 ∧
            signedTubeReflection closing (x : C3).1 = (y : C3).1) ∨
          ((y : C3).2 = 0 ∧ (x : C3).2 = n + 3 ∧
            signedTubeReflection closing (y : C3).1 = (x : C3).1) := by
  classical
  obtain ⟨N, M, n, p, hN, hLN, hNW, hM, hreg, hfr, harc, hsheetEq,
    hpi, hpv, hpf, joint, left, right, map, hjointPL, hmapPL,
    hlower₀, hupper₀, hsheets₀, haxis₀⟩ := exists_coordinate_circle_blocks
      P hP L hL hLi hPL hW hLW hisolate hcharts
  letI : Fintype N.faces := hN.fintype
  let t : Fin (n + 4) → ℝ := fun j ↦ j.val
  have ht : StrictMono t := fun _ _ h ↦ Nat.cast_lt.mpr h
  have hsucc (j : Fin (n + 2)) : finRotate (n + 3) j.castSucc = j.succ := by
    apply Fin.ext
    rw [coe_finRotate_of_ne_last]
    · rfl
    · intro h
      have := congrArg Fin.val h
      simp only [Fin.val_castSucc, Fin.val_last] at this
      omega
  have hprev (j : Fin (n + 2)) : (finRotate (n + 3)).symm j.succ = j.castSucc :=
    (Equiv.symm_apply_eq _).mpr (hsucc j).symm
  have hlast : finRotate (n + 3) (Fin.last (n + 2)) = 0 := finRotate_last
  have hfirst : (finRotate (n + 3)).symm 0 = Fin.last (n + 2) :=
    (Equiv.symm_apply_eq _).mpr hlast.symm
  let B := fun j ↦ (N.barycentricDualBlock {p j}).space
  let J := fun j : Fin (n + 2) ↦
    (N.barycentricDualBlock {p j.castSucc, p (finRotate (n + 3) j.castSucc)}).space
  let Jclose := (N.barycentricDualBlock
    {p (Fin.last (n + 2)), p (finRotate (n + 3) (Fin.last (n + 2)))}).space
  obtain ⟨hcontact, hclose, _, _, hfar, _, _, hcover⟩ :=
    N.full_cyclic_dual_contacts_linear (M (.inr 2))
      (hM (.inr 2)).1 (hM (.inr 2)).2.2 p hpi hpv hpf
  have hmaps (j : Fin (n + 3)) :
      ∃ map' : ↥(signedTubeDiamond ×ˢ Icc (t j.castSucc) (t j.succ)) ≃ₜ B j,
        map'.IsFinitePL ∧ ∀ x,
          (map' x : V3) = map j
            ⟨((x : C3).1, (x : C3).2 - (j.val : ℝ)), x.property.1,
              by
                have h0 := x.property.2.1
                have h1 := x.property.2.2
                simp only [t, Fin.val_castSucc, Fin.val_succ, Nat.cast_add, Nat.cast_one] at h0 h1
                constructor <;> linarith⟩ := by
    obtain ⟨map', hm, hv⟩ :=
      exists_translated_unit_diamond_block (map j) (hmapPL j) (j.val : ℝ)
    have hsource : signedTubeDiamond ×ˢ Icc (j.val : ℝ) (j.val + 1) =
        signedTubeDiamond ×ˢ Icc (t j.castSucc) (t j.succ) := by simp [t]
    let map'' := (Homeomorph.setCongr hsource.symm).trans
      (map'.trans (Homeomorph.setCongr rfl))
    refine ⟨map'', hm.setCongr hsource rfl, ?_⟩
    intro x
    exact hv ⟨x, hsource.symm ▸ x.property⟩
  choose maps hmapsPL hmapsVal using hmaps
  have hupper (j : Fin (n + 2)) (x : signedTubeDiamond) :
      (maps j.castSucc ⟨(x, t j.castSucc.succ), x.property,
        (ht Fin.castSucc_lt_succ).le, le_rfl⟩ : V3) =
          joint j.castSucc (signedTubeDiamondReflection (right j.castSucc) x) := by
    rw [hmapsVal]
    convert hupper₀ j.castSucc x using 1
    norm_num [t, Nat.cast_add]
  have hlower (j : Fin (n + 2)) (x : signedTubeDiamond) :
      (maps j.succ ⟨(x, t j.succ.castSucc), x.property,
        le_rfl, (ht Fin.castSucc_lt_succ).le⟩ : V3) =
          joint j.castSucc (signedTubeDiamondReflection (left j.succ) x) := by
    rw [hmapsVal]
    have h := hlower₀ j.succ x
    rw [hprev] at h
    simpa only [t, Fin.val_castSucc, sub_self] using h
  have hfirst' (x : signedTubeDiamond) :
      (maps 0 ⟨(x, t 0), x.property, le_rfl,
        (ht (show (0 : Fin (n + 4)) < (0 : Fin (n + 3)).succ from by
          change (0 : ℕ) < 1; omega)).le⟩ : V3) =
        joint (Fin.last (n + 2)) (signedTubeDiamondReflection (left 0) x) := by
    rw [hmapsVal]
    have h := hlower₀ 0 x
    rw [hfirst] at h
    simpa only [t, Fin.val_zero, Nat.cast_zero, sub_self] using h
  have hlast' (x : signedTubeDiamond) :
      (maps (Fin.last (n + 2)) ⟨(x, t (Fin.last (n + 3))), x.property,
        (ht Fin.castSucc_lt_succ).le, le_rfl⟩ : V3) =
        joint (Fin.last (n + 2))
          (signedTubeDiamondReflection (right (Fin.last (n + 2))) x) := by
    rw [hmapsVal]
    convert hupper₀ (Fin.last (n + 2)) x using 1
    norm_num [t, Nat.cast_add]
  obtain ⟨frame, closing, sigma, hf0, hc, hPL', hval, himage, hfib⟩ :=
    exists_signed_cyclic_tube_of_incident_frames t ht B J
      (fun j ↦ joint j.castSucc) (fun j ↦ hjointPL j.castSucc) maps hmapsPL
      (fun j ↦ right j.castSucc) (fun j ↦ left j.succ)
      (left 0) (right (Fin.last (n + 2))) (fun _ ↦ true)
      (by intro j; simpa only [J, B, hsucc] using hcontact j)
      hupper hlower Jclose (joint (Fin.last (n + 2)))
      (by simpa only [Jclose, B, hlast] using hclose) hfirst' hlast' hfar
  have htime : t 0 = 0 ∧ t (Fin.last (n + 3)) = (n : ℝ) + 3 := by simp [t]
  have hpiece (x : ↥(signedTubeDiamond ×ˢ Icc (0 : ℝ) (n + 3))) :
      ∃ j : Fin (n + 3), (x : C3).2 ∈ Icc (t j.castSucc) (t j.succ) := by
    apply ht.monotone.exists_mem_consecutive_Icc
    simpa only [htime.1, htime.2] using x.property.2
  have himage' : sigma '' (signedTubeDiamond ×ˢ Icc (0 : ℝ) (n + 3)) =
      (N.barycentricNeighborhood (M (.inr 2))).space := by
    apply Eq.trans _ hcover
    simpa only [htime.1, htime.2] using himage
  have hNimage : MapsTo sigma (signedTubeDiamond ×ˢ Icc (0 : ℝ) (n + 3)) N.space := by
    intro x hx
    have hsub := space_subset_of_le (N.barycentricNeighborhood_le (M (.inr 2)))
      (himage'.subset (mem_image_of_mem sigma hx))
    exact N.barycentricSubdivision_isSubdivision.space_eq ▸ hsub
  have hsheets (k : Fin 2) (x : ↥(signedTubeDiamond ×ˢ Icc (0 : ℝ) (n + 3))) :
      sigma x ∈ (M (.inr k.castSucc)).space ↔ (x : C3).1 ∈ signedTubeSheet k := by
    obtain ⟨j, hj⟩ := hpiece x
    let y : ↥(signedTubeDiamond ×ˢ Icc (t j.castSucc) (t j.succ)) := ⟨x, x.property.1, hj⟩
    rw [hval j y, hmapsVal]
    exact (hsheets₀ j k _).symm.trans (signedTubeReflection_mem_sheet (frame j) k _)
  have haxis (x : ↥(signedTubeDiamond ×ˢ Icc (0 : ℝ) (n + 3))) :
      sigma x ∈ (M (.inr 2)).space ↔ (x : C3).1 = (0, 0) := by
    obtain ⟨j, hj⟩ := hpiece x
    let y : ↥(signedTubeDiamond ×ˢ Icc (t j.castSucc) (t j.succ)) := ⟨x, x.property.1, hj⟩
    rw [hval j y, hmapsVal, ← haxis₀]
    change signedTubeReflection (frame j) (x : C3).1 = (0, 0) ↔ _
    simpa only [signedTubeReflection_zero] using
      (signedTubeReflection (frame j)).injective.eq_iff
        (a := (x : C3).1) (b := (0, 0))
  have haxisInt : L.boundary ℝ ⊆ interior
      (sigma '' (signedTubeDiamond ×ˢ Icc (0 : ℝ) (n + 3))) := by
    letI : Fintype (M (.inr 2)).faces := (hM (.inr 2)).2.1.fintype
    obtain ⟨U, hU, hAU, hUN⟩ := N.exists_open_barycentricNeighborhood (hM (.inr 2)).1
    have hsub : U ∩ interior N.space ⊆ sigma '' (signedTubeDiamond ×ˢ Icc (0 : ℝ) (n + 3)) := by
      rw [himage']
      exact fun _ hx => hUN ⟨hx.1, interior_subset hx.2⟩
    exact fun _ hx => (hU.inter isOpen_interior).subset_interior_iff.mpr hsub
      ⟨hAU (harc.symm ▸ hx), hLN hx⟩
  refine ⟨n, closing, sigma, ?_, fun x hx => hNW (hNimage hx), haxisInt, ?_, ?_, ?_, ?_⟩
  · simpa only [htime.1, htime.2] using hPL'
  · intro k x
    have h := hsheets k x
    rw [hsheetEq] at h
    exact (and_iff_right (hNimage x.property)).symm.trans h
  · intro x
    simpa only [harc] using haxis x
  · letI : Fintype (M (.inr 2)).faces := (hM (.inr 2)).2.1.fintype
    rw [← harc]
    ext z
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact (haxis ⟨((0, 0), t), signedTubeRadius_subset_diamond 0 false
        (left_mem_segment ℝ _ _), ht⟩).mpr rfl
    · intro hz
      have hzN := N.space_subset_barycentricNeighborhood (hM (.inr 2)).1 hz
      obtain ⟨x, hx, rfl⟩ := himage'.symm.subset hzN
      have hx0 := (haxis ⟨x, hx⟩).mp hz
      exact ⟨x.2, hx.2, congrArg sigma (Prod.ext hx0.symm rfl)⟩
  · rw [htime.1, htime.2] at hfib
    exact hfib

end PoincareConjecture.M76
