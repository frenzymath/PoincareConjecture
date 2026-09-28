import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.Tubes.PairedTube
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.Tubes.PairedTubeSigns

set_option autoImplicit false
open Set Metric Geometry Geometry.SimplicialComplex Topology

namespace PoincareConjecture.M76.Dehn
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)
local notation "C3" => (P2 × ℝ)

variable {X ι : Type*} [TopologicalSpace X]
  {e : ι → OpenPartialHomeomorph X V3} {f : V2 → X} {R : Set X}
  {old : OrdinaryDoubleCurveModel e f R} {i : old.Index}

theorem PairedCircleBlockData.exists_cyclic_map
    (D : OrdinaryIntervalMarkedModel old i) [Fintype D.complex.faces]
    {n : ℕ} (p : Fin (n + 3) → D.sample → ℝ × V3)
    (hpi : Function.Injective p) (hpv : range p = (D.marks (.inr 2)).vertices)
    (hpf : ∀ s : Finset (D.sample → ℝ × V3), s ∈ (D.marks (.inr 2)).faces ↔
      s.Nonempty ∧ ∃ j : Fin (n + 3), s ⊆ {p j, p (finRotate (n + 3) j)})
    (C : PairedCircleBlockData D p) :
    ∃ (frame : Fin (n + 3) → Fin 2 → Bool) (closing : Fin 2 → Bool)
      (sigma : C3 → D.sample → ℝ × V3),
      frame 0 = (fun _ ↦ true) ∧
      closing = signedCycleClosingFrame (C.left 0) (C.right (Fin.last (n + 2)))
        (frame 0) (frame (Fin.last (n + 2))) ∧
      FinitePiecewiseAffineOn sigma (signedTubeDiamond ×ˢ Icc (0 : ℝ) (n + 3)) ∧
      sigma '' (signedTubeDiamond ×ˢ Icc (0 : ℝ) (n + 3)) =
        (D.complex.barycentricNeighborhood (D.marks (.inr 2))).space ∧
      (∀ k (x : ↥(signedTubeDiamond ×ˢ Icc (0 : ℝ) (n + 3))),
        sigma x ∈ (D.marks (.inr k.castSucc)).space ↔
          (x : C3).1 ∈ signedTubeSheet k) ∧
      (∀ x : ↥(signedTubeDiamond ×ˢ Icc (0 : ℝ) (n + 3)),
        sigma x ∈ (D.marks (.inr 2)).space ↔ (x : C3).1 = (0, 0)) ∧
      (fun t : ℝ ↦ sigma ((0, 0), t)) '' Icc (0 : ℝ) (n + 3) =
        (D.marks (.inr 2)).space ∧
      ∀ x y : ↥(signedTubeDiamond ×ˢ Icc (0 : ℝ) (n + 3)),
        sigma x = sigma y ↔ x = y ∨
          ((x : C3).2 = 0 ∧ (y : C3).2 = n + 3 ∧
            signedTubeReflection closing (x : C3).1 = (y : C3).1) ∨
          ((y : C3).2 = 0 ∧ (x : C3).2 = n + 3 ∧
            signedTubeReflection closing (y : C3).1 = (x : C3).1) := by
  classical
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
  let B := fun j ↦ (D.complex.barycentricDualBlock {p j}).space
  let J := fun j : Fin (n + 2) ↦
    (D.complex.barycentricDualBlock {p j.castSucc, p (finRotate (n + 3) j.castSucc)}).space
  let Jclose := (D.complex.barycentricDualBlock
    {p (Fin.last (n + 2)), p (finRotate (n + 3) (Fin.last (n + 2)))}).space
  obtain ⟨hcontact, hclose, _, _, hfar, _, _, hcover⟩ :=
    D.complex.full_cyclic_dual_contacts_linear (D.marks (.inr 2))
      (D.marks_full (.inr 2)).1 (D.marks_full (.inr 2)).2.2 p hpi hpv hpf
  have hmaps (j : Fin (n + 3)) :
      ∃ map : ↥(signedTubeDiamond ×ˢ Icc (t j.castSucc) (t j.succ)) ≃ₜ B j,
        map.IsFinitePL ∧ ∀ x,
          (map x : D.sample → ℝ × V3) = C.map j
            ⟨((x : C3).1, (x : C3).2 - (j.val : ℝ)), x.property.1,
              by
                have h0 := x.property.2.1
                have h1 := x.property.2.2
                simp only [t, Fin.val_castSucc, Fin.val_succ, Nat.cast_add, Nat.cast_one] at h0 h1
                constructor <;> linarith⟩ := by
    obtain ⟨map, hm, hv⟩ :=
      exists_translated_unit_diamond_block (C.map j) (C.mapPL j) (j.val : ℝ)
    have hsource : signedTubeDiamond ×ˢ Icc (j.val : ℝ) (j.val + 1) =
        signedTubeDiamond ×ˢ Icc (t j.castSucc) (t j.succ) := by simp [t]
    let map' := (Homeomorph.setCongr hsource.symm).trans (map.trans (Homeomorph.setCongr rfl))
    refine ⟨map', hm.setCongr hsource rfl, ?_⟩
    intro x
    exact hv ⟨x, hsource.symm ▸ x.property⟩
  choose maps hmapsPL hmapsVal using hmaps
  have hupper (j : Fin (n + 2)) (x : signedTubeDiamond) :
      (maps j.castSucc ⟨(x, t j.castSucc.succ), x.property,
        (ht Fin.castSucc_lt_succ).le, le_rfl⟩ : D.sample → ℝ × V3) =
          C.joint j.castSucc (signedTubeDiamondReflection (C.right j.castSucc) x) := by
    rw [hmapsVal]
    convert C.upper j.castSucc x using 1
    norm_num [t, Nat.cast_add]
  have hlower (j : Fin (n + 2)) (x : signedTubeDiamond) :
      (maps j.succ ⟨(x, t j.succ.castSucc), x.property,
        le_rfl, (ht Fin.castSucc_lt_succ).le⟩ : D.sample → ℝ × V3) =
          C.joint j.castSucc (signedTubeDiamondReflection (C.left j.succ) x) := by
    rw [hmapsVal]
    have h := C.lower j.succ x
    rw [hprev] at h
    simpa only [t, Fin.val_castSucc, sub_self] using h
  have hfirst' (x : signedTubeDiamond) :
      (maps 0 ⟨(x, t 0), x.property, le_rfl,
        (ht (show (0 : Fin (n + 4)) < (0 : Fin (n + 3)).succ from by
          change (0 : ℕ) < 1; omega)).le⟩ : D.sample → ℝ × V3) =
        C.joint (Fin.last (n + 2)) (signedTubeDiamondReflection (C.left 0) x) := by
    rw [hmapsVal]
    have h := C.lower 0 x
    rw [hfirst] at h
    simpa only [t, Fin.val_zero, Nat.cast_zero, sub_self] using h
  have hlast' (x : signedTubeDiamond) :
      (maps (Fin.last (n + 2)) ⟨(x, t (Fin.last (n + 3))), x.property,
        (ht Fin.castSucc_lt_succ).le, le_rfl⟩ : D.sample → ℝ × V3) =
        C.joint (Fin.last (n + 2))
          (signedTubeDiamondReflection (C.right (Fin.last (n + 2))) x) := by
    rw [hmapsVal]
    convert C.upper (Fin.last (n + 2)) x using 1
    norm_num [t, Nat.cast_add]
  obtain ⟨frame, closing, sigma, hf0, hc, hPL, hval, himage, hfib⟩ :=
    exists_signed_cyclic_tube_of_incident_frames t ht B J
      (fun j ↦ C.joint j.castSucc) (fun j ↦ C.jointPL j.castSucc) maps hmapsPL
      (fun j ↦ C.right j.castSucc) (fun j ↦ C.left j.succ)
      (C.left 0) (C.right (Fin.last (n + 2))) (fun _ ↦ true)
      (by intro j; simpa only [J, B, hsucc] using hcontact j)
      hupper hlower Jclose (C.joint (Fin.last (n + 2)))
      (by simpa only [Jclose, B, hlast] using hclose) hfirst' hlast' hfar
  have htime : t 0 = 0 ∧ t (Fin.last (n + 3)) = (n : ℝ) + 3 := by
    simp [t]
  have hpiece (x : ↥(signedTubeDiamond ×ˢ Icc (0 : ℝ) (n + 3))) :
      ∃ j : Fin (n + 3), (x : C3).2 ∈ Icc (t j.castSucc) (t j.succ) := by
    apply ht.monotone.exists_mem_consecutive_Icc
    simpa only [htime.1, htime.2] using x.property.2
  have hsheet (k : Fin 2) (x : ↥(signedTubeDiamond ×ˢ Icc (0 : ℝ) (n + 3))) :
      sigma x ∈ (D.marks (.inr k.castSucc)).space ↔ (x : C3).1 ∈ signedTubeSheet k := by
    obtain ⟨j, hj⟩ := hpiece x
    let y : ↥(signedTubeDiamond ×ˢ Icc (t j.castSucc) (t j.succ)) := ⟨x, x.property.1, hj⟩
    rw [hval j y, hmapsVal]
    exact (C.sheets j k _).symm.trans (signedTubeReflection_mem_sheet (frame j) k _)
  have haxis (x : ↥(signedTubeDiamond ×ˢ Icc (0 : ℝ) (n + 3))) :
      sigma x ∈ (D.marks (.inr 2)).space ↔ (x : C3).1 = (0, 0) := by
    obtain ⟨j, hj⟩ := hpiece x
    let y : ↥(signedTubeDiamond ×ˢ Icc (t j.castSucc) (t j.succ)) := ⟨x, x.property.1, hj⟩
    rw [hval j y, hmapsVal, ← C.axis]
    change signedTubeReflection (frame j) (x : C3).1 = (0, 0) ↔ _
    simpa only [signedTubeReflection_zero] using
      (signedTubeReflection (frame j)).injective.eq_iff
        (a := (x : C3).1) (b := (0, 0))
  have himage' : sigma '' (signedTubeDiamond ×ˢ Icc (0 : ℝ) (n + 3)) =
      (D.complex.barycentricNeighborhood (D.marks (.inr 2))).space := by
    apply Eq.trans _ hcover
    simpa only [htime.1, htime.2] using himage
  refine ⟨frame, closing, sigma, hf0, hc, ?_, himage', hsheet, haxis, ?_, ?_⟩
  · simpa only [htime.1, htime.2] using hPL
  · let _ : Fintype (D.marks (.inr 2)).faces := (D.marks_full (.inr 2)).2.1.fintype
    ext z
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact (haxis ⟨((0, 0), t), signedTubeRadius_subset_diamond 0 false
        (left_mem_segment ℝ _ _), ht⟩).mpr rfl
    · intro hz
      have hzN := D.complex.space_subset_barycentricNeighborhood
        (D.marks_full (.inr 2)).1 hz
      obtain ⟨x, hx, rfl⟩ := himage'.symm.subset hzN
      have hx0 := (haxis ⟨x, hx⟩).mp hz
      exact ⟨x.2, hx.2, congrArg sigma (Prod.ext hx0.symm rfl)⟩
  · rw [htime.1, htime.2] at hfib
    exact hfib

theorem OrdinaryIntervalMarkedModel.exists_signed_circle_tube
    (D : OrdinaryIntervalMarkedModel old i) (hcore : D.core ⊆ interior R)
    {m : ℕ} (P : Polygon V2 (m + 3)) (hP : P.HasSimplicialEdges)
    (hPi : Function.Injective P) (hPs : P.boundary ℝ = old.pieces i) :
    letI : Fintype D.complex.faces := D.complex_finite.fintype
    ∃ (n : ℕ) (closing : Fin 2 → Bool) (sigma : C3 → D.sample → ℝ × V3),
      FinitePiecewiseAffineOn sigma (signedTubeDiamond ×ˢ Icc (0 : ℝ) (n + 3)) ∧
      sigma '' (signedTubeDiamond ×ˢ Icc (0 : ℝ) (n + 3)) =
        (D.complex.barycentricNeighborhood (D.marks (.inr 2))).space ∧
      MapsTo sigma (signedTubeDiamond ×ˢ Icc (0 : ℝ) (n + 3)) D.complex.space ∧
      (∀ k (x : ↥(signedTubeDiamond ×ˢ Icc (0 : ℝ) (n + 3))),
        sigma x ∈ (D.marks (.inr k.castSucc)).space ↔
          (x : C3).1 ∈ signedTubeSheet k) ∧
      (∀ x : ↥(signedTubeDiamond ×ˢ Icc (0 : ℝ) (n + 3)),
        sigma x ∈ (D.marks (.inr 2)).space ↔ (x : C3).1 = (0, 0)) ∧
      (fun t : ℝ ↦ sigma ((0, 0), t)) '' Icc (0 : ℝ) (n + 3) =
        (D.marks (.inr 2)).space ∧
      ∀ x y : ↥(signedTubeDiamond ×ˢ Icc (0 : ℝ) (n + 3)),
        sigma x = sigma y ↔ x = y ∨
          ((x : C3).2 = 0 ∧ (y : C3).2 = n + 3 ∧
            signedTubeReflection closing (x : C3).1 = (y : C3).1) ∨
          ((y : C3).2 = 0 ∧ (x : C3).2 = n + 3 ∧
            signedTubeReflection closing (y : C3).1 = (x : C3).1) := by
  classical
  let _ : Fintype D.complex.faces := D.complex_finite.fintype
  obtain ⟨n, p, hpi, hpv, hpf, ⟨C⟩⟩ := D.exists_circle_block_data hcore P hP hPi hPs
  obtain ⟨_, closing, sigma, _, _, hPL, himage, hsheet, haxis, haxisImage, hfib⟩ :=
    C.exists_cyclic_map D p hpi hpv hpf
  refine ⟨n, closing, sigma, hPL, himage, ?_, hsheet, haxis, haxisImage, hfib⟩
  intro x hx
  have hN := himage.subset (mem_image_of_mem sigma hx)
  have hsub := space_subset_of_le (D.complex.barycentricNeighborhood_le (D.marks (.inr 2))) hN
  exact D.complex.barycentricSubdivision_isSubdivision.space_eq ▸ hsub

theorem OrdinaryDoubleCurveModel.exists_paired_circle_polygons
    (old : OrdinaryDoubleCurveModel e f R) {i : old.Index}
    {m : ℕ} (P : Polygon V2 (m + 3)) (hP : P.HasSimplicialEdges)
    (hPi : Function.Injective P) (hPs : P.boundary ℝ = old.pieces i) :
    ∃ (nP : Fin 2 → ℕ) (Pj : ∀ j, Polygon V2 (nP j + 3)),
      (∀ j, (Pj j).HasSimplicialEdges) ∧ (∀ j, Function.Injective (Pj j)) ∧
      ∀ j, (Pj j).boundary ℝ = old.pieces (if j = 0 then i else old.mate i) := by
  classical
  obtain ⟨g, hg, hgval⟩ := old.partnerPL
  have hsub : P.boundary ℝ ⊆ doubleLocusOn f (closedBall (0 : V2) 1) :=
    hPs ▸ old.piece_subset_double i
  have hinj : InjOn g (P.boundary ℝ) := by
    intro x hx y hy hxy
    have hp : old.partner ⟨x, hsub hx⟩ = old.partner ⟨y, hsub hy⟩ := by
      apply Subtype.ext
      simpa only [hgval] using hxy
    exact congrArg Subtype.val (old.partner.injective hp)
  obtain ⟨k, Q, hQi, hQ, hQs⟩ := P.exists_polygon_finitePL_image hP hPi hg hsub hinj
  let d := old.partner.restrictSubsets (old.piece_subset_double i)
    (old.piece_subset_double (old.mate i)) (old.partner_component_iff i)
  have hval (x : old.pieces i) : g x = (d x : V2) :=
    (hgval ⟨x, old.piece_subset_double i x.property⟩).symm
  have himage : g '' old.pieces i = old.pieces (old.mate i) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [hval ⟨y, hy⟩]
      exact (d ⟨y, hy⟩).property
    · intro hx
      refine ⟨d.symm ⟨x, hx⟩, (d.symm ⟨x, hx⟩).property, ?_⟩
      rw [hval, d.apply_symm_apply]
  have hQpiece : Q.boundary ℝ = old.pieces (old.mate i) := by
    rw [hQs, hPs, himage]
  let nP : Fin 2 → ℕ := ![m, k]
  let Pj : ∀ j, Polygon V2 (nP j + 3) := Fin.cases P (Fin.cases Q (fun j ↦ j.elim0))
  refine ⟨nP, Pj, ?_, ?_, ?_⟩
  · intro j
    fin_cases j
    · exact hP
    · exact hQ
  · intro j
    fin_cases j
    · exact hPi
    · exact hQi
  · intro j
    fin_cases j
    · exact hPs
    · exact hQpiece

theorem OrdinaryIntervalMarkedModel.exists_identity_circle_tube
    (D : OrdinaryIntervalMarkedModel old i) (hcore : D.core ⊆ interior R)
    {m : ℕ} (P : Polygon V2 (m + 3)) (hP : P.HasSimplicialEdges)
    (hPi : Function.Injective P) (hPs : P.boundary ℝ = old.pieces i) :
    letI : Fintype D.complex.faces := D.complex_finite.fintype
    ∃ (n : ℕ) (sigma : C3 → D.sample → ℝ × V3),
      FinitePiecewiseAffineOn sigma (signedTubeDiamond ×ˢ Icc (0 : ℝ) (n + 3)) ∧
      sigma '' (signedTubeDiamond ×ˢ Icc (0 : ℝ) (n + 3)) =
        (D.complex.barycentricNeighborhood (D.marks (.inr 2))).space ∧
      MapsTo sigma (signedTubeDiamond ×ˢ Icc (0 : ℝ) (n + 3)) D.complex.space ∧
      (∀ k (x : ↥(signedTubeDiamond ×ˢ Icc (0 : ℝ) (n + 3))),
        sigma x ∈ (D.marks (.inr k.castSucc)).space ↔
          (x : C3).1 ∈ signedTubeSheet k) ∧
      (∀ x : ↥(signedTubeDiamond ×ˢ Icc (0 : ℝ) (n + 3)),
        sigma x ∈ (D.marks (.inr 2)).space ↔ (x : C3).1 = (0, 0)) ∧
      (fun t : ℝ ↦ sigma ((0, 0), t)) '' Icc (0 : ℝ) (n + 3) =
        (D.marks (.inr 2)).space ∧
      ∀ x ∈ signedTubeDiamond ×ˢ Icc (0 : ℝ) (n + 3),
        ∀ y ∈ signedTubeDiamond ×ˢ Icc (0 : ℝ) (n + 3),
          sigma x = sigma y ↔ x.1 = y.1 ∧
            (x.2 = y.2 ∨ (x.2 = 0 ∧ y.2 = n + 3) ∨ (x.2 = n + 3 ∧ y.2 = 0)) := by
  classical
  let _ : Fintype D.complex.faces := D.complex_finite.fintype
  obtain ⟨n, closing, sigma, hPL, himage, hK, hsheet, haxis, haxisImage, hfib⟩ :=
    D.exists_signed_circle_tube hcore P hP hPi hPs
  obtain ⟨nP, Pj, hPj, hPji, hPjs⟩ := old.exists_paired_circle_polygons P hP hPi hPs
  obtain ⟨_, hclosing, _⟩ := D.exists_paired_source_strips (by positivity : (0 : ℝ) < n + 3)
    sigma closing hPL hfib nP Pj hPj hPji hPjs hsheet haxis
  refine ⟨n, sigma, hPL, himage, hK, hsheet, haxis, haxisImage, ?_⟩
  intro x hx y hy
  rw [hfib ⟨x, hx⟩ ⟨y, hy⟩]
  simp only [Subtype.ext_iff, Prod.ext_iff, signedTubeReflection_apply,
    hclosing, ↓reduceIte, one_mul]
  constructor
  · rintro (h | h | h)
    · exact ⟨h.1, Or.inl h.2⟩
    · exact ⟨h.2.2, Or.inr (Or.inl ⟨h.1, h.2.1⟩)⟩
    · exact ⟨⟨h.2.2.1.symm, h.2.2.2.symm⟩, Or.inr (Or.inr ⟨h.2.1, h.1⟩)⟩
  · rintro ⟨hxy, ht | ht | ht⟩
    · exact Or.inl ⟨hxy, ht⟩
    · exact Or.inr (Or.inl ⟨ht.1, ht.2, hxy⟩)
    · exact Or.inr (Or.inr ⟨ht.2, ht.1, hxy.1.symm, hxy.2.symm⟩)

end PoincareConjecture.M76.Dehn
