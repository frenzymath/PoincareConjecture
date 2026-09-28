import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surgery.Tubes.CircleBlockData
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surgery.Tubes.Blocks.VertexFaces
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.Tubes.ComponentCyclicTube
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.Tubes.ReflectedCyclicTubeMap
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.Tubes.PairedTube










set_option autoImplicit false
open Set Metric Geometry Geometry.SimplicialComplex Topology

namespace PoincareConjecture.M76.Dehn.Annuli
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)
local notation "C3" => (P2 × ℝ)

variable {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace X] {S : Set E}
  {e : ι → OpenPartialHomeomorph X V3} {f : E → X} {R : Set X}
  {old : SourceCircleDecomposition f S} {i : old.Index}


theorem ComponentCircleBlockData.local_source_geometry
    (D : ComponentBranchModel (e := e) (R := R) old i) [Fintype D.complex.faces]
    {n : ℕ} (p : Fin (n + 3) → D.sample → ℝ × V3)
    (hpv : range p = D.axis.vertices) (C : ComponentCircleBlockData D p) :
    ∀ k, (D.complex.barycentricDualBlock {p k}).faces.Finite ∧
      (D.complex.barycentricDualBlock {p k}).space ⊆ D.complex.space ∧
      MapsTo (fun z ↦ (D.inverse z : X)) (D.complex.barycentricDualBlock {p k}).space
        (C.chart k).chart.source := by
  intro k
  have hv : p k ∈ D.axis.vertices := hpv ▸ mem_range_self k
  have hs := D.vertex_dual_subset_star (p k) hv
  exact ⟨D.complex.barycentricDualBlock_finite _, hs.trans
    (space_subset_of_le (show D.complex.closedStar (p k) ≤ D.complex from fun _ ht ↦ ht.1)),
    fun z hz ↦ C.source k (hs hz)⟩



theorem ComponentCircleBlockData.exists_cyclic_map
    (D : ComponentBranchModel (e := e) (R := R) old i) [Fintype D.complex.faces]
    (hcore : D.core ⊆ interior R)
    {n : ℕ} (p : Fin (n + 3) → D.sample → ℝ × V3)
    (hpi : Function.Injective p) (hpv : range p = D.axis.vertices)
    (hpf : ∀ s : Finset (D.sample → ℝ × V3), s ∈ D.axis.faces ↔
      s.Nonempty ∧ ∃ j : Fin (n + 3), s ⊆ {p j, p (finRotate (n + 3) j)})
    (C : ComponentCircleBlockData D p) :
    ∃ (frame : Fin (n + 3) → SignedAxisPermutation) (closing : SignedAxisPermutation)
      (sigma : C3 → D.sample → ℝ × V3),
      frame 0 = SignedAxisPermutation.refl ∧
      closing = reflectedCycleClosingFrame (C.left 0) (C.right (Fin.last (n + 2)))
        (frame 0) (frame (Fin.last (n + 2))) ∧
      FinitePiecewiseAffineOn sigma (signedTubeDiamond ×ˢ Icc (0 : ℝ) (n + 3)) ∧
      sigma '' (signedTubeDiamond ×ˢ Icc (0 : ℝ) (n + 3)) =
        (D.complex.barycentricNeighborhood D.axis).space ∧
      (∀ k : Fin (n + 3), FinitePiecewiseAffineOn sigma
        (signedTubeDiamond ×ˢ Icc (k.val : ℝ) (k.val + 1))) ∧
      (∀ k, MapsTo sigma (signedTubeDiamond ×ˢ Icc (k.val : ℝ) (k.val + 1))
        (D.complex.barycentricDualBlock {p k}).space) ∧
      (∀ k (x : ↥(signedTubeDiamond ×ˢ Icc (k.val : ℝ) (k.val + 1))),
        sigma x = C.map k ⟨((frame k).linear (x : C3).1, (x : C3).2 - k.val),
          ((frame k).mem_diamond _).mp x.property.1,
          by constructor <;> linarith [x.property.2.1, x.property.2.2]⟩) ∧
      (∀ k j z, z ∈ signedTubeDiamond ×ˢ Icc (k.val : ℝ) (k.val + 1) →
        ((C.chart k).chart (D.inverse (sigma z)) ((frame k).sheetPermutation j).castSucc = 0 ↔
          z.1 ∈ signedTubeSheet j)) ∧
      (∀ z ∈ signedTubeDiamond ×ˢ Icc (0 : ℝ) (n + 3),
        sigma z ∈ D.sourceImage.space ↔ z.1 ∈ signedTubeSheet 0 ∪ signedTubeSheet 1) ∧
      (∀ z ∈ signedTubeDiamond ×ˢ Icc (0 : ℝ) (n + 3),
        sigma z ∈ D.axis.space ↔ z.1 = (0, 0)) ∧
      (fun t : ℝ ↦ sigma ((0, 0), t)) '' Icc (0 : ℝ) (n + 3) = D.axis.space ∧
      ∀ x y : ↥(signedTubeDiamond ×ˢ Icc (0 : ℝ) (n + 3)),
        sigma x = sigma y ↔ x = y ∨
          ((x : C3).2 = 0 ∧ (y : C3).2 = n + 3 ∧
            closing.linear (x : C3).1 = (y : C3).1) ∨
          ((y : C3).2 = 0 ∧ (x : C3).2 = n + 3 ∧
            closing.linear (y : C3).1 = (x : C3).1) := by
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
    D.complex.full_cyclic_dual_contacts_linear D.axis
      D.axis_le D.axis_full p hpi hpv hpf
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
          C.joint j.castSucc ((C.right j.castSucc).diamond x) := by
    rw [hmapsVal]
    convert C.upper j.castSucc x using 1
    norm_num [t, Nat.cast_add]
  have hlower (j : Fin (n + 2)) (x : signedTubeDiamond) :
      (maps j.succ ⟨(x, t j.succ.castSucc), x.property,
        le_rfl, (ht Fin.castSucc_lt_succ).le⟩ : D.sample → ℝ × V3) =
          C.joint j.castSucc ((C.left j.succ).diamond x) := by
    rw [hmapsVal]
    have h := C.lower j.succ x
    rw [hprev] at h
    simpa only [t, Fin.val_castSucc, sub_self] using h
  have hfirst' (x : signedTubeDiamond) :
      (maps 0 ⟨(x, t 0), x.property, le_rfl,
        (ht (show (0 : Fin (n + 4)) < (0 : Fin (n + 3)).succ from by
          change (0 : ℕ) < 1; omega)).le⟩ : D.sample → ℝ × V3) =
        C.joint (Fin.last (n + 2)) ((C.left 0).diamond x) := by
    rw [hmapsVal]
    have h := C.lower 0 x
    rw [hfirst] at h
    simpa only [t, Fin.val_zero, Nat.cast_zero, sub_self] using h
  have hlast' (x : signedTubeDiamond) :
      (maps (Fin.last (n + 2)) ⟨(x, t (Fin.last (n + 3))), x.property,
        (ht Fin.castSucc_lt_succ).le, le_rfl⟩ : D.sample → ℝ × V3) =
        C.joint (Fin.last (n + 2))
          ((C.right (Fin.last (n + 2))).diamond x) := by
    rw [hmapsVal]
    convert C.upper (Fin.last (n + 2)) x using 1
    norm_num [t, Nat.cast_add]
  obtain ⟨frame, closing, sigma, hf0, hc, hPL, hval, himage, hfib⟩ :=
    exists_reflected_cyclic_tube_of_incident_frames t ht B J
      (fun j ↦ C.joint j.castSucc) (fun j ↦ C.jointPL j.castSucc) maps hmapsPL
      (fun j ↦ C.right j.castSucc) (fun j ↦ C.left j.succ)
      (C.left 0) (C.right (Fin.last (n + 2))) SignedAxisPermutation.refl
      (by intro j; simpa only [J, B, hsucc] using hcontact j)
      hupper hlower Jclose (C.joint (Fin.last (n + 2)))
      (by simpa only [Jclose, B, hlast] using hclose) hfirst' hlast' hfar
  have htime : t 0 = 0 ∧ t (Fin.last (n + 3)) = (n : ℝ) + 3 := by
    simp [t]
  have hpiece (x : ↥(signedTubeDiamond ×ˢ Icc (0 : ℝ) (n + 3))) :
      ∃ j : Fin (n + 3), (x : C3).2 ∈ Icc (t j.castSucc) (t j.succ) := by
    apply ht.monotone.exists_mem_consecutive_Icc
    simpa only [htime.1, htime.2] using x.property.2
  have hlocalValue (k : Fin (n + 3))
      (x : ↥(signedTubeDiamond ×ˢ Icc (k.val : ℝ) (k.val + 1))) :
      sigma x = C.map k ⟨((frame k).linear (x : C3).1, (x : C3).2 - k.val),
        ((frame k).mem_diamond _).mp x.property.1,
        by constructor <;> linarith [x.property.2.1, x.property.2.2]⟩ := by
    let y : ↥(signedTubeDiamond ×ˢ Icc (t k.castSucc) (t k.succ)) :=
      ⟨x, by
        simp only [t, Fin.val_castSucc, Fin.val_succ, Nat.cast_add, Nat.cast_one]
        exact x.property⟩
    exact (hval k y).trans (hmapsVal k _)
  have hlocalMaps (k : Fin (n + 3)) :
      MapsTo sigma (signedTubeDiamond ×ˢ Icc (k.val : ℝ) (k.val + 1)) (B k) := by
    intro x hx
    rw [hlocalValue k ⟨x, hx⟩]
    exact (C.map k _).property
  have hlocalPL (k : Fin (n + 3)) : FinitePiecewiseAffineOn sigma
      (signedTubeDiamond ×ˢ Icc (k.val : ℝ) (k.val + 1)) := by
    have hm := (signedTubePrismReparametrization_isFinitePL
      (SignedAxisPermutation.diamond_isFinitePL (C.jointPL 0) (frame k))
      (ht Fin.castSucc_lt_succ)).trans (hmapsPL k)
    obtain ⟨g, hg, hgval⟩ := hm
    have hh := hg.congr (fun x hx ↦
      (hgval ⟨x, hx⟩).symm.trans (hval k ⟨x, hx⟩).symm)
    simpa [t] using hh
  have hcoords (k : Fin (n + 3)) (j : Fin 2) (z : C3)
      (hz : z ∈ signedTubeDiamond ×ˢ Icc (k.val : ℝ) (k.val + 1)) :
      (C.chart k).chart (D.inverse (sigma z)) ((frame k).sheetPermutation j).castSucc = 0 ↔
        z.1 ∈ signedTubeSheet j := by
    rw [hlocalValue k ⟨z, hz⟩, ← C.sheets]
    exact (frame k).mem_sheet ⟨z.1, hz.1⟩ j
  have haxis (z : C3) (hz : z ∈ signedTubeDiamond ×ˢ Icc (0 : ℝ) (n + 3)) :
      sigma z ∈ D.axis.space ↔ z.1 = (0, 0) := by
    obtain ⟨k, hk⟩ := hpiece ⟨z, hz⟩
    have hz' : z ∈ signedTubeDiamond ×ˢ Icc (k.val : ℝ) (k.val + 1) := by
      simpa [t] using (show z ∈ signedTubeDiamond ×ˢ Icc (t k.castSucc) (t k.succ) from
        ⟨hz.1, hk⟩)
    rw [hlocalValue k ⟨z, hz'⟩, ← C.axis]
    exact (frame k).linear.map_eq_zero_iff
  have himage' : sigma '' (signedTubeDiamond ×ˢ Icc (0 : ℝ) (n + 3)) =
      (D.complex.barycentricNeighborhood D.axis).space := by
    apply Eq.trans _ hcover
    simpa only [htime.1, htime.2] using himage
  have haxisImage : (fun t : ℝ ↦ sigma ((0, 0), t)) '' Icc (0 : ℝ) (n + 3) =
      D.axis.space := by
    let : Fintype D.axis.faces := (D.complex_finite.subset D.axis_le).fintype
    ext z
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact (haxis _ ⟨signedTubeRadius_subset_diamond 0 false
        (left_mem_segment ℝ _ _), ht⟩).mpr rfl
    · intro hz
      have hzN := D.complex.space_subset_barycentricNeighborhood D.axis_le hz
      obtain ⟨x, hx, rfl⟩ := himage'.symm.subset hzN
      have hx0 := (haxis x hx).mp hz
      exact ⟨x.2, hx.2, congrArg sigma (Prod.ext hx0.symm rfl)⟩
  have hdisk (z : C3) (hz : z ∈ signedTubeDiamond ×ˢ Icc (0 : ℝ) (n + 3)) :
      sigma z ∈ D.sourceImage.space ↔ z.1 ∈ signedTubeSheet 0 ∪ signedTubeSheet 1 := by
    obtain ⟨k, hk⟩ := hpiece ⟨z, hz⟩
    have hz' : z ∈ signedTubeDiamond ×ˢ Icc (k.val : ℝ) (k.val + 1) := by
      simpa [t] using (show z ∈ signedTubeDiamond ×ˢ Icc (t k.castSucc) (t k.succ) from
        ⟨hz.1, hk⟩)
    have hv : p k ∈ D.axis.vertices := hpv ▸ mem_range_self k
    have hstar := D.vertex_dual_subset_star (p k) hv (hlocalMaps k hz')
    have hcomplex := space_subset_of_le
      (show D.complex.closedStar (p k) ≤ D.complex from fun _ ht ↦ ht.1) hstar
    rw [D.mem_sourceImage _ hcomplex, (C.chart k).source_image_iff _ (C.source k hstar)]
    have hregion : (D.inverse (sigma z) : X) ∈ R :=
      interior_subset (hcore (D.inverse (sigma z)).property)
    have h0 := hcoords k 0 z hz'
    have h1 := hcoords k 1 z hz'
    cases hs : (frame k).swap <;>
      simpa [SignedAxisPermutation.sheetPermutation, SignedAxisPermutation.index,
        jointSheetIndex, hs, Fin.rev, hregion, or_comm] using (or_congr h0 h1)
  refine ⟨frame, closing, sigma, hf0, hc, ?_, himage', hlocalPL, hlocalMaps,
    hlocalValue, hcoords, hdisk, haxis, haxisImage, ?_⟩
  · simpa only [htime.1, htime.2] using hPL
  · rw [htime.1, htime.2] at hfib
    exact hfib

end PoincareConjecture.M76.Dehn.Annuli

