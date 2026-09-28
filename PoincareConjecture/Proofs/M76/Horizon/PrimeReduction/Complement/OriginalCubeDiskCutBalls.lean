import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Complement.ProperProductBoundaryDisks
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Complement.FinitePLBallProperDiskCut
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Complement.SimplyConnectedDiskCut
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Complement.TwoComponentBoundaryPieces
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Complement.CompactSphereBoundaryRecognition










set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)
local notation "P3" => ((ℝ × ℝ) × ℝ)
local notation "Disk" => closedBall (0 : V2) 1
local notation "Rim" => sphere (0 : V2) 1
local notation "Cube" => closedBall (0 : V3) 1
local notation "Sphere" => sphere (0 : V3) 1
local notation "I" => Icc (-1 : ℝ) 1
local notation "Half" => Icc (-(1 / 2) : ℝ) (1 / 2)
local notation "atlas" => (fun _ : Unit => OpenPartialHomeomorph.refl V3)



theorem _root_.Set.IsFinitePLBallPair.three_coordinate_model
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    {D B : Set X} (h : IsFinitePLBallPair E D B) (hdim : Module.finrank ℝ E = 3) :
    IsFinitePLBallPair V3 D B := by
  let coord : E ≃L[ℝ] V3 := ContinuousLinearEquiv.ofFinrankEq (by simpa using hdim)
  obtain ⟨e, he, heb⟩ := h.exists_cube_chart coord
  exact ⟨h.1, Cube, isCompact_closedBall _ _, convex_closedBall _ _,
    ⟨0, ball_subset_interior_closedBall (mem_ball_self zero_lt_one)⟩, e, he, heb⟩

private theorem disk_pair_two_coordinates : IsFinitePLBallPair P2 Disk Rim := by
  have hS := _root_.Dehn.isFinitePLBallPair_annulusSquare
    (L := 8) (u := 0) (by norm_num)
  obtain ⟨e, he, heb⟩ := hS.exists_cube_chart (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm
  apply hS.of_homeomorph sphere_subset_closedBall e.symm he.symm
  intro x
  have h := heb (e.symm x)
  rw [e.apply_symm_apply, frontier_closedBall _ one_ne_zero] at h
  exact h.symm

theorem OriginalDiskProduct.exists_two_cube_cut_balls
    {j : V2 → V3} (P : OriginalDiskProduct atlas Cube j)
    (hopen : IsOpen ((Subtype.val : Cube → V3) ⁻¹' P.openStrip))
    (hPL : PLDomain atlas P.cutCarrier) :
    ∃ (C k : Bool → Set V3) (a : Bool → V3),
      (∀ b, a b ∈ P.cutCarrier ∧ C b = connectedComponentIn P.cutCarrier (a b)) ∧
      (∀ b, IsFinitePLBallPair P3 (C b) (frontier (C b)) ∧
        IsCompact (C b) ∧ PLDomain atlas (C b) ∧ IsConnected (C b)) ∧
      P.cutCarrier = C false ∪ C true ∧ Disjoint (C false) (C true) ∧
      (∀ b, IsFinitePLBallPair P2 (k b) (P.capRimSet b) ∧
        k b ⊆ Sphere ∧ k b ⊆ C b ∧
        frontier (C b) = k b ∪ P.capDisk b ∧ k b ∩ P.capDisk b = P.capRimSet b ∧
        P.capDisk b ⊆ C b ∧ Disjoint (C b) (P.capDisk (!b)) ∧
        C b ∩ P.closedStrip = P.capDisk b ∧ C b ⊆ Cube) ∧
      P.closedStrip ∪ (C false ∪ C true) = Cube := by
  classical
  have hproper (z : V2 × ℝ) (hz : z ∈ Disk ×ˢ I) :
      P.map z ∈ Sphere ↔ z.1 ∈ Rim := by
    simpa only [frontier_closedBall _ one_ne_zero] using P.proper z hz
  obtain ⟨k, hk, _, hkwhole⟩ :=
    exists_proper_product_boundary_disks P.map P.finitePiecewiseAffineOn_standard
      P.injective hproper
  let band := P.map '' (Rim ×ˢ Half)
  have hkb (b : Bool) : IsFinitePLBallPair P2 (k b) (P.capRimSet b) := (hk b).1
  have hks (b : Bool) : k b ⊆ Sphere := (hk b).2.1
  have hkband (b : Bool) : k b ∩ band = P.capRimSet b := (hk b).2.2
  have hrimfull (b : Bool) :
      Rim ×ˢ {if b then (1 / 2 : ℝ) else -(1 / 2)} ⊆ Disk ×ˢ I :=
    (prod_mono sphere_subset_closedBall subset_rfl).trans (OriginalDiskProduct.cap_source_subset b)
  have hopenfull (z : V2 × ℝ) (hz : z ∈ Disk ×ˢ Ioo (-(1 / 2) : ℝ) (1 / 2)) :
      z ∈ Disk ×ˢ I :=
    ⟨hz.1, by constructor <;> linarith [hz.2.1, hz.2.2]⟩
  have hkrim (b : Bool) : k b ∩ P.capDisk b = P.capRimSet b := by
    apply Subset.antisymm
    · rintro x ⟨hxk, z, hz, rfl⟩
      have hzrim := (hproper z (OriginalDiskProduct.cap_source_subset b hz)).mp (hks b hxk)
      exact ⟨z, ⟨hzrim, hz.2⟩, rfl⟩
    · intro x hx
      exact ⟨(hkb b).1 hx, P.capRimSet_subset_capDisk b hx⟩
  have hkmiss (b : Bool) : Disjoint (k b) P.openStrip := by
    apply disjoint_left.mpr
    rintro x hxk ⟨z, hz, rfl⟩
    have hzrim := (hproper z (hopenfull z hz)).mp (hks b hxk)
    have hxband : P.map z ∈ band :=
      ⟨z, ⟨hzrim, hz.2.1.le, hz.2.2.le⟩, rfl⟩
    obtain ⟨w, hw, heq⟩ := (hkband b).subset ⟨hxk, hxband⟩
    have hzw := P.injective (hrimfull b hw) (hopenfull z hz) heq
    have ht : w.2 = if b then (1 / 2 : ℝ) else -(1 / 2) := hw.2
    have ht' := congrArg Prod.snd hzw
    cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] at ht <;>
      linarith [hz.2.1, hz.2.2]
  have hold : Sphere \ P.openStrip = k false ∪ k true := by
    apply Subset.antisymm
    · intro x hx
      rcases hkwhole.symm.subset hx.1 with hkside | hxband
      · exact hkside.symm
      · obtain ⟨z, hz, rfl⟩ := hxband
        have ht : z.2 = -(1 / 2 : ℝ) ∨ z.2 = 1 / 2 := by
          by_contra hn
          push Not at hn
          exact hx.2 ⟨z, ⟨sphere_subset_closedBall hz.1,
            lt_of_le_of_ne hz.2.1 hn.1.symm, lt_of_le_of_ne hz.2.2 hn.2⟩, rfl⟩
        rcases ht with ht | ht
        · exact Or.inl ((hkb false).1 ⟨z, ⟨hz.1, ht⟩, rfl⟩)
        · exact Or.inr ((hkb true).1 ⟨z, ⟨hz.1, ht⟩, rfl⟩)
    · rintro x (hx | hx)
      · exact ⟨hks false hx, fun hu => disjoint_left.mp (hkmiss false) hx hu⟩
      · exact ⟨hks true hx, fun hu => disjoint_left.mp (hkmiss true) hx hu⟩
  have hcapball (b : Bool) : IsFinitePLBallPair P2 (P.capDisk b) (P.capRimSet b) :=
    (disk_pair_two_coordinates.prod_singleton
      (if b then (1 / 2 : ℝ) else -(1 / 2))).image_of_subset
      P.finitePiecewiseAffineOn_standard (OriginalDiskProduct.cap_source_subset b) P.injective
  obtain ⟨hc, _, hf, _, _, _⟩ := P.cut_geometry (isCompact_closedBall _ _) hopen
  have hfront : frontier P.cutCarrier =
      (k false ∪ P.capDisk false) ∪ (k true ∪ P.capDisk true) := by
    rw [hf, frontier_closedBall _ one_ne_zero, hold, P.endDisks_eq_capDisks]
    ac_rfl
  obtain ⟨a, ha, _, _, _, _, hcover, hdis, hcap, hmiss, hstrip, hwhole⟩ :=
    P.exists_two_components_of_disconnected_cut (isCompact_closedBall _ _)
      (isConnected_closedBall (x := (0 : V3)) zero_le_one) hopen hPL
      (P.not_isConnected_cut_of_cube hopen hPL)
  let C := fun b => connectedComponentIn P.cutCarrier (a b)
  have hpieces := two_component_frontiers_of_marked_rims hc hPL a ha C k
    P.capDisk P.capRimSet (fun _ => rfl) hdis
    (fun b => (hkb b).isConnected.isPreconnected) hcap hkrim
    (fun b => ⟨P.map (1, if b then (1 / 2 : ℝ) else -(1 / 2)),
      ⟨(1, if b then (1 / 2 : ℝ) else -(1 / 2)), ⟨by simp, rfl⟩, rfl⟩⟩) hfront
  refine ⟨C, k, a, fun b => ⟨ha b, rfl⟩, ?_, hcover, hdis, ?_, ?_⟩
  · intro b
    obtain ⟨hCc, hCP, hCc', _, hCf⟩ := hpieces b
    have hball := finitePLBallPair_of_compact_plDomain_two_disk_frontier
      (by simp : Module.finrank ℝ V3 = 3) hCc hCP (hkb b) (hcapball b) (hkrim b) hCf
    exact ⟨hCf.symm ▸ hball, hCc, hCP, hCc'⟩
  · intro b
    exact ⟨hkb b, hks b, (hpieces b).2.2.2.1, (hpieces b).2.2.2.2,
      hkrim b, hcap b, hmiss b, hstrip b,
      (connectedComponentIn_subset _ _).trans sdiff_subset⟩
  · rw [← hcover]
    exact hwhole

end PoincareConjecture.M76
