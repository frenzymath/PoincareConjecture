import PoincareConjecture.Proofs.M76.Triangulation.HamiltonBrownBoundaryChart
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonLowerMissingSide










set_option autoImplicit false

open Set Metric

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

private theorem relative_cap_first_coordinate (ell : V3 →ᴬ[ℝ] ℝ)
    (hell : ell.toAffineMap.linear ≠ 0) :
    ∃ a : V3 ≃ᴬ[ℝ] V3, ∀ x, a x 0 = ell x := by
  exact exists_affine_first_coordinate ell hell

variable {X α : Type*} [TopologicalSpace X] [T2Space X]
  {U : TopologicalSpace.Opens X} {H : Set X}
  {e : α → OpenPartialHomeomorph U V3} {K S : Set U}

local notation "R" => ((Subtype.val : U → X) ⁻¹' H)





theorem PLDomain.brown_relative_wall_complement
    (brown : HasBrownLocallyFlatSphereBalls)
    (hH : IsCompact H) (hHU : frontier H ⊆ (U : Set X))
    (hK : IsCompact K) (hKD : PLDomain e K)
    (hS : S ⊆ interior R) (hfront : frontier K = frontier R ∪ S)
    (hretain : (Subtype.val : R → U) ⁻¹' frontier R ⊆
      interior ((Subtype.val : R → U) ⁻¹' K))
    (s : ChartwisePLSphere e S) (c : OpenPartialHomeomorph X V3)
    (hc : H \ ((Subtype.val : U → X) '' ((Subtype.val : R → U) ''
      interior ((Subtype.val : R → U) ⁻¹' K))) ⊆ c.source) :
    IsUnitBallPair V3
      (H \ ((Subtype.val : U → X) '' ((Subtype.val : R → U) ''
        interior ((Subtype.val : R → U) ⁻¹' K))))
      ((Subtype.val : U → X) '' S) := by
  classical
  let D := H \ ((Subtype.val : U → X) '' ((Subtype.val : R → U) ''
    interior ((Subtype.val : R → U) ⁻¹' K)))
  let SX := (Subtype.val : U → X) '' S
  let x0 : sphere (0 : V3) 1 := ⟨fun _ => 1, by simp⟩
  let : Nonempty U := ⟨(s.parametrization x0 : U)⟩
  obtain ⟨hD, _, hfrontD, hDlocal⟩ :=
    PLDomain.relative_wall_missing_side hH hHU hK hKD hS hfront hretain
  have hfrontD' : frontier D = SX := hfrontD
  let j : OpenPartialHomeomorph U X :=
    U.isOpen.isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph (Subtype.val : U → X)
  have hjs : j.source = univ := rfl
  let T : Set V3 := c '' D
  have hT : IsCompact T := hD.image_of_continuousOn (c.continuousOn.mono hc)
  have hcD : c.IsImage D T := by
    intro x hx
    constructor
    · rintro ⟨y, hy, heq⟩
      exact (c.injOn (hc hy) hx heq) ▸ hy
    · intro hxD
      exact mem_image_of_mem c hxD
  have hfrontT : frontier T = c '' frontier D := by
    ext z
    constructor
    · intro hz
      obtain ⟨x, hx, rfl⟩ := hT.isClosed.frontier_subset hz
      exact ⟨x, (hcD.frontier.apply_mem_iff (hc hx)).mp hz, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact (hcD.frontier.apply_mem_iff (hc (hD.isClosed.frontier_subset hx))).mpr hx
  let jS : S ≃ₜ SX := j.homeomorphOfImageSubsetSource
    (by rw [hjs]; exact subset_univ _) rfl
  let cS : frontier D ≃ₜ frontier T := c.homeomorphOfImageSubsetSource
    (hD.isClosed.frontier_subset.trans hc) hfrontT.symm
  let sT : sphere (0 : V3) 1 ≃ₜ frontier T :=
    ((s.parametrization.trans jS).trans (Homeomorph.setCongr hfrontD.symm)).trans cS
  have hhalfT : ∀ z ∈ frontier T,
      ∃ B : OpenPartialHomeomorph V3 V3, z ∈ B.source ∧
        B z 0 = 0 ∧ ∀ w ∈ B.source, w ∈ T ↔ 0 ≤ B w 0 := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := hfrontT.subset hz
    obtain ⟨y, hy, rfl⟩ := hfrontD.subset hx
    have hyf : y ∈ frontier K := hfront.symm ▸ Or.inr hy
    obtain ⟨ell, v, B0, hv, hyB0, hzero, _, hhalf⟩ := hKD.halfspace y hyf
    let B := B0.restrOpen (interior R) isOpen_interior
    have hyB : y ∈ B.source := ⟨hyB0, hS hy⟩
    have hell : ell.toAffineMap.linear ≠ 0 := by
      intro hlin
      have hv' : ell.toAffineMap.linear v = 1 := hv
      rw [hlin] at hv'
      norm_num at hv'
    have hneg : (-ell).toAffineMap.linear ≠ 0 := by
      intro hlin
      apply hell
      apply LinearMap.ext
      intro u
      have hu := congrArg (fun f : V3 →ₗ[ℝ] ℝ => f u) hlin
      change -(ell.toAffineMap.linear u) = 0 at hu
      exact neg_eq_zero.mp hu
    obtain ⟨a, ha⟩ := relative_cap_first_coordinate (-ell) hneg
    let F := j.trans c
    let B' := (F.symm.trans B).transHomeomorph a.toHomeomorph
    have hyD : (y : X) ∈ D := hD.isClosed.frontier_subset hx
    have hyF : y ∈ F.source :=
      ⟨(show y ∈ j.source by rw [hjs]; exact mem_univ _), hc hyD⟩
    have hyB' : c (y : X) ∈ B'.source := by
      change F y ∈ F.target ∧ F.symm (F y) ∈ B.source
      exact ⟨F.map_source hyF, by rw [F.left_inv hyF]; exact hyB⟩
    refine ⟨B', hyB', ?_, ?_⟩
    · change a (B (F.symm (F y))) 0 = 0
      rw [F.left_inv hyF, ha]
      change -ell (B0 y) = 0
      rw [hzero, neg_zero]
    · intro w hw
      have hwF : w ∈ F.target := hw.1
      have hwB : F.symm w ∈ B.source := hw.2
      have hwc : w ∈ c.target := hwF.1
      have hwj : c.symm w ∈ j.target := hwF.2
      have hjval : (F.symm w : X) = c.symm w := j.right_inv hwj
      have hBF : B.IsImage K {u | 0 ≤ ell u} := by
        intro u hu
        exact (hhalf u hu.1).symm
      have hopen : IsOpenMap (ell : V3 → ℝ) :=
        ell.toAffineMap.isOpenMap ell.continuous
          (ell.toAffineMap.linear_surjective_iff.mp (LinearMap.surjective hell))
      have hint : interior {u | 0 ≤ ell u} = {u | 0 < ell u} := by
        change interior ((ell : V3 → ℝ) ⁻¹' Ici 0) = (ell : V3 → ℝ) ⁻¹' Ioi 0
        rw [← hopen.preimage_interior_eq_interior_preimage ell.continuous, interior_Ici]
      have hBi : B.IsImage (interior K) {u | 0 < ell u} := by
        simpa only [hint] using hBF.interior
      change w ∈ T ↔ 0 ≤ a (B (F.symm w)) 0
      rw [ha]
      change w ∈ T ↔ 0 ≤ -ell (B (F.symm w))
      rw [neg_nonneg]
      calc
        w ∈ T ↔ c.symm w ∈ D := (hcD.symm_apply_mem_iff hwc).symm
        _ ↔ (F.symm w : X) ∈ D := by rw [hjval]
        _ ↔ F.symm w ∉ interior K := hDlocal _ hwB.2
        _ ↔ ¬ 0 < ell (B (F.symm w)) := not_congr (hBi.apply_mem_iff hwB).symm
        _ ↔ ell (B (F.symm w)) ≤ 0 := not_lt
  have hpair := exists_brown_ball_pair_of_compact_halfspace_domain brown hT sT hhalfT
  apply hpair.of_homeomorph (show SX ⊆ D from by
    rw [← hfrontD']
    exact hD.isClosed.frontier_subset)
    (c.homeomorphOfImageSubsetSource hc rfl)
  intro x
  change (x : X) ∈ SX ↔ c (x : X) ∈ frontier T
  rw [← hfrontD']
  exact (hcD.frontier.apply_mem_iff (hc x.property)).symm

end PoincareConjecture.M76
