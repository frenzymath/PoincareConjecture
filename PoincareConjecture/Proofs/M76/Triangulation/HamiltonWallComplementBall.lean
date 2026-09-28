import PoincareConjecture.Proofs.M76.Triangulation.HamiltonBrownBallRecognition

set_option autoImplicit false

open Set Metric

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

private theorem affine_halfspace_topology (ell : V3 →ᴬ[ℝ] ℝ)
    (hell : ell.toAffineMap.linear ≠ 0) :
    interior {x | 0 ≤ ell x} = {x | 0 < ell x} ∧
      closure (interior {x | 0 ≤ ell x}) = {x | 0 ≤ ell x} := by
  have hopen : IsOpenMap (ell : V3 → ℝ) := ell.toAffineMap.isOpenMap ell.continuous
    (ell.toAffineMap.linear_surjective_iff.mp (LinearMap.surjective hell))
  have hint : interior {x | 0 ≤ ell x} = {x | 0 < ell x} := by
    change interior ((ell : V3 → ℝ) ⁻¹' Ici 0) = (ell : V3 → ℝ) ⁻¹' Ioi 0
    rw [← hopen.preimage_interior_eq_interior_preimage ell.continuous, interior_Ici]
  refine ⟨hint, ?_⟩
  rw [hint]
  change closure ((ell : V3 → ℝ) ⁻¹' Ioi 0) = (ell : V3 → ℝ) ⁻¹' Ici 0
  rw [← hopen.preimage_closure_eq_closure_preimage ell.continuous, closure_Ioi]

private theorem affine_first_coordinate (ell : V3 →ᴬ[ℝ] ℝ)
    (hell : ell.toAffineMap.linear ≠ 0) :
    ∃ a : V3 ≃ᴬ[ℝ] V3, ∀ x, a x 0 = ell x := by
  exact exists_affine_first_coordinate ell hell

variable {X : Type*} [TopologicalSpace X] {ι : Type*}

theorem PLDomain.closure_interior {e : ι → OpenPartialHomeomorph X V3}
    {K : Set X} (hK : PLDomain e K) : closure (interior K) = K := by
  apply Subset.antisymm (closure_minimal interior_subset hK.closed)
  intro x hx
  by_cases hi : x ∈ interior K
  · exact subset_closure hi
  have hf : x ∈ frontier K := ⟨hK.closed.closure_eq.symm ▸ hx, hi⟩
  obtain ⟨ell, v, B, hv, hxB, _, _, hhalf⟩ := hK.halfspace x hf
  have hell : ell.toAffineMap.linear ≠ 0 := by
    intro hz
    have hv' : ell.toAffineMap.linear v = 1 := hv
    rw [hz] at hv'
    norm_num at hv'
  have himage : B.IsImage K {z | 0 ≤ ell z} := fun {y} hy => (hhalf y hy).symm
  apply (himage.interior.closure.apply_mem_iff hxB).mp
  rw [(affine_halfspace_topology ell hell).2]
  exact (hhalf x hxB).mp hx

variable [T2Space X] [CompactSpace X]

theorem PLDomain.brown_complement_ball_of_chart
    (brown : HasBrownLocallyFlatSphereBalls) {Y : Set X} (hY : IsOpen Y)
    {e : ι → OpenPartialHomeomorph Y V3} {K : Set Y}
    (hK : IsCompact K) (hKD : PLDomain e K)
    (s : ChartwisePLSphere e (frontier K))
    (c : OpenPartialHomeomorph X V3)
    (hc : (interior ((Subtype.val : Y → X) '' K))ᶜ ⊆ c.source) :
    IsUnitBallPair V3 (interior ((Subtype.val : Y → X) '' K))ᶜ
      ((Subtype.val : Y → X) '' frontier K) := by
  classical
  let x0 : sphere (0 : V3) 1 := ⟨fun _ => 1, by simp⟩
  let : Nonempty Y := ⟨(s.parametrization x0 : Y)⟩
  let j : OpenPartialHomeomorph Y X :=
    hY.isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph (Subtype.val : Y → X)
  have hjs : j.source = univ := rfl
  have hjt : j.target = Y := by simp [j]
  let KX : Set X := (Subtype.val : Y → X) '' K
  let D : Set X := (interior KX)ᶜ
  let S : Set X := (Subtype.val : Y → X) '' frontier K
  have hKX : IsCompact KX := hK.image continuous_subtype_val
  have hD : IsClosed D := isOpen_interior.isClosed_compl
  have hjK : j.IsImage K KX := by
    intro y _
    change (y : X) ∈ (Subtype.val : Y → X) '' K ↔ y ∈ K
    exact Subtype.val_injective.mem_set_image
  have hKXreg : closure (interior KX) = KX := by
    apply Subset.antisymm (closure_minimal interior_subset hKX.isClosed)
    rintro x ⟨y, hy, rfl⟩
    have hy' : y ∈ closure (interior K) := hKD.closure_interior.symm ▸ hy
    exact closure_mono (hY.isOpenMap_subtype_val.image_interior_subset K)
      (image_closure_subset_closure_image continuous_subtype_val ⟨y, hy', rfl⟩)
  have hfrontK : frontier KX = S := by
    ext x
    constructor
    · intro hx
      obtain ⟨y, hy, rfl⟩ := hKX.isClosed.frontier_subset hx
      exact ⟨y, (hjK.frontier.apply_mem_iff (hjs.symm ▸ mem_univ y)).mp hx, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact (hjK.frontier.apply_mem_iff (hjs.symm ▸ mem_univ y)).mpr hy
  have hfrontD : frontier D = S := by
    calc
      frontier D = frontier KX := by
        change frontier ((interior KX)ᶜ) = frontier KX
        rw [frontier_compl]
        simp only [frontier, hKXreg, interior_interior, hKX.isClosed.closure_eq]
      _ = S := hfrontK
  let T : Set V3 := c '' D
  have hT : IsCompact T := hD.isCompact.image_of_continuousOn (c.continuousOn.mono hc)
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
      exact (hcD.frontier.apply_mem_iff (hc (hD.frontier_subset hx))).mpr hx
  let jS : frontier K ≃ₜ S := j.homeomorphOfImageSubsetSource
    (by rw [hjs]; exact subset_univ _) rfl
  let cS : frontier D ≃ₜ frontier T := c.homeomorphOfImageSubsetSource
    (hD.frontier_subset.trans hc) hfrontT.symm
  let sT : sphere (0 : V3) 1 ≃ₜ frontier T :=
    ((s.parametrization.trans jS).trans (Homeomorph.setCongr hfrontD.symm)).trans cS
  have hhalfT : ∀ z ∈ frontier T,
      ∃ B : OpenPartialHomeomorph V3 V3, z ∈ B.source ∧
        B z 0 = 0 ∧ ∀ w ∈ B.source, w ∈ T ↔ 0 ≤ B w 0 := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := hfrontT.subset hz
    obtain ⟨y, hy, rfl⟩ := hfrontD.subset hx
    obtain ⟨ell, v, B, hv, hyB, hzero, _, hhalf⟩ := hKD.halfspace y hy
    have hell : ell.toAffineMap.linear ≠ 0 := by
      intro hz
      have hv' : ell.toAffineMap.linear v = 1 := hv
      rw [hz] at hv'
      norm_num at hv'
    have hneg : (-ell).toAffineMap.linear ≠ 0 := by
      intro hz
      apply hell
      apply LinearMap.ext
      intro u
      have hu := congrArg (fun f : V3 →ₗ[ℝ] ℝ => f u) hz
      change -(ell.toAffineMap.linear u) = 0 at hu
      exact neg_eq_zero.mp hu
    obtain ⟨a, ha⟩ := affine_first_coordinate (-ell) hneg
    let F := j.trans c
    let B' := (F.symm.trans B).transHomeomorph a.toHomeomorph
    have hyD : (y : X) ∈ D := hD.frontier_subset hx
    have hyF : y ∈ F.source := by
      refine ⟨?_, hc hyD⟩
      change y ∈ j.source
      rw [hjs]
      exact mem_univ y
    have hyB' : c (y : X) ∈ B'.source := by
      change F y ∈ F.target ∧ F.symm (F y) ∈ B.source
      exact ⟨F.map_source hyF, by rw [F.left_inv hyF]; exact hyB⟩
    refine ⟨B', hyB', ?_, ?_⟩
    · change a (B (F.symm (F y))) 0 = 0
      rw [F.left_inv hyF, ha]
      change -ell (B y) = 0
      rw [hzero, neg_zero]
    · intro w hw
      have hwF : w ∈ F.target := hw.1
      have hwB : F.symm w ∈ B.source := hw.2
      have hwc : w ∈ c.target := hwF.1
      have hwj : c.symm w ∈ j.target := hwF.2
      have hjval : (F.symm w : X) = c.symm w := j.right_inv hwj
      have hBF : B.IsImage K {u | 0 ≤ ell u} := fun {u} hu => (hhalf u hu).symm
      have hBi : B.IsImage (interior K) {u | 0 < ell u} := by
        simpa only [(affine_halfspace_topology ell hell).1] using hBF.interior
      have hwi : c.symm w ∈ interior KX ↔ F.symm w ∈ interior K := by
        rw [← hjval]
        exact hjK.interior.apply_mem_iff (hjs.symm ▸ mem_univ _)
      change w ∈ T ↔ 0 ≤ a (B (F.symm w)) 0
      rw [ha]
      change w ∈ T ↔ 0 ≤ -ell (B (F.symm w))
      rw [neg_nonneg]
      calc
        w ∈ T ↔ c.symm w ∈ D := (hcD.symm_apply_mem_iff hwc).symm
        _ ↔ ¬ F.symm w ∈ interior K := not_congr hwi
        _ ↔ ¬ 0 < ell (B (F.symm w)) := not_congr (hBi.apply_mem_iff hwB).symm
        _ ↔ ell (B (F.symm w)) ≤ 0 := not_lt
  have hpair := exists_brown_ball_pair_of_compact_halfspace_domain brown hT sT hhalfT
  apply hpair.of_homeomorph (show S ⊆ D from by
    rw [← hfrontD]
    exact hD.frontier_subset)
    (c.homeomorphOfImageSubsetSource hc rfl)
  intro x
  change (x : X) ∈ S ↔ c (x : X) ∈ frontier T
  rw [← hfrontD]
  exact (hcD.frontier.apply_mem_iff (hc x.property)).symm

end PoincareConjecture.M76
