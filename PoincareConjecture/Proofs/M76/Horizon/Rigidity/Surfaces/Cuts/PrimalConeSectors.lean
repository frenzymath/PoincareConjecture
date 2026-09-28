import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Surfaces.Cuts.PrimalDiskSectors
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Surfaces.Cuts.SingleTriangle
import PoincareConjecture.Proofs.M76.Mathlib.AlexanderBaseConeBall

set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76.OriginalTriangleCopies

open Dehn.Annuli TriangleDiskModel

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem interval_cone_isFinitePLBallPair {s : Set E} {a b : E}
    (hs : IsFinitePLBallPair ℝ s {a, b}) (L : E →ₗ[ℝ] ℝ)
    (hL : ∀ x ∈ s, L x = 1) :
    IsFinitePLBallPair (ℝ × ℝ) (convexJoin ℝ {0} s)
      (s ∪ convexJoin ℝ {0} ({a, b} : Set E)) := by
  let u : ℝ × ℝ := (1, 0)
  let v : ℝ × ℝ := (0, 1)
  have huv : u ≠ v := by simp [u, v]
  have hbase : IsFinitePLBallPair ℝ (segment ℝ u v) {u, v} := by
    simpa only [ContinuousAffineMap.coe_lineMap_eq, AffineMap.lineMap_apply_zero,
      AffineMap.lineMap_apply_one, ← segment_eq_image_lineMap] using
      isFinitePLBallPair_affine_interval zero_lt_one (ContinuousAffineMap.lineMap u v)
        (AffineMap.lineMap_injective ℝ huv).injOn
  have hpair : convexJoin ℝ {(0 : ℝ × ℝ)} ({u, v} : Set (ℝ × ℝ)) =
      segment ℝ 0 u ∪ segment ℝ 0 v := by simp [convexJoin_singleton_left]
  have hrange : range rightTriangle = ({0, u, v} : Set (ℝ × ℝ)) := by
    ext x
    simp [rightTriangle, u, v, Prod.zero_eq_mk, or_comm, or_left_comm]
  have hmodel : IsFinitePLBallPair (ℝ × ℝ) (convexJoin ℝ {0} (segment ℝ u v))
      (segment ℝ u v ∪ convexJoin ℝ {0} ({u, v} : Set (ℝ × ℝ))) := by
    have ht := isFinitePLBallPair_triangleRim rightTriangle independent_rightTriangle
    rw [hrange] at ht
    rw [convexJoin_singleton_segment, hpair]
    convert ht using 1
    ext x
    change (x ∈ segment ℝ u v ∨ x ∈ segment ℝ 0 u ∨ x ∈ segment ℝ 0 v) ↔
      (x ∈ segment ℝ 0 u ∨ x ∈ segment ℝ u v) ∨ x ∈ segment ℝ v 0
    rw [segment_symm ℝ v 0]
    tauto
  obtain ⟨e, he, heb⟩ := hs.exists_homeomorph hbase
  let M : (ℝ × ℝ) →ₗ[ℝ] ℝ := LinearMap.fst ℝ ℝ ℝ + LinearMap.snd ℝ ℝ ℝ
  have hM (x : ℝ × ℝ) (hx : x ∈ segment ℝ u v) : M x = 1 := by
    rw [segment_eq_image_lineMap] at hx
    obtain ⟨r, hr, rfl⟩ := hx
    simp [M, u, v, AffineMap.lineMap_apply_module]
  have hne : s.Nonempty := ⟨a, hs.1 (by simp)⟩
  obtain ⟨H, hH, hHr⟩ := he.exists_radial_cone_extension hne L M hL hM
  have hbd : s ∪ convexJoin ℝ {0} ({a, b} : Set E) ⊆ convexJoin ℝ {0} s :=
    union_subset (subset_convexJoin_right (singleton_nonempty 0))
      (convexJoin_mono_right hs.1)
  apply hmodel.of_homeomorph hbd H hH
  intro x
  obtain ⟨y, hy, r, hr, hxy⟩ := (mem_convexJoin_zero_iff s _).mp x.property
  have hvalue : (H x : ℝ × ℝ) = r • (e ⟨y, hy⟩ : ℝ × ℝ) := by
    have hx : x = ⟨r • y, (mem_convexJoin_zero_iff s _).mpr ⟨y, hy, r, hr, rfl⟩⟩ :=
      Subtype.ext hxy
    rw [hx]
    exact hHr ⟨y, hy⟩ r hr
  rw [hvalue, hxy, L.mem_base_union_convexJoin_iff hs.1 (by simp) hL hy hr,
    M.mem_base_union_convexJoin_iff hbase.1 (by simp) hM (e ⟨y, hy⟩).property hr,
    heb ⟨y, hy⟩]

theorem capSector_isFinitePLBallPair {A : Set E} {a b : E}
    (hA : IsFinitePLBallPair ℝ A {a, b}) :
    IsFinitePLBallPair (ℝ × ℝ) (boundaryCircleCap true A)
      ((A ×ˢ {(0 : ℝ)}) ∪ boundaryCircleCap true ({a, b} : Set E)) := by
  have hlift := hA.affine_image (circleLevelLift : E →ᴬ[ℝ] E × ℝ)
    (fun x _ y _ h ↦ congrArg Prod.fst h)
  have hlevel (x : E × ℝ) (hx : x ∈ circleLevelLift '' A) :
      (LinearMap.snd ℝ E ℝ) x = 1 := by
    obtain ⟨y, hy, rfl⟩ := hx
    rfl
  rw [image_pair] at hlift
  have hcone := interval_cone_isFinitePLBallPair hlift (LinearMap.snd ℝ E ℝ) hlevel
  have hcap := hcone.affine_image (capRebase true) (capRebase_injective true).injOn
  have hbase : capRebase true '' (circleLevelLift '' A) = A ×ˢ {(0 : ℝ)} := by
    ext x
    constructor
    · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      exact ⟨hy, by simp [capRebase, capSign, circleLevelLift]⟩
    · rintro ⟨hx, hx0⟩
      refine ⟨circleLevelLift x.1, mem_image_of_mem _ hx, ?_⟩
      apply Prod.ext
      · rfl
      · simpa [capRebase, capSign, circleLevelLift] using hx0.symm
  simpa only [boundaryCircleCap, boundaryCircleCone, image_union, hbase, image_pair] using hcap

omit [FiniteDimensional ℝ E] in
theorem mem_capSector_iff (A : Set E) (z : E × ℝ) :
    z ∈ boundaryCircleCap true A ↔
      ∃ a ∈ A, ∃ t ∈ Icc (0 : ℝ) 1, z = capSpoke a t := by
  simp only [mem_boundaryCircleCap_iff, capSign, if_true, one_mul, capSpoke_apply]

omit [FiniteDimensional ℝ E] in
theorem capSector_union (A B : Set E) :
    boundaryCircleCap true (A ∪ B) = boundaryCircleCap true A ∪ boundaryCircleCap true B := by
  ext z
  simp only [mem_capSector_iff, mem_union]
  constructor
  · rintro ⟨a, ha | ha, t, ht, hzt⟩
    · exact Or.inl ⟨a, ha, t, ht, hzt⟩
    · exact Or.inr ⟨a, ha, t, ht, hzt⟩
  · rintro (⟨a, ha, t, ht, hzt⟩ | ⟨a, ha, t, ht, hzt⟩)
    · exact ⟨a, Or.inl ha, t, ht, hzt⟩
    · exact ⟨a, Or.inr ha, t, ht, hzt⟩

omit [FiniteDimensional ℝ E] in
theorem capSector_singleton (a : E) :
    boundaryCircleCap true ({a} : Set E) = capSpoke a '' Icc (0 : ℝ) 1 := by
  ext z
  simp only [mem_capSector_iff, mem_singleton_iff, exists_eq_left, mem_image]
  exact exists_congr fun t ↦ and_congr_right fun _ ↦ eq_comm

omit [FiniteDimensional ℝ E] in
theorem capSector_inter (A B : Set E) (hA : A.Nonempty) (hB : B.Nonempty) :
    boundaryCircleCap true A ∩ boundaryCircleCap true B =
      {(0, 1)} ∪ boundaryCircleCap true (A ∩ B) := by
  apply Subset.antisymm
  · intro z hz
    obtain ⟨a, ha, u, hu, hzu⟩ := (mem_capSector_iff A z).mp hz.1
    obtain ⟨b, hb, v, hv, hzv⟩ := (mem_capSector_iff B z).mp hz.2
    obtain ⟨huv, hzero | hab⟩ := (capSpoke_fibers a b u v).mp (hzu.symm.trans hzv)
    · left
      simpa only [mem_singleton_iff, hzero, capSpoke_apply, zero_smul, sub_zero] using hzu
    · right
      exact (mem_capSector_iff (A ∩ B) z).mpr ⟨a, ⟨ha, hab.symm ▸ hb⟩, u, hu, hzu⟩
  · intro z hz
    rcases hz with hz | hz
    · have hz' : z = (0, 1) := hz
      obtain ⟨a, ha⟩ := hA
      obtain ⟨b, hb⟩ := hB
      exact ⟨(mem_capSector_iff A z).mpr ⟨a, ha, 0, by simp, by simp [hz']⟩,
        (mem_capSector_iff B z).mpr ⟨b, hb, 0, by simp, by simp [hz']⟩⟩
    · obtain ⟨a, ha, t, ht, hzt⟩ := (mem_capSector_iff (A ∩ B) z).mp hz
      exact ⟨(mem_capSector_iff A z).mpr ⟨a, ha.1, t, ht, hzt⟩,
        (mem_capSector_iff B z).mpr ⟨a, ha.2, t, ht, hzt⟩⟩

omit [FiniteDimensional ℝ E] in
theorem capSector_inter_of_singleton {A B : Set E} {a : E} (h : A ∩ B = {a}) :
    boundaryCircleCap true A ∩ boundaryCircleCap true B =
      capSpoke a '' Icc (0 : ℝ) 1 := by
  have ha : a ∈ A ∩ B := h.symm ▸ (mem_singleton a)
  rw [capSector_inter A B ⟨a, ha.1⟩ ⟨a, ha.2⟩, h, capSector_singleton]
  apply union_eq_right.mpr
  rintro z rfl
  exact ⟨0, by simp, by simp⟩

omit [FiniteDimensional ℝ E] in
theorem capSector_inter_of_disjoint {A B : Set E} (hA : A.Nonempty) (hB : B.Nonempty)
    (h : Disjoint A B) :
    boundaryCircleCap true A ∩ boundaryCircleCap true B = {(0, 1)} := by
  rw [capSector_inter A B hA hB, h.inter_eq]
  have he : boundaryCircleCap true (∅ : Set E) = ∅ := by
    ext z
    simp [mem_capSector_iff]
  rw [he, union_empty]

theorem capSector_isFinitePLBallPair_spokes {A : Set E} {a b : E}
    (hA : IsFinitePLBallPair ℝ A {a, b}) :
    IsFinitePLBallPair (ℝ × ℝ) (boundaryCircleCap true A)
      ((A ×ˢ {(0 : ℝ)}) ∪
        (capSpoke a '' Icc (0 : ℝ) 1 ∪ capSpoke b '' Icc (0 : ℝ) 1)) := by
  have hp : ({a, b} : Set E) = {a} ∪ {b} := by ext z; simp [or_comm]
  have h := capSector_isFinitePLBallPair hA
  rwa [hp, capSector_union, capSector_singleton, capSector_singleton] at h

theorem exists_four_prescribed_cap_sectors
    {d q : Set E} (hd : IsFinitePLBallPair (ℝ × ℝ) d q)
    (marks : Fin 4 → E) (hm : Function.Injective marks) (hq : ∀ i, marks i ∈ q) :
    ∃ (σ : Fin 4 ≃ Fin 4) (A B C D : Set E),
      IsFinitePLBallPair ℝ A {marks (σ 0), marks (σ 1)} ∧
      IsFinitePLBallPair ℝ B {marks (σ 1), marks (σ 2)} ∧
      IsFinitePLBallPair ℝ C {marks (σ 2), marks (σ 3)} ∧
      IsFinitePLBallPair ℝ D {marks (σ 3), marks (σ 0)} ∧
      (A ∪ B) ∪ (C ∪ D) = q ∧
      (boundaryCircleCap true A ∪ boundaryCircleCap true B) ∪
        (boundaryCircleCap true C ∪ boundaryCircleCap true D) = boundaryCircleCap true q ∧
      boundaryCircleCap true A ∩ boundaryCircleCap true B = capSpoke (marks (σ 1)) '' Icc (0 : ℝ) 1 ∧
      boundaryCircleCap true B ∩ boundaryCircleCap true C = capSpoke (marks (σ 2)) '' Icc (0 : ℝ) 1 ∧
      boundaryCircleCap true C ∩ boundaryCircleCap true D = capSpoke (marks (σ 3)) '' Icc (0 : ℝ) 1 ∧
      boundaryCircleCap true D ∩ boundaryCircleCap true A = capSpoke (marks (σ 0)) '' Icc (0 : ℝ) 1 ∧
      boundaryCircleCap true A ∩ boundaryCircleCap true C = {(0, 1)} ∧
      boundaryCircleCap true B ∩ boundaryCircleCap true D = {(0, 1)} := by
  obtain ⟨σ, A, B, C, D, hA, hB, hC, hD, hcover, hAB, hBC, hCD, hDA, hAC, hBD⟩ :=
    exists_four_prescribed_rim_arcs hd marks hm hq
  refine ⟨σ, A, B, C, D, hA, hB, hC, hD, hcover, ?_,
    capSector_inter_of_singleton hAB, capSector_inter_of_singleton hBC,
    capSector_inter_of_singleton hCD, capSector_inter_of_singleton hDA,
    capSector_inter_of_disjoint ⟨marks (σ 0), hA.1 (by simp)⟩
      ⟨marks (σ 2), hC.1 (by simp)⟩ hAC,
    capSector_inter_of_disjoint ⟨marks (σ 1), hB.1 (by simp)⟩
      ⟨marks (σ 3), hD.1 (by simp)⟩ hBD⟩
  rw [← capSector_union, ← capSector_union, ← capSector_union, hcover]

end PoincareConjecture.M76.OriginalTriangleCopies
