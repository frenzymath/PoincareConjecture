import PoincareConjecture.Proofs.M76.Triangulation.HamiltonZeroLatticeBrownCap
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonCappedAtlas










set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "W" => LatticeHandleAmbient (Fin 0) (Fin 3) hamiltonZeroPeriodLattice
local notation "Y" => ((Set.singleton hamiltonZeroHandlePuncture)ᶜ : Set W)
local notation "V3" => (Fin 3 → ℝ)





theorem exists_zero_lattice_capped_PL_domain
    (h : OpenPartialHomeomorph CubeShell.Ambient V3) (hsource : h.source = univ)
    (wall : ∀ e : Y → OpenPartialHomeomorph Y V3, HasWallCompactCore e)
    (brown : HasBrownLocallyFlatSphereBalls) :
    ∃ (d : ((Fin 0 → ℝ) × V3) → OpenPartialHomeomorph W V3)
      (charts : Set (OpenPartialHomeomorph W V3)),
      StandardLatticeHandleAtlas (Fin 0) (Fin 3) hamiltonZeroPeriodLattice d ∧
      PLDomain (fun c : charts => (c : OpenPartialHomeomorph W V3))
        (latticeHandleDomain (Fin 0) (Fin 3) hamiltonZeroPeriodLattice) ∧
      ∃ (r : ℝ) (c : charts), 0 < r ∧ r ≤ 1 / 64 ∧
        ∀ x : V3, ‖x‖ ≤ r →
          (0, QuotientAddGroup.mk x) ∈ (c : OpenPartialHomeomorph W V3).source ∧
          (c : OpenPartialHomeomorph W V3) (0, QuotientAddGroup.mk x) =
            h (CubeShell.vector x) := by
  classical
  let : Fact (0 < 4 * (16 : ℝ)) := ⟨by norm_num⟩
  let : T2Space W := hamiltonZeroHandleProductEquiv.isEmbedding.t2Space
  have hY : IsOpen Y := isClosed_singleton.isOpen_compl
  obtain ⟨d, hd⟩ := exists_zero_standard_lattice_handle_atlas
    (Fin 0) (Fin 3) hamiltonZeroPeriodLattice (by simp)
  have hR : latticeHandleDomain (Fin 0) (Fin 3) hamiltonZeroPeriodLattice = univ := by
    ext x
    have hx : x.1 = 0 := Subsingleton.elim _ _
    simp [latticeHandleDomain, hx]
  have hduniv : PLDomain d (univ : Set W) := by
    simpa only [hR] using hd.domain
  obtain ⟨_, e, r, i, K, _, _, hK, hKD, ⟨s⟩, _, hball,
    hr, hr64, _, hretained⟩ :=
    exists_zero_lattice_marked_brown_cap h hsource wall brown ∅ isCompact_empty
  let : Nonempty Y := ⟨i⟩
  let j : OpenPartialHomeomorph Y W :=
    hY.isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph (Subtype.val : Y → W)
  have hjs : j.source = univ := rfl
  have hj (y : Y) : y ∈ j.source := by rw [hjs]; exact mem_univ y
  let KX : Set W := (Subtype.val : Y → W) '' K
  let D : Set W := (interior KX)ᶜ
  have hKX : IsCompact KX := hK.image continuous_subtype_val
  have hD : IsClosed D := isOpen_interior.isClosed_compl
  have hjK : j.IsImage K KX := by
    intro y _
    exact Subtype.val_injective.mem_set_image
  have hreg : closure (interior KX) = KX := by
    apply Subset.antisymm (closure_minimal interior_subset hKX.isClosed)
    rintro x ⟨y, hy, rfl⟩
    have hy' : y ∈ closure (interior K) := hKD.closure_interior.symm ▸ hy
    exact closure_mono (hY.isOpenMap_subtype_val.image_interior_subset K)
      (image_closure_subset_closure_image continuous_subtype_val ⟨y, hy', rfl⟩)
  have hfrontK : frontier KX = (Subtype.val : Y → W) '' frontier K := by
    ext x
    constructor
    · intro hx
      obtain ⟨y, hy, rfl⟩ := hKX.isClosed.frontier_subset hx
      exact ⟨y, (hjK.frontier.apply_mem_iff (hj y)).mp hx, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact (hjK.frontier.apply_mem_iff (hj y)).mpr hy
  have hfrontD : frontier D = (Subtype.val : Y → W) '' frontier K := by
    change frontier ((interior KX)ᶜ) = _
    rw [frontier_compl]
    simpa only [frontier, hreg, interior_interior, hKX.isClosed.closure_eq] using hfrontK
  have hlocal (y : Y) (_hy : y ∈ (univ : Set Y)) :
      (y : W) ∈ D ↔ y ∉ interior K := by
    exact not_congr (hjK.interior.apply_mem_iff (hj y))
  have hold : (univ : Set W) \ D ⊆ Y := by
    rintro x ⟨_, hx⟩
    have hxi : x ∈ interior KX := not_not.mp hx
    obtain ⟨y, _, rfl⟩ := interior_subset hxi
    exact y.property
  have hcross (i : Y) (l : (Fin 0 → ℝ) × V3) :
      (j.symm.trans (e i)).symm.trans ((d l).restrOpen ∅ isOpen_empty) ∈
        piecewiseAffineGroupoid V3 := by
    apply (mem_piecewiseAffineGroupoid_iff_forward _).mpr
    apply LocallyPiecewiseAffineOn.locality
    intro x hx
    exact False.elim hx.2.2
  obtain ⟨charts, hcharts, hinsert, _⟩ :=
    exists_marked_brown_cap_PL_domain hY e hKD s d hduniv hD hfrontD
      (Subset.refl _) isOpen_univ (subset_univ _) hlocal hball
      isOpen_univ isOpen_empty (subset_univ _) (by simp)
      (by simp) hold (by simp) hcross
  let c := (j.symm.trans (e i)).restrOpen Dᶜ hD.isOpen_compl
  have hc : c ∈ charts := hinsert i
  refine ⟨d, charts, hd, hR.symm ▸ hcharts, r, ⟨c, hc⟩, hr, hr64, ?_⟩
  intro x hx
  obtain ⟨z, hz, hzK, hzi, hzval⟩ := hretained x hx
  have hznot : (z : W) ∉ D := by
    exact fun hn => hn (hY.isOpenMap_subtype_val.image_interior_subset K ⟨z, hzK, rfl⟩)
  have hzc : (z : W) ∈ c.source := by
    refine ⟨⟨j.map_source (hj z), ?_⟩, hznot⟩
    change j.symm (j z) ∈ (e i).source
    rw [j.left_inv (hj z)]
    exact hzi
  have hzcv : c (z : W) = h (CubeShell.vector x) := by
    change e i (j.symm (j z)) = _
    rw [j.left_inv (hj z)]
    exact hzval
  change (0, QuotientAddGroup.mk x) ∈ c.source ∧ c (0, QuotientAddGroup.mk x) = _
  rw [← hz]
  exact ⟨hzc, hzcv⟩

end PoincareConjecture.M76
