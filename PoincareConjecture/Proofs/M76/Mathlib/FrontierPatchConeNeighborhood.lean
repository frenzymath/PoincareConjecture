import PoincareConjecture.Proofs.M76.Mathlib.ConvexBoundaryRadial
import PoincareConjecture.Proofs.M76.Mathlib.AlexanderBaseConeCarriers
import PoincareConjecture.Proofs.M76.Mathlib.CoordinateHalfBoxes

set_option autoImplicit false

open Set Filter Geometry CoordinateHalfBoxes
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem Convex.smul_mem_interior_frontier_patch_cone
    {C P O : Set E} (hcv : Convex ℝ C) (hzero : (0 : E) ∈ interior C)
    {p : E} (hp : p ∈ frontier C) (hO : IsOpen O) (hpO : p ∈ O)
    (hOP : frontier C ∩ O ⊆ P) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    t • p ∈ interior C ∧ t • p ∈ interior (convexJoin ℝ {0} P) := by
  have hnhds : C ∈ 𝓝 (0 : E) := mem_interior_iff_mem_nhds.mp hzero
  have hgp : gauge C p = 1 := (gauge_eq_one_iff_mem_frontier hcv hnhds).mpr hp
  have hgt : gauge C (t • p) = t := by
    rw [gauge_smul_of_nonneg ht.1.le, smul_eq_mul, hgp, mul_one]
  have hgc : Continuous (gauge C) := continuous_gauge hcv hnhds
  let R : E → E := fun y => (gauge C y)⁻¹ • y
  have hRt : R (t • p) = p := by
    dsimp only [R]
    rw [hgt, inv_smul_smul₀ ht.1.ne']
  have hRc : ContinuousAt R (t • p) :=
    (hgc.continuousAt.inv₀ (by rw [hgt]; exact ht.1.ne')).smul continuousAt_id
  have hRO : R ⁻¹' O ∈ 𝓝 (t • p) :=
    hRc.preimage_mem_nhds (hO.mem_nhds (hRt.symm ▸ hpO))
  have hwindow : (gauge C) ⁻¹' Ioo (0 : ℝ) 1 ∈ 𝓝 (t • p) :=
    hgc.continuousAt.preimage_mem_nhds (isOpen_Ioo.mem_nhds (hgt.symm ▸ ht))
  refine ⟨(gauge_lt_one_iff_mem_interior hcv hnhds).mp (by rw [hgt]; exact ht.2),
    mem_interior_iff_mem_nhds.mpr ?_⟩
  filter_upwards [hwindow, hRO] with y hy hyO
  have hyfront : R y ∈ frontier C := by
    apply (gauge_eq_one_iff_mem_frontier hcv hnhds).mp
    dsimp only [R]
    rw [gauge_smul_of_nonneg (inv_nonneg.mpr hy.1.le), smul_eq_mul,
      inv_mul_cancel₀ hy.1.ne']
  apply (mem_convexJoin_zero_iff P y).mpr
  refine ⟨R y, hOP ⟨hyfront, hyO⟩, gauge C y, ⟨hy.1.le, hy.2.le⟩, ?_⟩
  dsimp only [R]
  rw [smul_inv_smul₀ hy.1.ne']

theorem Convex.mem_interior_frontier_patch_cone_of_radial_pole
    {C P O : Set E} (hcv : Convex ℝ C) (hzero : (0 : E) ∈ interior C)
    {p q : E} (hq : q ∈ frontier C) {ρ : ℝ} (hρ : 1 < ρ) (hqp : q = ρ • p)
    (hO : IsOpen O) (hqO : q ∈ O) (hOP : frontier C ∩ O ⊆ P) :
    p ∈ interior C ∧ p ∈ interior (convexJoin ℝ {0} P) := by
  have hρpos : 0 < ρ := zero_lt_one.trans hρ
  have hpq : ρ⁻¹ • q = p := by rw [hqp, inv_smul_smul₀ hρpos.ne']
  have h := hcv.smul_mem_interior_frontier_patch_cone hzero hq hO hqO hOP
    ⟨inv_pos.mpr hρpos, (inv_lt_one₀ hρpos).mpr hρ⟩
  rwa [hpq] at h

theorem ContinuousAffineEquiv.exists_box_in_frontier_patch_cone
    (f : ((ℝ × ℝ) × ℝ) ≃ᴬ[ℝ] E)
    {C P O : Set E} (hcv : Convex ℝ C) (hzero : (0 : E) ∈ interior C)
    {p q : E} (hf0 : f 0 = p) (hq : q ∈ frontier C)
    {ρ : ℝ} (hρ : 1 < ρ) (hqp : q = ρ • p)
    (hO : IsOpen O) (hqO : q ∈ O) (hOP : frontier C ∩ O ⊆ P) :
    ∃ r : ℝ, 0 < r ∧ f '' box r ⊆ interior C ∩ convexJoin ℝ {0} P := by
  have hp := hcv.mem_interior_frontier_patch_cone_of_radial_pole
    hzero hq hρ hqp hO hqO hOP
  let U := f ⁻¹' (interior C ∩ interior (convexJoin ℝ {0} P))
  have hU : IsOpen U := (isOpen_interior.inter isOpen_interior).preimage f.continuous
  have h0U : (0 : (ℝ × ℝ) × ℝ) ∈ U := by
    change f 0 ∈ interior C ∩ interior (convexJoin ℝ {0} P)
    rw [hf0]
    exact hp
  obtain ⟨r, hr, hbox⟩ := exists_box_subset hU h0U
  refine ⟨r, hr, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  exact ⟨(hbox hx).1, interior_subset (hbox hx).2⟩
