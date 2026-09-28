import PoincareConjecture.Proofs.M76.Dehn.OriginalBoundaryDiskPush
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Complement.OriginalFinitePLBallImage

set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Disk" => closedBall (0 : V2) 1
local notation "Rim" => sphere (0 : V2) 1
local notation "I" => Icc (0 : ℝ) 1
local notation "Signed" => Icc (-1 : ℝ) 1

theorem exists_original_frontier_disk_inward_block
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {N O : Set X}
    (hN : IsCompact N) (he : PLDomain e N)
    {j : V2 → X} (hj : PolyhedralPLInCharts e j Disk)
    (hji : InjOn j Disk) (hjB : MapsTo j Disk (frontier N))
    (hO : IsOpen O) (hjO : j '' Disk ⊆ O) :
    ∃ k : V2 × ℝ → X,
      PolyhedralPLInCharts e k (Disk ×ˢ I) ∧ InjOn k (Disk ×ˢ I) ∧
      MapsTo k (Disk ×ˢ I) N ∧ MapsTo k (Disk ×ˢ I) O ∧
      (∀ x ∈ Disk, k (x, 0) = j x) ∧
      (∀ z ∈ Disk ×ˢ I, k z ∈ frontier N ↔ z.2 = 0) ∧
      (k '' (Disk ×ˢ I)) ∩ frontier N = j '' Disk ∧
      Nonempty (ChartwisePLBall e (k '' (Disk ×ˢ I))
        (k '' ((Rim ×ˢ I) ∪ (Disk ×ˢ ({0, 1} : Set ℝ))))) := by
  have hNne : N.Nonempty := ⟨j 0,
    he.closed.frontier_subset (hjB (mem_closedBall_self zero_le_one))⟩
  have hint : (interior N).Nonempty := closure_nonempty_iff.mp
    (he.closure_interior.symm ▸ hNne)
  obtain ⟨B, _, hBN, ⟨b⟩⟩ := he.exists_ball_in_interior hint
  obtain ⟨s, L, HB, c, hL, hc, hci, hcN, hc0, hcfront, _⟩ :=
    exists_protected_small_boundary_collar hN he (hBN.trans interior_subset) b
      isOpen_univ (subset_univ _)
  obtain ⟨q, hq, hqval⟩ := Dehn.exists_finitePL_boundary_disk_collar_parameter
    he.compatible hj hjB L hL HB c hc hci hc0
  have hqmap : MapsTo q Disk L.space := by
    intro x hx
    rw [hqval ⟨x, hx⟩]
    exact (HB.symm ⟨j x, hjB hx⟩).property
  have hbase (x : V2) (hx : x ∈ Disk) : c (q x, 0) = j x := by
    rw [hqval ⟨x, hx⟩, hc0, HB.apply_symm_apply]
  let f : Disk × Signed → X := fun z => c (q z.1, |(z.2 : ℝ)|)
  have hf : Continuous f := by
    apply hc.continuousOn.comp_continuous
      (hq.continuousOn.domRestrict.comp continuous_fst |>.prodMk
        ((continuous_subtype_val.comp continuous_snd).abs))
    intro z
    exact ⟨hqmap z.1.property, abs_nonneg _, abs_le.mpr z.2.property⟩
  have hf0 (x : Disk) : f (x, ⟨0, by norm_num⟩) ∈ O := by
    change c (q x, |(0 : ℝ)|) ∈ O
    rw [abs_zero, hbase x x.property]
    exact hjO ⟨x, x.property, rfl⟩
  obtain ⟨δ, hδ, hδsmall, hthin⟩ := hf.exists_closed_strip_subset hO hf0
  let a : V2 × ℝ → (s → ℝ × V3) × ℝ := Prod.map q (fun t => δ * t)
  have ha : FinitePiecewiseAffineOn a (Disk ×ˢ I) := by
    have ht : FinitePiecewiseAffineOn (fun t : ℝ => δ * t) I := by
      obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKs, _⟩, _⟩, _⟩ :=
        isFinitePLBallPair_Icc (show (0 : ℝ) < 1 by norm_num)
      rw [← hKs]
      exact (K.affineOnFaces_affine (δ • ContinuousAffineMap.id ℝ ℝ)).finitePiecewiseAffineOn hK
    exact hq.prodMap ht
  have hamap : MapsTo a (Disk ×ˢ I) (L.space ×ˢ I) := by
    intro z hz
    change q z.1 ∈ L.space ∧ 0 ≤ δ * z.2 ∧ δ * z.2 ≤ 1
    exact ⟨hqmap hz.1, mul_nonneg hδ.le hz.2.1, by nlinarith [hz.2.1, hz.2.2]⟩
  let k : V2 × ℝ → X := c ∘ a
  have hk : PolyhedralPLInCharts e k (Disk ×ˢ I) := by
    obtain ⟨K, hK, hKs, hKaff⟩ := ha
    rw [← hKs]
    exact hc.comp_finitePiecewiseAffineOn K hK ⟨K, hK, rfl, hKaff⟩
      (fun z hz => hamap (hKs.subset hz))
  have hki : InjOn k (Disk ×ˢ I) := by
    intro z hz w hw hzw
    have hab : a z = a w := congrArg Subtype.val
      (hci.injective (a₁ := ⟨a z, hamap hz⟩) (a₂ := ⟨a w, hamap hw⟩) hzw)
    have hqeq : q z.1 = q w.1 := congrArg Prod.fst hab
    have hj : j z.1 = j w.1 := by rw [← hbase z.1 hz.1, ← hbase w.1 hw.1, hqeq]
    exact Prod.ext (hji hz.1 hw.1 hj)
      (mul_left_cancel₀ hδ.ne' (congrArg Prod.snd hab))
  have hk0 (x : V2) (hx : x ∈ Disk) : k (x, 0) = j x := by
    change c (q x, δ * 0) = j x
    rw [mul_zero, hbase x hx]
  have hkfront (z : V2 × ℝ) (hz : z ∈ Disk ×ˢ I) :
      k z ∈ frontier N ↔ z.2 = 0 := by
    change c (a z) ∈ frontier N ↔ z.2 = 0
    rw [hcfront ⟨a z, hamap hz⟩]
    change δ * z.2 = 0 ↔ z.2 = 0
    exact mul_eq_zero.trans (or_iff_right hδ.ne')
  refine ⟨k, hk, hki, fun z hz => hcN (hamap hz), ?_, hk0, hkfront, ?_, ?_⟩
  · intro z hz
    change c (q z.1, δ * z.2) ∈ O
    have ht : δ * z.2 ∈ Signed :=
      ⟨by nlinarith [hz.2.1], by nlinarith [hz.2.1, hz.2.2]⟩
    have hpos : 0 ≤ δ * z.2 := mul_nonneg hδ.le hz.2.1
    have hh := hthin ⟨z.1, hz.1⟩ ⟨δ * z.2, ht⟩
      (by rw [abs_of_nonneg hpos]; nlinarith [hz.2.2])
    simpa only [f, abs_of_nonneg hpos] using hh
  · ext x
    constructor
    · rintro ⟨⟨z, hz, rfl⟩, hx⟩
      have hz0 := (hkfront z hz).mp hx
      have heq : z = (z.1, 0) := Prod.ext rfl hz0
      rw [heq, hk0 z.1 hz.1]
      exact ⟨z.1, hz.1, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨⟨(z, 0), ⟨hz, by norm_num⟩, hk0 z hz⟩, hjB hz⟩
  · exact exists_chartwisePLBall_image
      ((isFinitePLBallPair_unit_cube (ι := Fin 2)).prod
        (isFinitePLBallPair_Icc (show (0 : ℝ) < 1 by norm_num)))
      (ContinuousLinearEquiv.ofFinrankEq (by simp)) hk subset_rfl hki

end PoincareConjecture.M76
