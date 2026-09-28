import PoincareConjecture.Proofs.M76.Rigidity.OriginalProductCut
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonIndexOneRetraction

set_option autoImplicit false

open Set Metric unitInterval Geometry

namespace PoincareConjecture.M76

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "Q" => sphere (0 : V2) 1
local notation "J" => Icc (-(1 / 2 : ℝ)) (1 / 2)
local notation "T" => Icc (-1 : ℝ) 1

private theorem radial_unit_mem (z : V2) (hz : z ≠ 0) : ‖z‖⁻¹ • z ∈ Q := by
  rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (norm_nonneg z)), inv_mul_cancel₀ (norm_ne_zero_iff.mpr hz)]

private theorem radial_interpolate_mem (t : I) (z : V2) (hz : z ∈ D) (hzero : z ≠ 0) :
    (1 - (t : ℝ)) • z + (t : ℝ) • (‖z‖⁻¹ • z) ∈ D := by
  exact (convex_closedBall (0 : V2) 1) hz
    (sphere_subset_closedBall (radial_unit_mem z hzero))
    (sub_nonneg.mpr t.property.2) t.property.1 (by ring)

theorem exists_disk_block_frontier_deformation
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {K : Set X} {j : V2 → X}
    (P : OriginalDiskProduct e K j) (F : Set X) (hF : IsCompact F)
    (hPF : ∀ z ∈ D ×ˢ T, P.map z ∈ F ↔ z.1 ∈ Q) :
    let Z := F ∪ P.closedStrip
    let core := P.map '' (closedBall (0 : V2) (1 / 2) ×ˢ J)
    let U := Z \ core
    ∃ H : C(I × U, X),
      (∀ (t : I) (x : U), H (t, x) ∈ Z) ∧
      (∀ x : U, H (0, x) = x) ∧
      (∀ x : U, H (1, x) ∈ F) ∧
      (∀ (t : I) (x : U), (x : X) ∈ F → H (t, x) = x) ∧
      ∀ (t : I) (x : U) (z : V2 × ℝ), z ∈ D ×ˢ J → P.map z = x →
        H (t, x) = P.map ((1 - (t : ℝ)) • z.1 +
          (t : ℝ) • (‖z.1‖⁻¹ • z.1), z.2) := by
  classical
  dsimp only
  let Z := F ∪ P.closedStrip
  let core := P.map '' (closedBall (0 : V2) (1 / 2) ×ˢ J)
  let U := Z \ core
  let A : Set (I × U) := {p | (p.2 : X) ∈ F}
  let B : Set (I × U) := {p | (p.2 : X) ∈ P.closedStrip}
  have hfull : D ×ˢ J ⊆ D ×ˢ T := by
    intro z hz
    exact ⟨hz.1, by linarith [hz.2.1], by linarith [hz.2.2]⟩
  have hA : IsClosed A := hF.isClosed.preimage (continuous_subtype_val.comp continuous_snd)
  have hB : IsClosed B :=
    (P.isCompact_closed_strip (by norm_num : (1 / 2 : ℝ) ≤ 1)).isClosed.preimage
      (continuous_subtype_val.comp continuous_snd)
  have hcover : A ∪ B = univ := by
    apply eq_univ_of_forall
    intro p
    exact p.2.property.1
  let E := P.embedding.isEmbedding.toHomeomorph
  let source : B → range (fun z : (D ×ˢ T : Set (V2 × ℝ)) => P.map z) := fun p =>
    ⟨p.val.2, by
      obtain ⟨z, hz, hzx⟩ := p.property
      exact ⟨⟨z, hfull hz⟩, hzx⟩⟩
  have hsource : Continuous source :=
    (continuous_subtype_val.comp (continuous_snd.comp continuous_subtype_val)).subtype_mk _
  let q : B → (D ×ˢ T : Set (V2 × ℝ)) := fun p => E.symm (source p)
  have hq : Continuous q := E.symm.continuous.comp hsource
  have hqval (p : B) : P.map (q p) = p.val.2 := by
    exact congrArg Subtype.val (E.apply_symm_apply (source p))
  have hqJ (p : B) : (q p).val.2 ∈ J := by
    obtain ⟨z, hz, hzx⟩ := p.property
    have heq := P.injective (q p).property (hfull hz) ((hqval p).trans hzx.symm)
    exact heq ▸ hz.2
  have hqpos (p : B) : 0 < ‖(q p).val.1‖ := by
    have hhalf : (1 / 2 : ℝ) < ‖(q p).val.1‖ := by
      by_contra hn
      apply p.val.2.property.2
      exact ⟨(q p).val, ⟨mem_closedBall_zero_iff.mpr (le_of_not_gt hn), hqJ p⟩, hqval p⟩
    linarith
  let radial : B → (D ×ˢ T : Set (V2 × ℝ)) := fun p =>
    ⟨((1 - (p.val.1 : ℝ)) • (q p).val.1 +
      (p.val.1 : ℝ) • (‖(q p).val.1‖⁻¹ • (q p).val.1), (q p).val.2),
      radial_interpolate_mem p.val.1 (q p).val.1 (q p).property.1
        (norm_pos_iff.mp (hqpos p)), (q p).property.2⟩
  have hradial : Continuous radial := by
    have ht : Continuous (fun p : B => (p.val.1 : ℝ)) :=
      continuous_subtype_val.comp (continuous_fst.comp continuous_subtype_val)
    have hz : Continuous (fun p : B => (q p).val.1) := hq.subtype_val.fst
    have hnorm := hz.norm.inv₀ (fun p => ne_of_gt (hqpos p))
    exact (((continuous_const.sub ht).smul hz).add
      (ht.smul (hnorm.smul hz))).prodMk hq.subtype_val.snd |>.subtype_mk _
  let f : C(A, X) := ⟨fun p => p.val.2,
    continuous_subtype_val.comp (continuous_snd.comp continuous_subtype_val)⟩
  let g : C(B, X) := ⟨fun p => P.map (radial p), P.embedding.continuous.comp hradial⟩
  have hagree (p : I × U) (hpA : p ∈ A) (hpB : p ∈ B) :
      f ⟨p, hpA⟩ = g ⟨p, hpB⟩ := by
    have hnorm : ‖(q ⟨p, hpB⟩).val.1‖ = 1 := by
      apply mem_sphere_zero_iff_norm.mp
      exact (hPF _ (q ⟨p, hpB⟩).property).mp ((hqval ⟨p, hpB⟩).symm ▸ hpA)
    change (p.2 : X) = P.map _
    simp only [radial, hnorm, inv_one, one_smul]
    rw [← add_smul, sub_add_cancel, one_smul]
    exact (hqval ⟨p, hpB⟩).symm
  obtain ⟨H, hleft, hright⟩ := HamiltonIndexOne.glue_closed_cover A B hA hB hcover f g hagree
  have hformula (t : I) (x : U) (z : V2 × ℝ) (hz : z ∈ D ×ˢ J)
      (hzx : P.map z = x) :
      H (t, x) = P.map ((1 - (t : ℝ)) • z.1 +
        (t : ℝ) • (‖z.1‖⁻¹ • z.1), z.2) := by
    have hxB : (t, x) ∈ B := ⟨z, hz, hzx⟩
    have heq : (q ⟨(t, x), hxB⟩).val = z :=
      P.injective (q ⟨(t, x), hxB⟩).property (hfull hz)
        ((hqval ⟨(t, x), hxB⟩).trans hzx.symm)
    rw [hright ⟨(t, x), hxB⟩]
    change P.map _ = _
    simp only [radial, heq]
  have hfix (t : I) (x : U) (hx : (x : X) ∈ F) : H (t, x) = x :=
    hleft ⟨(t, x), hx⟩
  refine ⟨H, ?_, ?_, ?_, hfix, hformula⟩
  · intro t x
    rcases x.property.1 with hx | ⟨z, hz, hzx⟩
    · exact Or.inl (hfix t x hx ▸ hx)
    · rw [hformula t x z hz hzx]
      have hzero : z.1 ≠ 0 := by
        intro heq
        apply x.property.2
        exact ⟨z, ⟨by rw [heq]; exact mem_closedBall_self (by norm_num), hz.2⟩, hzx⟩
      exact Or.inr ⟨((1 - (t : ℝ)) • z.1 + (t : ℝ) • (‖z.1‖⁻¹ • z.1), z.2),
        ⟨radial_interpolate_mem t z.1 hz.1 hzero, hz.2⟩, rfl⟩
  · intro x
    rcases x.property.1 with hx | ⟨z, hz, hzx⟩
    · exact hfix 0 x hx
    · rw [hformula 0 x z hz hzx]
      simpa using hzx
  · intro x
    rcases x.property.1 with hx | ⟨z, hz, hzx⟩
    · exact hfix 1 x hx ▸ hx
    · rw [hformula 1 x z hz hzx]
      change P.map ((1 - (1 : ℝ)) • z.1 + (1 : ℝ) • (‖z.1‖⁻¹ • z.1), z.2) ∈ F
      simp only [sub_self, zero_smul, one_smul, zero_add]
      have hzero : z.1 ≠ 0 := by
        intro heq
        apply x.property.2
        exact ⟨z, ⟨by rw [heq]; exact mem_closedBall_self (by norm_num), hz.2⟩, hzx⟩
      exact (hPF (‖z.1‖⁻¹ • z.1, z.2)
        (hfull (show (‖z.1‖⁻¹ • z.1, z.2) ∈ D ×ˢ J from
          ⟨sphere_subset_closedBall (radial_unit_mem z.1 hzero), hz.2⟩))).mpr
        (radial_unit_mem z.1 hzero)

theorem exists_disk_block_frontier_retraction
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {K : Set X} {j : V2 → X}
    (P : OriginalDiskProduct e K j) (F : Set X) (hF : IsCompact F)
    (hPF : ∀ z ∈ D ×ˢ T, P.map z ∈ F ↔ z.1 ∈ Q) :
    let Z := F ∪ P.closedStrip
    let core := P.map '' (closedBall (0 : V2) (1 / 2) ×ˢ J)
    let U := Z \ core
    ∃ (r : C(U, F))
      (H : (ContinuousMap.inclusion (sdiff_subset : U ⊆ Z)).Homotopy
        ((ContinuousMap.inclusion (subset_union_left : F ⊆ Z)).comp r)),
      (∀ (t : I) (x : U), (x : X) ∈ F → (H (t, x) : X) = x) ∧
      ∀ (t : I) (x : U) (z : V2 × ℝ), z ∈ D ×ˢ J → P.map z = x →
        (H (t, x) : X) = P.map ((1 - (t : ℝ)) • z.1 +
          (t : ℝ) • (‖z.1‖⁻¹ • z.1), z.2) := by
  dsimp only
  let Z := F ∪ P.closedStrip
  let core := P.map '' (closedBall (0 : V2) (1 / 2) ×ˢ J)
  let U := Z \ core
  obtain ⟨G, hGZ, hG0, hG1, hfix, hformula⟩ :=
    exists_disk_block_frontier_deformation P F hF hPF
  let r : C(U, F) := ⟨fun x => ⟨G (1, x), hG1 x⟩,
    (G.continuous.comp (continuous_const.prodMk continuous_id)).subtype_mk _⟩
  let H : (ContinuousMap.inclusion (sdiff_subset : U ⊆ Z)).Homotopy
      ((ContinuousMap.inclusion (subset_union_left : F ⊆ Z)).comp r) := {
    toFun := fun p => ⟨G p, hGZ p.1 p.2⟩
    continuous_toFun := G.continuous.subtype_mk _
    map_zero_left := fun x => Subtype.ext (hG0 x)
    map_one_left := fun _ => rfl }
  exact ⟨r, H, hfix, hformula⟩

end PoincareConjecture.M76
