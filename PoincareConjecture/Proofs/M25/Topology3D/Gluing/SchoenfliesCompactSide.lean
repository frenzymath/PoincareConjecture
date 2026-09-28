import PoincareConjecture.Proofs.M25.Mathlib.CompactBallChart
import PoincareConjecture.Proofs.M25.Mathlib.CofinalCylinderEnd
import PoincareConjecture.Proofs.M25.Topology3D.Gluing.SchoenfliesRadial

set_option autoImplicit false

open Set Metric
open scoped Manifold ContDiff

namespace PoincareConjecture.M25.Topology3D.SchoenfliesData

section Ball

variable {ψ : UnitTwoSphere × ℝ → E3} {δ t : ℝ} (S : SchoenfliesData ψ δ)

theorem isCompact_chart_closedBall (ht : t ∈ Ico δ 1) :
    IsCompact (S.chart '' closedBall 0 (S.radial t)) := by
  obtain ⟨D, hs, _, hD, _, _⟩ := S.exists_chart_openPartialHomeomorph
  rw [← hD]
  exact D.isCompact_image_closedBall hs (S.radial_lt t ht)

theorem interior_chart_closedBall (ht : t ∈ Ico δ 1) :
    interior (S.chart '' closedBall 0 (S.radial t)) =
      S.chart '' ball 0 (S.radial t) := by
  obtain ⟨D, hs, _, hD, _, _⟩ := S.exists_chart_openPartialHomeomorph
  rw [← hD]
  exact D.interior_image_closedBall hs (S.radial_pos t ht) (S.radial_lt t ht)

theorem frontier_chart_closedBall (ht : t ∈ Ico δ 1) :
    frontier (S.chart '' closedBall 0 (S.radial t)) =
      S.chart '' sphere 0 (S.radial t) := by
  obtain ⟨D, hs, _, hD, _, _⟩ := S.exists_chart_openPartialHomeomorph
  rw [← hD]
  exact D.frontier_image_closedBall hs (S.radial_pos t ht) (S.radial_lt t ht)

theorem isConnected_compl_chart_closedBall (ht : t ∈ Ico δ 1) :
    IsConnected (S.chart '' closedBall 0 (S.radial t))ᶜ := by
  obtain ⟨D, hs, _, hD, _, _⟩ := S.exists_chart_openPartialHomeomorph
  rw [← hD]
  exact D.m25_isConnected_compl_image_closedBall hs (S.radial_pos t ht)
    (S.radial_lt t ht) (by rw [← Module.finrank_eq_rank]; norm_num)

theorem image_sphere_eq_collar_level (ht : t ∈ Ico δ 1) :
    S.chart '' sphere 0 (S.radial t) = (fun q => ψ (q, S.side * t)) '' univ := by
  have hr := S.radial_pos t ht
  ext x
  constructor
  · rintro ⟨v, hv, rfl⟩
    have hvnorm : ‖v‖ = S.radial t := mem_sphere_zero_iff_norm.mp hv
    let q' : UnitTwoSphere := ⟨(S.radial t)⁻¹ • v, by
      rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hr), hvnorm, inv_mul_cancel₀ hr.ne']⟩
    obtain ⟨q, hq⟩ := S.boundary_map.surjective q'
    change S.boundary_map q = q' at hq
    have hvq : S.radial t • (S.boundary_map q).1 = v := by
      rw [hq]
      exact smul_inv_smul₀ hr.ne' v
    exact ⟨q, mem_univ _, (S.chart_collar q t ht).symm.trans (congrArg S.chart hvq)⟩
  · rintro ⟨q, _, rfl⟩
    refine ⟨S.radial t • (S.boundary_map q).1, ?_, S.chart_collar q t ht⟩
    rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs,
      mem_sphere_zero_iff_norm.mp (S.boundary_map q).2, mul_one, abs_of_pos hr]

end Ball

private theorem subset_compl_of_unbounded_image
    {W : Type*} [TopologicalSpace W] [T2Space W] (Phi : W ≃ₜ E3)
    {K T : Set W} (hK : IsCompact K) (hT : IsPreconnected T)
    (hunbounded : ¬ Bornology.IsBounded (Phi '' T)) (havoid : Disjoint T (frontier K)) :
    T ⊆ Kᶜ := by
  have hcover : T ⊆ interior K ∪ Kᶜ := by
    intro x hx
    by_cases hxi : x ∈ interior K
    · exact Or.inl hxi
    · exact Or.inr fun hxK => disjoint_left.mp havoid hx
        ⟨subset_closure hxK, hxi⟩
  have hdisjoint : Disjoint (interior K) Kᶜ :=
    disjoint_left.mpr fun _ hx hy => hy (interior_subset hx)
  rcases hT.subset_or_subset isOpen_interior hK.isClosed.isOpen_compl hdisjoint hcover
      with hinside | houtside
  · exact (hunbounded ((hK.image Phi.continuous).isBounded.subset
      (image_mono (hinside.trans interior_subset)))).elim
  · exact houtside

private theorem connectedSpace_unitTwoSphere : ConnectedSpace UnitTwoSphere := by
  apply isConnected_iff_connectedSpace.mp
  exact (isPathConnected_sphere
    (by rw [← Module.finrank_eq_rank]; norm_num) (0 : E3) zero_le_one).isConnected

section Cofinal

variable {W : Type*} [TopologicalSpace W] (Phi : W ≃ₜ E3)
  (e : OpenPartialHomeomorph (UnitTwoSphere × ℝ) W) {a b c h δ t : ℝ}
  (S : SchoenfliesData (fun p => Phi (e (p.1, c + h * p.2))) δ)

theorem isCompact_buffered_ball (ht : t ∈ Ico δ 1) :
    IsCompact (Phi.symm '' (S.chart '' closedBall 0 (S.radial t))) :=
  (S.isCompact_chart_closedBall ht).image Phi.symm.continuous

theorem interior_buffered_ball (ht : t ∈ Ico δ 1) :
    interior (Phi.symm '' (S.chart '' closedBall 0 (S.radial t))) =
      Phi.symm '' (S.chart '' ball 0 (S.radial t)) := by
  rw [← Phi.symm.image_interior, S.interior_chart_closedBall ht]

theorem frontier_buffered_ball (ht : t ∈ Ico δ 1) :
    frontier (Phi.symm '' (S.chart '' closedBall 0 (S.radial t))) =
      e.cylinderSlice (c + h * (S.side * t)) := by
  rw [← Phi.symm.image_frontier, S.frontier_chart_closedBall ht,
    S.image_sphere_eq_collar_level ht]
  ext x
  constructor
  · rintro ⟨_, ⟨q, _, rfl⟩, rfl⟩
    exact ⟨(q, c + h * (S.side * t)), ⟨mem_univ _, rfl⟩, (Phi.symm_apply_apply _).symm⟩
  · rintro ⟨⟨q, s⟩, ⟨_, hs⟩, rfl⟩
    have hs' : s = c + h * (S.side * t) := hs
    subst s
    exact ⟨Phi (e (q, c + h * (S.side * t))), ⟨q, mem_univ _, rfl⟩,
      Phi.symm_apply_apply _⟩

theorem isConnected_compl_buffered_ball (ht : t ∈ Ico δ 1) :
    IsConnected (Phi.symm '' (S.chart '' closedBall 0 (S.radial t)))ᶜ := by
  rw [← Phi.symm.image_compl]
  exact (S.isConnected_compl_chart_closedBall ht).image Phi.symm
    Phi.symm.continuous.continuousOn

private theorem signed_height_mem_Ioo (hh : 0 < h) (ha : a < c - h)
    (hb : c + h < b) (hδ : 0 ≤ δ) (ht : t ∈ Ico δ 1) :
    c + h * (S.side * t) ∈ Ioo a b := by
  have ht0 : 0 ≤ t := hδ.trans ht.1
  rcases mul_self_eq_one_iff.mp S.side_sq with hs | hs
  · simp only [hs, one_mul, mem_Ioo]
    constructor <;> nlinarith [ht.2]
  · simp only [hs, neg_one_mul, mem_Ioo]
    constructor <;> nlinarith [ht.2]

private theorem cylinderTail_subset_compl_buffered_ball
    (hsource : e.source = univ ×ˢ Ioo a b)
    (hend : ∀ d ∈ Ioo a b, IsCompact (e.cylinderTail b d)ᶜ)
    (hh : 0 < h) (ha : a < c - h) (hb : c + h < b) (hδ : 0 ≤ δ)
    (ht : t ∈ Ico δ 1) :
    e.cylinderTail b (c + h * (S.side * t)) ⊆
      (Phi.symm '' (S.chart '' closedBall 0 (S.radial t)))ᶜ := by
  let : T2Space W := Phi.isEmbedding.t2Space
  let : ConnectedSpace UnitTwoSphere := connectedSpace_unitTwoSphere
  have hd := S.signed_height_mem_Ioo Phi e hh ha hb hδ ht
  apply subset_compl_of_unbounded_image Phi (S.isCompact_buffered_ball Phi e ht)
    (e.isConnected_cylinderTail hsource hd).isPreconnected
    (Phi.not_isBounded_image_of_isCompact_compl (NormedSpace.unbounded_univ ℝ E3)
      (hend _ hd))
  rw [S.frontier_buffered_ball Phi e ht]
  apply disjoint_left.mpr
  rintro x hx ⟨z, hz, rfl⟩
  have hzs : z ∈ e.source := by
    rw [hsource]
    exact ⟨hz.1, (show z.2 = c + h * (S.side * t) from hz.2) ▸ hd⟩
  have hhgt := ((e.mem_cylinderTail_iff hsource hd.1 (e z)).mp hx).2.1
  rw [e.left_inv hzs, show z.2 = c + h * (S.side * t) from hz.2] at hhgt
  exact lt_irrefl _ hhgt

theorem side_eq_one_of_cofinal_cylinder
    (hsource : e.source = univ ×ˢ Ioo a b)
    (hend : ∀ d ∈ Ioo a b, IsCompact (e.cylinderTail b d)ᶜ)
    (hh : 0 < h) (ha : a < c - h) (hb : c + h < b)
    (hδ : 0 ≤ δ) (hδ_one : δ < 1) : S.side = 1 := by
  rcases mul_self_eq_one_iff.mp S.side_sq with hside | hside
  · exact hside
  · obtain ⟨t₀, hδ₀, h₀1⟩ := exists_between hδ_one
    obtain ⟨t₁, hδ₁, h₁₀⟩ := exists_between hδ₀
    have ht₀ : t₀ ∈ Ico δ 1 := ⟨hδ₀.le, h₀1⟩
    have ht₁ : t₁ ∈ Ico δ 1 := ⟨hδ₁.le, h₁₀.trans h₀1⟩
    have htail := S.cylinderTail_subset_compl_buffered_ball
      Phi e hsource hend hh ha hb hδ ht₀
    have hd₁ := S.signed_height_mem_Ioo Phi e hh ha hb hδ ht₁
    obtain ⟨q, hq⟩ := (NormedSpace.sphere_nonempty (E := E3) (x := 0) (r := 1)).mpr
      (by norm_num)
    let q₀ : UnitTwoSphere := ⟨q, hq⟩
    have hx : e (q₀, c + h * (S.side * t₁)) ∈
        e.cylinderTail b (c + h * (S.side * t₀)) := by
      refine ⟨(q₀, c + h * (S.side * t₁)), ⟨mem_univ _, ?_, hd₁.2⟩, rfl⟩
      rw [hside]
      nlinarith
    exfalso
    apply htail hx
    refine ⟨S.chart (S.radial t₁ • (S.boundary_map q₀).1), ⟨_, ?_, rfl⟩, ?_⟩
    · rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs,
        mem_sphere_zero_iff_norm.mp (S.boundary_map q₀).2, mul_one,
        abs_of_pos (S.radial_pos t₁ ht₁)]
      exact (S.radial_strictMono ht₁ ht₀ h₁₀).le
    · rw [S.chart_collar q₀ t₁ ht₁]
      exact Phi.symm_apply_apply _

theorem compl_cylinderTail_eq_buffered_ball
    (hsource : e.source = univ ×ˢ Ioo a b)
    (hend : ∀ d ∈ Ioo a b, IsCompact (e.cylinderTail b d)ᶜ)
    (hh : 0 < h) (ha : a < c - h) (hb : c + h < b) (hδ : 0 ≤ δ)
    (ht : t ∈ Ico δ 1) :
    (e.cylinderTail b (c + h * t))ᶜ =
      Phi.symm '' (S.chart '' closedBall 0 (S.radial t)) := by
  let : T2Space W := Phi.isEmbedding.t2Space
  let : WeaklyLocallyCompactSpace W := Phi.isClosedEmbedding.weaklyLocallyCompactSpace
  let : ConnectedSpace UnitTwoSphere := connectedSpace_unitTwoSphere
  have hside := S.side_eq_one_of_cofinal_cylinder
    Phi e hsource hend hh ha hb hδ (ht.1.trans_lt ht.2)
  have hd := S.signed_height_mem_Ioo Phi e hh ha hb hδ ht
  have hsub := S.cylinderTail_subset_compl_buffered_ball
    Phi e hsource hend hh ha hb hδ ht
  have hfront := S.frontier_buffered_ball Phi e ht
  simp only [hside, one_mul] at hd hsub hfront
  have hescape : ∀ Q : Set W, IsCompact Q → ∀ d ∈ Ioo a b,
      ∃ u ∈ Ioo d b, Disjoint Q (e.cylinderTail b u) := by
    intro Q hQ d hd
    exact e.exists_cylinderTail_disjoint_compact_after Phi hsource hend hQ hd
  have hclosure := e.closure_cylinderTail_eq_union_slice_of_escape hsource hescape hd
  have hKclosed := (S.isCompact_buffered_ball Phi e ht).isClosed
  have hslice : e.cylinderSlice (c + h * t) ⊆
      Phi.symm '' (S.chart '' closedBall 0 (S.radial t)) := by
    rw [← hfront]
    exact hKclosed.frontier_subset
  have hclosure_inter : closure (e.cylinderTail b (c + h * t)) ∩
      (Phi.symm '' (S.chart '' closedBall 0 (S.radial t)))ᶜ ⊆
        e.cylinderTail b (c + h * t) := by
    rw [hclosure]
    rintro x ⟨hx | hx, hxc⟩
    · exact hx
    · exact (hxc (hslice hx)).elim
  have hconnected := (S.isConnected_compl_buffered_ball Phi e ht).isPreconnected
  have hreverse := hconnected.subset_of_closure_inter_subset
    (e.isOpen_cylinderTail hsource hd.1)
      (by
        obtain ⟨x, hx⟩ := (e.isConnected_cylinderTail hsource hd).nonempty
        exact ⟨x, hsub hx, hx⟩) hclosure_inter
  rw [Subset.antisymm hsub hreverse, compl_compl]

theorem interior_compl_cylinderTail_eq_buffered_ball
    (hsource : e.source = univ ×ˢ Ioo a b)
    (hend : ∀ d ∈ Ioo a b, IsCompact (e.cylinderTail b d)ᶜ)
    (hh : 0 < h) (ha : a < c - h) (hb : c + h < b) (hδ : 0 ≤ δ)
    (ht : t ∈ Ico δ 1) :
    interior (e.cylinderTail b (c + h * t))ᶜ =
      Phi.symm '' (S.chart '' ball 0 (S.radial t)) := by
  rw [S.compl_cylinderTail_eq_buffered_ball Phi e hsource hend hh ha hb hδ ht]
  exact S.interior_buffered_ball Phi e ht

end Cofinal

end PoincareConjecture.M25.Topology3D.SchoenfliesData
