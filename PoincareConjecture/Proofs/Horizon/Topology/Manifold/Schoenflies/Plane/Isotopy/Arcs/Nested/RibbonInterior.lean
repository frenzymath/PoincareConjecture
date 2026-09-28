import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Attachment.Compression.Slab



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Filter Function
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies.PlaneArcs.Nested

private abbrev E2 := EuclideanSpace Real (Fin 2)

private def ribbonShift
    (R : Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞) :
    Diffeomorph 𝓘(Real, Real × Real) (𝓡 2) (Real × Real) E2 ∞ where
  toFun p := R (WithLp.toLp 2 ![p.1, p.2 + 1])
  invFun x := ((R.symm x) 0, (R.symm x) 1 - 1)
  left_inv p := by simp
  right_inv x := by
    change R (WithLp.toLp 2 ![(R.symm x) 0, (R.symm x) 1 - 1 + 1]) = x
    have h : WithLp.toLp 2 ![(R.symm x) 0, (R.symm x) 1 - 1 + 1] = R.symm x := by
      ext i
      fin_cases i <;> simp
    rw [h, R.apply_symm_apply]
  contMDiff_toFun := by
    apply ContDiff.contMDiff
    apply R.contDiff.comp
    apply (contDiff_piLp 2).mpr
    intro i
    fin_cases i
    · exact contDiff_fst
    · exact contDiff_snd.add contDiff_const
  contMDiff_invFun := by
    apply ContDiff.contMDiff
    exact ((EuclideanSpace.proj (𝕜 := Real) (0 : Fin 2)).contDiff.comp R.symm.contDiff).prodMk
      (((EuclideanSpace.proj (𝕜 := Real) (1 : Fin 2)).contDiff.comp R.symm.contDiff).sub contDiff_const)




theorem exists_supported_ribbon_compression
    (R : Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞)
    {a w : Real} (_ha : 0 < a) (haw : a < w)
    {O W : Set E2} (hO : IsOpen O) (hW : IsOpen W)
    (htrace : ∀ u ∈ Ioo (-w) w, ∀ t ∈ Ioc (0 : Real) 1,
      R (WithLp.toLp 2 ![u, t]) ∈ O)
    (hbase : ∀ u ∈ Icc (-a) a, R (WithLp.toLp 2 ![u, 0]) ∈ W) :
    ∃ K : Set E2, IsCompact K ∧ K ⊆ O ∧
      Disjoint K (range (fun u : Real => R (WithLp.toLp 2 ![u, 0]))) ∧
      ∃ F : Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞,
        (∀ x ∉ K, F x = x) ∧
        F '' ((fun p : Real × Real => R (WithLp.toLp 2 ![p.1, p.2])) ''
          (Icc (-a) a ×ˢ Icc (0 : Real) 1)) ⊆
          ((fun p : Real × Real => R (WithLp.toLp 2 ![p.1, p.2])) ''
            (Icc (-a) a ×ˢ Icc (0 : Real) 1)) ∩ W := by
  let q := ribbonShift R
  let rmap : Real × Real → E2 := fun p => R (WithLp.toLp 2 ![p.1, p.2])
  have hrmap : Continuous rmap := R.continuous.comp (by fun_prop)
  have hbase' : Icc (-a) a ×ˢ {(0 : Real)} ⊆ rmap ⁻¹' W := by
    rintro ⟨u, t⟩ ⟨hu, ht⟩
    have ht0 : t = 0 := ht
    subst t
    exact hbase u hu
  obtain ⟨U, V, _, hV, hIU, h0V, hUV⟩ :=
    generalized_tube_lemma isCompact_Icc isCompact_singleton (hW.preimage hrmap) hbase'
  obtain ⟨ε, hε, hεV⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
    (hV.mem_nhds (h0V (mem_singleton 0)))
  let δ := min ε (1 / 2)
  have hδ : 0 < δ := lt_min hε (by norm_num)
  have hδ1 : δ < 1 := (min_le_right _ _).trans_lt (by norm_num)
  have hsmall (u : Real) (hu : u ∈ Icc (-a) a) (t : Real) (ht : t ∈ Icc 0 δ) :
      R (WithLp.toLp 2 ![u, t]) ∈ W := by
    change (u, t) ∈ rmap ⁻¹' W
    apply hUV
    refine ⟨hIU hu, hεV ?_⟩
    rw [mem_closedBall, dist_zero_right, Real.norm_eq_abs, abs_of_nonneg ht.1]
    exact ht.2.trans (min_le_left _ _)
  obtain ⟨L, hL, hIL, hLw⟩ := exists_compact_between isCompact_Icc isOpen_Ioo
    (show Icc (-a) a ⊆ Ioo (-w) w from fun u hu => ⟨by linarith [hu.1], by linarith [hu.2]⟩)
  obtain ⟨χ, hχone, hχzero, hχrange⟩ :=
    exists_contMDiffMap_one_nhds_of_subset_interior 𝓘(Real, Real)
      isClosed_Icc hIL (n := ⊤)
  have hχsupport : tsupport (χ : Real → Real) ⊆ L := by
    apply closure_minimal _ hL.isClosed
    intro u hu
    by_contra hn
    exact hu (hχzero u hn)
  have hχcompact : HasCompactSupport (χ : Real → Real) :=
    hL.of_isClosed_subset isClosed_closure hχsupport
  let α : Real → Real := fun u => (δ - 1) * χ u
  have hα : ContDiff Real ∞ α := contDiff_const.mul χ.contMDiff.contDiff
  have hαcompact : HasCompactSupport α := hχcompact.mul_left
  have hαsupport : tsupport α ⊆ L := by
    apply closure_minimal _ hL.isClosed
    intro u hu
    by_contra hn
    exact hu (by simp [α, hχzero u hn])
  have hαrange (u : Real) : δ - 1 ≤ α u ∧ α u ≤ 0 := by
    have hu := hχrange u
    constructor
    · simpa only [mul_one] using mul_le_mul_of_nonpos_left hu.2 (sub_nonpos.mpr hδ1.le)
    · exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hδ1.le) hu.1
  let T : Set (Real × Real) := q ⁻¹' O ∩ {p | 0 < p.2 + 1}
  have hT : IsOpen T := (hO.preimage q.continuous).inter
    (isOpen_lt continuous_const (continuous_snd.add continuous_const))
  have hαtrace (u : Real) (hu : u ∈ tsupport α) (t : Real) (ht : t ∈ Icc (0 : Real) 1) :
      (u, t * α u) ∈ T := by
    have hrange := hαrange u
    have hlo : δ ≤ t * α u + 1 := by
      have hh := mul_le_mul_of_nonpos_right ht.2 hrange.2
      linarith [hrange.1]
    have hhi : t * α u + 1 ≤ 1 := by
      have hh := mul_nonpos_of_nonneg_of_nonpos ht.1 hrange.2
      linarith
    exact ⟨htrace u (hLw (hαsupport hu)) _ ⟨hδ.trans_le hlo, hhi⟩, hδ.trans_le hlo⟩
  obtain ⟨K₀, hK₀, hK₀T, G, hGfirst, hGfix, hGtop, _⟩ :=
    Rounding.exists_graph_push_within α hα hαcompact hT hαtrace
  have hGbottom (u : Real) : G (u, -1) = (u, -1) := by
    apply hGfix
    intro h
    have hpos := (hK₀T h).2
    norm_num at hpos
  have hmono (u : Real) : Monotone (fun t : Real => (G (u, t)).2) :=
    (strictMono_vertical_of_compact_support G.toHomeomorph hGfirst hK₀ hGfix u).monotone
  let F := q.symm.trans (G.trans q)
  have hcoord (p : Real × Real) : F (q p) = q (G p) := by
    change q (G (q.symm (q p))) = q (G p)
    rw [q.symm_apply_apply]
  refine ⟨q '' K₀, hK₀.image q.continuous, ?_, ?_, F, ?_, ?_⟩
  · rintro _ ⟨p, hp, rfl⟩
    exact (hK₀T hp).1
  · apply disjoint_left.mpr
    rintro _ ⟨p, hp, rfl⟩ ⟨u, hu⟩
    have hbaseq : R (WithLp.toLp 2 ![u, 0]) = q (u, -1) := by
      change R (WithLp.toLp 2 ![u, 0]) = R (WithLp.toLp 2 ![u, -1 + 1])
      norm_num
    have he := q.injective (hbaseq.symm.trans hu)
    have hpos := (hK₀T hp).2
    rw [← he] at hpos
    norm_num at hpos
  · intro x hx
    change q (G (q.symm x)) = x
    rw [hGfix _ (fun h => hx ⟨q.symm x, h, q.apply_symm_apply x⟩), q.apply_symm_apply]
  · rintro _ ⟨_, ⟨⟨u, t⟩, ⟨hu, ht⟩, rfl⟩, rfl⟩
    have hq : R (WithLp.toLp 2 ![u, t]) = q (u, t - 1) := by
      change R (WithLp.toLp 2 ![u, t]) = R (WithLp.toLp 2 ![u, t - 1 + 1])
      rw [sub_add_cancel]
    have hlo := hmono u (show (-1 : Real) ≤ t - 1 by linarith [ht.1])
    have hhi := hmono u (show t - 1 ≤ 0 by linarith [ht.2])
    dsimp only at hlo hhi
    rw [hGbottom] at hlo
    rw [hGtop] at hhi
    have hαu : α u = δ - 1 := by
      dsimp [α]
      rw [hχone.self_of_nhdsSet u hu, mul_one]
    rw [hαu] at hhi
    have hheight : (G (u, t - 1)).2 + 1 ∈ Icc (0 : Real) δ := by
      constructor <;> linarith
    dsimp only
    rw [hq, hcoord]
    change R (WithLp.toLp 2 ![(G (u, t - 1)).1, (G (u, t - 1)).2 + 1]) ∈ _
    rw [hGfirst]
    exact ⟨⟨(u, (G (u, t - 1)).2 + 1),
      ⟨hu, hheight.1, hheight.2.trans hδ1.le⟩, rfl⟩, hsmall u hu _ hheight⟩

private theorem image_eq_self_of_support_subset
    (H : Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞)
    {K S : Set E2} (hKS : K ⊆ S) (hfix : ∀ x ∉ K, H x = x) :
    H '' S = S := by
  have hc : H '' Sᶜ = Sᶜ := by
    calc
      H '' Sᶜ = id '' Sᶜ := image_congr (fun x hx => hfix x (fun h => hx (hKS h)))
      _ = Sᶜ := image_id _
  exact compl_injective ((image_compl_eq H.bijective).symm.trans hc)




theorem exists_supported_isotopy_fixing_ribbon
    (R : Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞)
    {a w : Real} (ha : 0 < a) (haw : a < w)
    {A B O : Set E2} (hO : IsOpen O) (hOA : O ⊆ A) (hOB : O ⊆ B)
    (htrace : ∀ u ∈ Ioo (-w) w, ∀ t ∈ Ioc (0 : Real) 1,
      R (WithLp.toLp 2 ![u, t]) ∈ O)
    {K : Set E2} (hK : IsCompact K)
    (hbase : Disjoint K ((fun u : Real => R (WithLp.toLp 2 ![u, 0])) '' Icc (-a) a))
    (Φ : Real → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞)
    (hΦ0 : ∀ x, Φ 0 x = x)
    (hΦs : ContDiff Real ∞ (fun z : Real × E2 => Φ z.1 z.2))
    (hΦi : ContDiff Real ∞ (fun z : Real × E2 => (Φ z.1).symm z.2))
    (hΦfix : ∀ t x, x ∉ K → Φ t x = x)
    (hΦAB : Φ 1 '' A = B) :
    ∃ L : Set E2, IsCompact L ∧
      Disjoint L ((fun p : Real × Real => R (WithLp.toLp 2 ![p.1, p.2])) ''
        (Icc (-a) a ×ˢ Icc (0 : Real) 1)) ∧
      ∃ Ψ : Real → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞,
        (∀ x, Ψ 0 x = x) ∧
        ContDiff Real ∞ (fun z : Real × E2 => Ψ z.1 z.2) ∧
        ContDiff Real ∞ (fun z : Real × E2 => (Ψ z.1).symm z.2) ∧
        (∀ t x, x ∉ L → Ψ t x = x) ∧
        Ψ 1 '' A = B := by
  obtain ⟨J, hJ, hJO, _, H, hHfix, hHP⟩ :=
    exists_supported_ribbon_compression R ha haw hO hK.isClosed.isOpen_compl htrace
      (fun u hu hKu => disjoint_left.mp hbase hKu ⟨u, hu, rfl⟩)
  have hHA : H '' A = A := image_eq_self_of_support_subset H (hJO.trans hOA) hHfix
  have hHB : H '' B = B := image_eq_self_of_support_subset H (hJO.trans hOB) hHfix
  have hHiB : H.symm '' B = B := by
    calc
      H.symm '' B = H.symm '' (H '' B) := congrArg (fun S => H.symm '' S) hHB.symm
      _ = B := by simp only [image_image, H.symm_apply_apply, image_id']
  let Ψ : Real → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞ :=
    fun t => H.trans ((Φ t).trans H.symm)
  have hΨ (t : Real) (x : E2) : Ψ t x = H.symm (Φ t (H x)) := rfl
  have hΨi (t : Real) (x : E2) : (Ψ t).symm x = H.symm ((Φ t).symm (H x)) := rfl
  refine ⟨H.symm '' K, hK.image H.symm.continuous, ?_, Ψ, ?_, ?_, ?_, ?_, ?_⟩
  · apply disjoint_left.mpr
    rintro _ ⟨x, hx, rfl⟩ hp
    have hn := (hHP (mem_image_of_mem H hp)).2
    exact hn (by simpa only [H.apply_symm_apply] using hx)
  · intro x
    rw [hΨ, hΦ0, H.symm_apply_apply]
  · exact H.symm.contDiff.comp
      (hΦs.comp (contDiff_fst.prodMk (H.contDiff.comp contDiff_snd)))
  · exact H.symm.contDiff.comp
      (hΦi.comp (contDiff_fst.prodMk (H.contDiff.comp contDiff_snd)))
  · intro t x hx
    rw [hΨ, hΦfix t (H x) (fun h => hx ⟨H x, h, H.symm_apply_apply x⟩),
      H.symm_apply_apply]
  · change (fun x => H.symm (Φ 1 (H x))) '' A = B
    calc
      _ = H.symm '' (Φ 1 '' (H '' A)) := by rw [image_image, image_image]
      _ = B := by rw [hHA, hΦAB, hHiB]

end Poincare.Manifold.Schoenflies.PlaneArcs.Nested
