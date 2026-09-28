import PoincareConjecture.Proofs.M38.CollarShift










set_option autoImplicit false

open Set TopologicalSpace
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M38

variable {Q : Type*} [TopologicalSpace Q] [ChartedSpace StandardCapSpace Q]
  (C : SmoothProjectiveDoubleModel Q)


theorem projectiveDouble_collar_sphere_iff (z : UnitTwoSphere) {s : ℝ}
    (hs : s ∈ Ioo (-1 : ℝ) 1) : C.collar (z, s) ∈ C.sphere ↔ s = 0 := by
  constructor
  · intro h
    obtain ⟨⟨w, t⟩, ⟨_, ht⟩, hwt⟩ := C.collar_sphere.symm.subset h
    have ht0 : t = 0 := ht
    subst t
    exact congrArg Prod.snd (C.collar_injective ⟨mem_univ _, hs⟩
      (by simp) hwt.symm)
  · rintro rfl
    exact C.collar_sphere.subset ⟨(z, 0), ⟨mem_univ _, rfl⟩, rfl⟩


theorem projectiveDouble_collar_first_iff (z : UnitTwoSphere) {s : ℝ}
    (hs : s ∈ Ioo (-1 : ℝ) 1) : C.collar (z, s) ∈ C.first_region ↔ s < 0 := by
  constructor
  · intro h
    by_contra hn
    rcases eq_or_lt_of_le (le_of_not_gt hn) with hzero | hpos
    · exact disjoint_left.mp C.sphere_disjoint
        ((projectiveDouble_collar_sphere_iff C z hs).mpr hzero.symm) (Or.inl h)
    · exact disjoint_left.mp C.disjoint h
        (C.collar_positive ⟨(z, s), ⟨mem_univ _, hpos, hs.2⟩, rfl⟩)
  · intro h
    exact C.collar_negative ⟨(z, s), ⟨mem_univ _, hs.1, h⟩, rfl⟩


theorem projectiveDouble_collar_closedFirst_iff (z : UnitTwoSphere) {s : ℝ}
    (hs : s ∈ Ioo (-1 : ℝ) 1) :
    C.collar (z, s) ∈ closure C.first_region ↔ s ≤ 0 := by
  rw [(projectiveDouble_region_closures C).1, mem_union,
    projectiveDouble_collar_first_iff C z hs,
    projectiveDouble_collar_sphere_iff C z hs]
  exact le_iff_lt_or_eq.symm



theorem exists_projectiveDouble_small_collar {O : Set Q}
    (hO : IsOpen O) (hSO : C.sphere ⊆ O) :
    ∃ R : ℝ, 0 < R ∧ R < 1 ∧
      C.collar '' (univ ×ˢ Icc (-R) R) ⊆ O := by
  let c := projectiveDoubleCollarChart C
  let W := c.source ∩ c ⁻¹' O
  have hW : IsOpen W := c.toOpenPartialHomeomorph.isOpen_inter_preimage hO
  have hzero : (univ : Set UnitTwoSphere) ×ˢ ({0} : Set ℝ) ⊆ W := by
    rintro ⟨z, s⟩ ⟨_, hs⟩
    have hs0 : s = 0 := hs
    subst s
    exact ⟨by simp [c, projectiveDoubleCollarChart],
      hSO ((projectiveDouble_collar_sphere_iff C z (by norm_num)).mpr rfl)⟩
  obtain ⟨U, V, _, hV, hU, hV0, hUV⟩ := generalized_tube_lemma
    (isCompact_univ : IsCompact (univ : Set UnitTwoSphere)) isCompact_singleton hW hzero
  obtain ⟨r, hr, hrv⟩ := Metric.isOpen_iff.mp hV 0 (hV0 (by simp))
  let R := min (r / 2) (1 / 2)
  have hR : 0 < R := lt_min (by positivity) (by norm_num)
  refine ⟨R, hR, (min_le_right _ _).trans_lt (by norm_num), ?_⟩
  rintro _ ⟨⟨z, s⟩, ⟨_, hs⟩, rfl⟩
  have hsr : |s| < r := (abs_le.mpr hs).trans_lt
    ((min_le_left _ _).trans_lt (by linarith))
  exact (hUV ⟨hU (mem_univ z), hrv (by
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using hsr)⟩).2

variable [T2Space Q]



theorem exists_projectiveDouble_first_interior_cut {O : Set Q}
    (hO : IsOpen O) (hSO : C.sphere ⊆ O) :
    ∃ (e : Diffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℝ ℝ ∞)
      (H : Diffeomorph (𝓡 3) (𝓡 3) Q Q ∞),
      StrictMono e ∧ e 0 ∈ Ioo (-1 : ℝ) 0 ∧
      (∀ (z : UnitTwoSphere) (s : ℝ), s ∈ Ioo (-1 : ℝ) 1 →
        H (C.collar (z, s)) = C.collar (z, e s)) ∧
      H '' closure C.first_region ⊆ C.first_region ∧
      ∀ x : Q, x ∉ O → H x = x := by
  obtain ⟨R, hR, hR1, hRO⟩ := exists_projectiveDouble_small_collar C hO hSO
  let c := projectiveDoubleCollarChart C
  obtain ⟨e, H, he, he0, heR, hefix, hH, hHfix⟩ :=
    exists_negative_collar_motion c hR hR1 rfl
  change ∀ (z : UnitTwoSphere) (s : ℝ), s ∈ Ioo (-1 : ℝ) 1 →
    H (C.collar (z, s)) = C.collar (z, e s) at hH
  have heone : e (-1) = -1 := hefix (-1) (by simpa using hR1.le)
  have hcsub : C.collar '' (univ ×ˢ Icc (-R) R) ⊆ c.target := by
    rintro _ ⟨z, hz, rfl⟩
    exact c.map_source ⟨mem_univ _, by linarith [hz.2.1], by linarith [hz.2.2]⟩
  refine ⟨e, H, he, ⟨by linarith, he0⟩, hH, ?_,
    fun x hx => hHfix x (fun h => hx (hRO h))⟩
  rintro _ ⟨x, hx, rfl⟩
  by_cases hxc : x ∈ c.target
  · let z := c.symm x
    have hz : z ∈ univ ×ˢ Ioo (-1 : ℝ) 1 := c.map_target hxc
    have hcx : C.collar z = x := c.toPartialEquiv.right_inv hxc
    have hs : z.2 ≤ 0 :=
      (projectiveDouble_collar_closedFirst_iff C z.1 hz.2).mp (hcx.symm ▸ hx)
    have hes : e z.2 ∈ Ioo (-1 : ℝ) 1 :=
      ⟨by simpa only [heone] using he hz.2.1, (he.monotone hs).trans_lt (he0.trans
        (by norm_num))⟩
    rw [← hcx, hH z.1 z.2 hz.2]
    exact (projectiveDouble_collar_first_iff C z.1 hes).mpr
      ((he.monotone hs).trans_lt he0)
  · rw [hHfix x (fun h => hxc (hcsub h))]
    rcases (projectiveDouble_region_closures C).1.subset hx with hfirst | hsphere
    · exact hfirst
    · obtain ⟨z, rfl⟩ := (projectiveDouble_central_range C).symm.subset hsphere
      exact (hxc (c.map_source (by simp [c, projectiveDoubleCollarChart]))).elim

end PoincareConjecture.M38
