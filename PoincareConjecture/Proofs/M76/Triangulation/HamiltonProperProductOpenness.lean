import PoincareConjecture.Proofs.M76.Triangulation.HamiltonGeometricInputs
import PoincareConjecture.Proofs.M76.Mathlib.AffineHypersurfaceCharts
import PoincareConjecture.Proofs.M76.Mathlib.BoundedRegionBallInterior
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallImages
import PoincareConjecture.Proofs.M76.Mathlib.PolygonRegionRecognition

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76.HamiltonIndexOne

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D2" => closedBall (0 : V2) 1
local notation "Q2" => sphere (0 : V2) 1

private theorem relative_halfspace_neighborhood {R B Z : Set V3}
    (hBreg : closure (interior B) = B) (hBR : B ⊆ R) (hZ : IsClosed Z)
    (hfront : frontier B ⊆ frontier R ∪ Z)
    {x : V3} (hxB : x ∈ B) (hxZ : x ∉ Z)
    (H : OpenPartialHomeomorph V3 V3) (hxH : x ∈ H.source)
    (ell : V3 →ᴬ[ℝ] ℝ) (hell : ell.toAffineMap.linear ≠ 0)
    (hhalf : ∀ y ∈ H.source, y ∈ R ↔ 0 ≤ ell (H y)) :
    ∃ U : Set V3, IsOpen U ∧ x ∈ U ∧ U ∩ R ⊆ B \ Z := by
  let V := H.target ∩ H.symm ⁻¹' Zᶜ
  have hV : IsOpen V := H.isOpen_inter_preimage_symm hZ.isOpen_compl
  have hxV : H x ∈ V := ⟨H.map_source hxH, by
    change H.symm (H x) ∉ Z
    rwa [H.left_inv hxH]⟩
  obtain ⟨r, hr, hrV⟩ := Metric.isOpen_iff.mp hV (H x) hxV
  let U := H.source ∩ H ⁻¹' ball (H x) r
  have hU : IsOpen U := H.isOpen_inter_preimage isOpen_ball
  have hxU : x ∈ U := ⟨hxH, mem_ball_self hr⟩
  have hUZ (y : V3) (hy : y ∈ U) : y ∉ Z := by
    have h := (hrV hy.2).2
    change H.symm (H y) ∉ Z at h
    rwa [H.left_inv hy.1] at h
  have hRfront := H.isImage_frontier_of_affine_nonneg ell hell hhalf
  let P := ball (H x) r ∩ {z | 0 < ell z}
  have hPcv : Convex ℝ P := (convex_ball _ _).inter
    ((convex_Ioi (0 : ℝ)).affine_preimage ell.toAffineMap)
  have hPtarget : P ⊆ H.target := fun _ hz => (hrV hz.1).1
  have hpre : IsPreconnected (H.symm '' P) := hPcv.isPreconnected.image H.symm
    (H.continuousOn_invFun.mono hPtarget)
  have havoid : Disjoint (frontier (interior B)) (H.symm '' P) := by
    apply disjoint_left.mpr
    rintro y hy ⟨z, hz, rfl⟩
    have hzT := hPtarget hz
    have hzU : H.symm z ∈ U := ⟨H.map_target hzT, by
      change H (H.symm z) ∈ ball (H x) r
      rw [H.right_inv hzT]
      exact hz.1⟩
    have hyR : H.symm z ∈ frontier R := by
      rcases hfront (frontier_interior_subset hy) with h | h
      · exact h
      · exact False.elim (hUZ _ hzU h)
    have hzero := (hRfront.apply_mem_iff (H.map_target hzT)).mpr hyR
    rw [H.right_inv hzT] at hzero
    exact (ne_of_gt hz.2) hzero
  have hxcl : x ∈ closure (interior B) := hBreg.symm.subset hxB
  obtain ⟨z, hzU, hzB⟩ := mem_closure_iff.mp hxcl U hU hxU
  have hzR : z ∈ interior R := interior_mono hBR hzB
  have hzpos : 0 < ell (H z) := by
    have hle := (hhalf z hzU.1).mp (interior_subset hzR)
    have hne : ell (H z) ≠ 0 := fun h =>
      ((hRfront.apply_mem_iff hzU.1).mp h).2 hzR
    exact lt_of_le_of_ne hle (Ne.symm hne)
  have hmeet : ((H.symm '' P) ∩ interior B).Nonempty :=
    ⟨z, ⟨H z, ⟨hzU.2, hzpos⟩, H.left_inv hzU.1⟩, hzB⟩
  have hsub := hpre.m76_subset_of_disjoint_frontier isOpen_interior havoid hmeet
  have hellopen : IsOpenMap (ell : V3 → ℝ) :=
    ell.toAffineMap.isOpenMap ell.continuous
      (ell.toAffineMap.linear_surjective_iff.mp (LinearMap.surjective hell))
  have hposcl : closure {z : V3 | 0 < ell z} = {z : V3 | 0 ≤ ell z} := by
    change closure ((ell : V3 → ℝ) ⁻¹' Ioi 0) = (ell : V3 → ℝ) ⁻¹' Ici 0
    rw [← hellopen.preimage_closure_eq_closure_preimage ell.continuous, closure_Ioi]
  refine ⟨U, hU, hxU, ?_⟩
  rintro y ⟨hyU, hyR⟩
  have hycl : H y ∈ closure P := isOpen_ball.inter_closure
    ⟨hyU.2, hposcl.symm.subset ((hhalf y hyU.1).mp hyR)⟩
  have hyimage : H.symm (H y) ∈ closure (H.symm '' P) :=
    mem_closure_image
      (H.continuousOn_invFun.continuousAt (H.open_target.mem_nhds (H.map_source hyU.1)))
      hycl
  rw [H.left_inv hyU.1] at hyimage
  exact ⟨hBreg.subset (closure_mono hsub hyimage), hUZ y hyU⟩

private theorem isOpen_relative_sdiff_of_frontier_subset {R B Z : Set V3}
    (hR : PLDomain
      (fun _ : Unit => (Homeomorph.refl V3).toOpenPartialHomeomorph) R)
    (hBreg : closure (interior B) = B) (hBR : B ⊆ R) (hZ : IsClosed Z)
    (hfront : frontier B ⊆ frontier R ∪ Z) :
    IsOpen ((Subtype.val : R → V3) ⁻¹' (B \ Z)) := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  change (x : V3) ∈ B \ Z at hx
  by_cases hxf : (x : V3) ∈ frontier R
  · obtain ⟨ell, v, H, hv, hxH, _, _, hhalf⟩ := hR.halfspace x hxf
    have hell : ell.toAffineMap.linear ≠ 0 := by
      intro he
      have hv' : ell.toAffineMap.linear v = 1 := hv
      rw [he] at hv'
      norm_num at hv'
    obtain ⟨U, hU, hxU, hUR⟩ :=
      relative_halfspace_neighborhood hBreg hBR hZ hfront hx.1 hx.2 H hxH ell hell hhalf
    apply Filter.mem_of_superset ((hU.preimage continuous_subtype_val).mem_nhds hxU)
    intro y hy
    exact hUR ⟨hy, y.property⟩
  · have hxint : (x : V3) ∈ interior B := by
      by_contra hn
      rcases hfront ⟨subset_closure hx.1, hn⟩ with h | h
      · exact hxf h
      · exact hx.2 h
    have hU : IsOpen (interior B \ Z) := isOpen_interior.sdiff hZ
    apply Filter.mem_of_superset
      ((hU.preimage continuous_subtype_val).mem_nhds ⟨hxint, hx.2⟩)
    intro y hy
    exact ⟨interior_subset hy.1, hy.2⟩

private theorem isOpen_proper_product_standard {R : Set V3} {w : ℝ}
    (hR : PLDomain
      (fun _ : Unit => (Homeomorph.refl V3).toOpenPartialHomeomorph) R)
    (hw : 0 < w) (f : (V2 × ℝ) → V3)
    (hf : FinitePiecewiseAffineOn f (D2 ×ˢ Icc (-w) w))
    (hinj : InjOn f (D2 ×ˢ Icc (-w) w))
    (hinside : MapsTo f (D2 ×ˢ Icc (-w) w) R)
    (hproper : ∀ x ∈ D2 ×ˢ Icc (-w) w,
      f x ∈ frontier R ↔ x.1 ∈ Q2) :
    IsOpen ((Subtype.val : R → V3) ⁻¹' (f '' (D2 ×ˢ Ioo (-w) w))) := by
  let C : Set (V2 × ℝ) := D2 ×ˢ Icc (-w) w
  let T : Set (V2 × ℝ) := D2 ×ˢ Ioo (-w) w
  let Z0 : Set (V2 × ℝ) := D2 ×ˢ ({-w, w} : Set ℝ)
  let B := f '' C
  let Z := f '' Z0
  have hwidth : -w < w := by linarith
  have hTC : T ⊆ C := fun _ hx => ⟨hx.1, hx.2.1.le, hx.2.2.le⟩
  have hZC : Z0 ⊆ C := by
    rintro x ⟨hx, ht⟩
    change x.2 = -w ∨ x.2 = w at ht
    rcases ht with ht | ht
    · refine ⟨hx, ?_⟩
      rw [ht]
      exact left_mem_Icc.mpr hwidth.le
    · refine ⟨hx, ?_⟩
      rw [ht]
      exact right_mem_Icc.mpr hwidth.le
  have hC : IsCompact C := (isCompact_closedBall (0 : V2) 1).prod isCompact_Icc
  have hcv : Convex ℝ C := (convex_closedBall (0 : V2) 1).prod (convex_Icc (-w) w)
  have hCint : (interior C).Nonempty := by
    refine ⟨(0, 0), ?_⟩
    rw [show C = D2 ×ˢ Icc (-w) w from rfl, interior_prod_eq,
      interior_closedBall (0 : V2) one_ne_zero, interior_Icc]
    exact ⟨mem_ball_self zero_lt_one, by simpa using hw, hw⟩
  have hcopy := hf
  obtain ⟨K, hK, hKC, _⟩ := hcopy
  have hCball : IsFinitePLBallPair (V2 × ℝ) C (frontier C) :=
    isFinitePLBallPair_of_compact_convex hC hcv hCint K hK hKC
  have hBball := hCball.image hf hinj
  have hdim : Module.finrank ℝ (V2 × ℝ) = Module.finrank ℝ V3 := by
    simp [Module.finrank_prod]
  have hBfront : frontier B = f '' frontier C := hBball.frontier_eq_of_finrank_eq hdim
  have hBreg : closure (interior B) = B := hBball.closure_interior_of_finrank_eq hdim
  have hZ : IsCompact Z :=
    ((isCompact_closedBall (0 : V2) 1).prod
      (isCompact_singleton.insert (-w))).image_of_continuousOn
      (hf.continuousOn.mono hZC)
  have hCfront : frontier C = (Q2 ×ˢ Icc (-w) w) ∪ Z0 := by
    change frontier (D2 ×ˢ Icc (-w) w) = _
    rw [frontier_prod_eq, isClosed_closedBall.closure_eq, isClosed_Icc.closure_eq,
      frontier_closedBall _ one_ne_zero, frontier_Icc hwidth.le, union_comm]
  have hfront : frontier B ⊆ frontier R ∪ Z := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := hBfront.subset hy
    rcases hCfront.subset hx with hx | hx
    · exact Or.inl ((hproper x ⟨sphere_subset_closedBall hx.1, hx.2⟩).mpr hx.1)
    · exact Or.inr (mem_image_of_mem f hx)
  have hTimage : f '' T = B \ Z := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨mem_image_of_mem f (hTC hx), ?_⟩
      rintro ⟨z, hz, hzx⟩
      have he : z = x := hinj (hZC hz) (hTC hx) hzx
      subst z
      have ht := hz.2
      change x.2 = -w ∨ x.2 = w at ht
      rcases ht with he | he
      · exact (ne_of_gt hx.2.1) he
      · exact (ne_of_lt hx.2.2) he
    · rintro ⟨⟨x, hx, rfl⟩, hn⟩
      refine ⟨x, ⟨hx.1, ?_, ?_⟩, rfl⟩
      · by_contra h
        have he : x.2 = -w := le_antisymm (not_lt.mp h) hx.2.1
        exact hn (mem_image_of_mem f (show x ∈ Z0 from ⟨hx.1, Or.inl he⟩))
      · by_contra h
        have he : x.2 = w := le_antisymm hx.2.2 (not_lt.mp h)
        exact hn (mem_image_of_mem f (show x ∈ Z0 from ⟨hx.1, Or.inr he⟩))
  have hBR : B ⊆ R := by
    rintro _ ⟨x, hx, rfl⟩
    exact hinside hx
  have hopen := isOpen_relative_sdiff_of_frontier_subset hR hBreg hBR hZ.isClosed hfront
  rwa [← hTimage] at hopen

theorem isOpen_image_proper_finitePL_product {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {R : Set E} (a : E ≃ᴬ[ℝ] V3)
    (hR : PLDomain
      (fun _ : Unit => (Homeomorph.refl V3).toOpenPartialHomeomorph) (a '' R))
    {w : ℝ} (hw : 0 < w) (f : (V2 × ℝ) → E)
    (hf : FinitePiecewiseAffineOn f (D2 ×ˢ Icc (-w) w))
    (hinj : InjOn f (D2 ×ˢ Icc (-w) w))
    (hinside : MapsTo f (D2 ×ˢ Icc (-w) w) R)
    (hproper : ∀ x ∈ D2 ×ˢ Icc (-w) w,
      f x ∈ frontier R ↔ x.1 ∈ Q2) :
    IsOpen ((Subtype.val : R → E) ⁻¹' (f '' (D2 ×ˢ Ioo (-w) w))) := by
  let g : (V2 × ℝ) → V3 := a ∘ f
  have hg : FinitePiecewiseAffineOn g (D2 ×ˢ Icc (-w) w) :=
    hf.postcomp a.toContinuousAffineMap
  have hginj : InjOn g (D2 ×ˢ Icc (-w) w) := fun x hx y hy h =>
    hinj hx hy (a.injective h)
  have hginside : MapsTo g (D2 ×ˢ Icc (-w) w) (a '' R) :=
    fun x hx => mem_image_of_mem a (hinside hx)
  have hfront : a '' frontier R = frontier (a '' R) :=
    a.toHomeomorph.image_frontier R
  have hgproper (x : V2 × ℝ) (hx : x ∈ D2 ×ˢ Icc (-w) w) :
      g x ∈ frontier (a '' R) ↔ x.1 ∈ Q2 := by
    rw [← hfront]
    change a (f x) ∈ a '' frontier R ↔ _
    constructor
    · rintro ⟨y, hy, he⟩
      exact (hproper x hx).mp (a.injective he ▸ hy)
    · intro h
      exact mem_image_of_mem a ((hproper x hx).mpr h)
  have hopen := isOpen_proper_product_standard hR hw g hg hginj hginside hgproper
  let j := a.toHomeomorph.image R
  have hpull := hopen.preimage j.continuous
  have hsets : (Subtype.val : R → E) ⁻¹' (f '' (D2 ×ˢ Ioo (-w) w)) =
      j ⁻¹' ((Subtype.val : (a '' R) → V3) ⁻¹' (g '' (D2 ×ˢ Ioo (-w) w))) := by
    ext x
    change (x : E) ∈ f '' (D2 ×ˢ Ioo (-w) w) ↔
      a (x : E) ∈ g '' (D2 ×ˢ Ioo (-w) w)
    constructor
    · rintro ⟨y, hy, he⟩
      exact ⟨y, hy, congrArg a he⟩
    · rintro ⟨y, hy, he⟩
      exact ⟨y, hy, a.injective he⟩
  exact hsets.symm ▸ hpull

end PoincareConjecture.M76.HamiltonIndexOne
