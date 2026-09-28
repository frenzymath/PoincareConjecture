import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Isotopy.Arcs.Terminal.ModelMarkedCircles
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Isotopy.ArcPairs.CircleMatching

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies.PlaneArcs.Terminal

open SaddleLevel Plane.Isotopy.ArcPairs

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S1 := sphere (0 : E2) 1
private abbrev S2 := sphere (0 : E3) 1

private theorem filled_disk_in_halfplane
    (F : Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞)
    {σ : Real} (hσ : σ ^ 2 = 1)
    (hboundary : ∀ x ∈ F '' sphere (0 : E2) 1, σ * x 0 < 0) :
    ∀ x ∈ F '' closedBall (0 : E2) 1, σ * x 0 < 0 := by
  let K := F '' closedBall (0 : E2) 1
  have hK : IsCompact K := (isCompact_closedBall (0 : E2) 1).image F.continuous
  have hne : K.Nonempty := ⟨F 0, mem_image_of_mem F (mem_closedBall_self (by norm_num))⟩
  have hf : Continuous (fun x : E2 => σ * x 0) := by fun_prop
  obtain ⟨m, hm, hmax⟩ := hK.exists_isMaxOn hne hf.continuousOn
  have hmb : m ∈ F '' sphere (0 : E2) 1 := by
    obtain ⟨u, hu, rfl⟩ := hm
    by_contra hn
    have hu' : u ∈ ball (0 : E2) 1 := by
      rw [mem_ball_zero_iff]
      have hun := mem_closedBall_zero_iff.mp hu
      apply lt_of_le_of_ne hun
      intro heq
      exact hn ⟨u, mem_sphere_zero_iff_norm.mpr heq, rfl⟩
    have hopen : IsOpen (F '' ball (0 : E2) 1) :=
      F.toHomeomorph.isOpenMap _ isOpen_ball
    obtain ⟨ε, hε, hεsub⟩ := Metric.isOpen_iff.mp hopen (F u) (mem_image_of_mem F hu')
    have hσabs : |σ| = 1 := by
      rcases sq_eq_one_iff.mp hσ with hs | hs <;> rw [hs] <;> norm_num
    let y : E2 := F u + EuclideanSpace.single 0 (σ * (ε / 2))
    have hy : y ∈ ball (F u) ε := by
      rw [mem_ball, dist_eq_norm]
      simp only [y, add_sub_cancel_left, PiLp.norm_single, Real.norm_eq_abs,
        abs_mul, hσabs, one_mul, abs_of_pos (half_pos hε)]
      linarith
    have hyK : y ∈ K := (image_mono ball_subset_closedBall) (hεsub hy)
    have h := hmax hyK
    change σ * (F u 0 + σ * (ε / 2)) ≤ σ * F u 0 at h
    nlinarith
  intro x hx
  exact (hmax hx).trans_lt (hboundary m hmb)

private theorem not_nested_of_opposite_halfplanes
    (C D : S1 → E2) {σ : Real} (hσ : σ ^ 2 = 1)
    (hC : ∀ q, 0 < σ * C q 0) (hD : ∀ q, σ * D q 0 < 0) :
    ¬ NestedPair C D := by
  rintro ⟨F, hF, hinside⟩
  have hboundary (x : E2) (hx : x ∈ F '' sphere (0 : E2) 1) : σ * x 0 < 0 := by
    rw [hF] at hx
    obtain ⟨q, rfl⟩ := hx
    exact hD q
  let q : S1 := ⟨EuclideanSpace.single 0 1, by simp⟩
  have hneg := filled_disk_in_halfplane F hσ hboundary (C q)
    ((image_mono ball_subset_closedBall) (hinside (mem_range_self q)))
  linarith [hC q]

private theorem circle_lies_on_one_side
    (C : S1 → E2) (hC : Continuous C) (hne : ∀ q, C q 0 ≠ 0) :
    (∀ q, C q 0 < 0) ∨ (∀ q, 0 < C q 0) := by
  let : ConnectedSpace S1 := isConnected_iff_connectedSpace.mp
    (isConnected_sphere (by simp [← Module.finrank_eq_rank, E2]) (0 : E2) zero_le_one)
  have hconn := isPreconnected_range hC
  have hparts := isPreconnected_iff_subset_of_disjoint_closed.mp hconn
    {x : E2 | x 0 ≤ 0} {x : E2 | 0 ≤ x 0}
    (isClosed_le (by fun_prop) continuous_const)
    (isClosed_le continuous_const (by fun_prop))
    (fun x _ => le_total (x 0) 0) (by
      rw [eq_empty_iff_forall_notMem]
      rintro x ⟨⟨q, rfl⟩, hle, hge⟩
      exact (hne q (le_antisymm hle hge)).elim)
  rcases hparts with hneg | hpos
  · exact Or.inl (fun q => lt_of_le_of_ne (hneg (mem_range_self q)) (hne q))
  · exact Or.inr (fun q => lt_of_le_of_ne (hpos (mem_range_self q)) (hne q).symm)

private theorem raw_standard_pair_not_nested
    {s : Real} (hs : 0 < s) (hsu : s < 1 / 4)
    (C : Fin 2 → S1 → E2) (hC : ∀ i, Continuous (C i))
    (hcover : (⋃ i, range (C i)) =
      {x : E2 | Saddle.toE3 x (-1 - s) ∈ Saddle.shear '' sphere (0 : E3) 1}) :
    ¬ NestedPair (C 0) (C 1) ∧ ¬ NestedPair (C 1) (C 0) := by
  have hlevel (i : Fin 2) (q : S1) :
      (C i q 0) ^ 2 + (C i q 1) ^ 2 + (-1 - s + (C i q 0) ^ 2) ^ 2 = 1 := by
    have hm := hcover.subset (mem_iUnion_of_mem i (mem_range_self q))
    rw [Saddle.shear_image_sphere] at hm
    exact hm
  have hne (i : Fin 2) (q : S1) : C i q 0 ≠ 0 := by
    intro hz
    have hl := hlevel i q
    rw [hz] at hl
    nlinarith [sq_nonneg (C i q 1), sq_nonneg s]
  let X := Real.sqrt (1 / 2 + s)
  let Y := Real.sqrt (1 / 4 - s)
  have hX : 0 < X := Real.sqrt_pos.mpr (by linarith)
  have hXsq : X ^ 2 = 1 / 2 + s := Real.sq_sqrt (by linarith)
  have hYsq : Y ^ 2 = 1 / 4 - s := Real.sq_sqrt (by linarith)
  have hpoint (σ : Real) (hσ : σ ^ 2 = 1) :
      (WithLp.toLp 2 ![σ * X, Y] : E2) ∈ ⋃ i, range (C i) := by
    rw [hcover, Saddle.shear_image_sphere]
    change (σ * X) ^ 2 + Y ^ 2 + (-1 - s + (σ * X) ^ 2) ^ 2 = 1
    rw [mul_pow, hσ, one_mul, hXsq, hYsq]
    ring
  have hnotbothneg : ¬ (∀ i q, C i q 0 < 0) := by
    intro h
    obtain ⟨i, q, hq⟩ := mem_iUnion.mp (hpoint 1 (by norm_num))
    have hneg := h i q
    rw [hq] at hneg
    change 1 * X < 0 at hneg
    linarith
  have hnotbothpos : ¬ (∀ i q, 0 < C i q 0) := by
    intro h
    obtain ⟨i, q, hq⟩ := mem_iUnion.mp (hpoint (-1) (by norm_num))
    have hpos := h i q
    rw [hq] at hpos
    change 0 < -1 * X at hpos
    linarith
  rcases circle_lies_on_one_side (C 0) (hC 0) (hne 0) with h0 | h0 <;>
    rcases circle_lies_on_one_side (C 1) (hC 1) (hne 1) with h1 | h1
  · exact (hnotbothneg (by intro i; fin_cases i <;> assumption)).elim
  · exact ⟨not_nested_of_opposite_halfplanes (C 0) (C 1) (σ := -1) (by norm_num)
      (fun q => by linarith [h0 q]) (fun q => by linarith [h1 q]),
      not_nested_of_opposite_halfplanes (C 1) (C 0) (σ := 1) (by norm_num)
        (fun q => by simpa using h1 q) (fun q => by simpa using h0 q)⟩
  · exact ⟨not_nested_of_opposite_halfplanes (C 0) (C 1) (σ := 1) (by norm_num)
      (fun q => by simpa using h0 q) (fun q => by simpa using h1 q),
      not_nested_of_opposite_halfplanes (C 1) (C 0) (σ := -1) (by norm_num)
        (fun q => by linarith [h1 q]) (fun q => by linarith [h0 q])⟩
  · exact (hnotbothpos (by intro i; fin_cases i <;> assumption)).elim

private theorem projection_lift (x : E2) (z : Real) :
    Saddle.toE2 (Saddle.toE3 x z) = x := by
  ext i
  fin_cases i <;> rfl

private theorem lift_projection {y : E3} {z : Real} (hy : y 2 = z) :
    Saddle.toE3 (Saddle.toE2 y) z = y := by
  ext i
  fin_cases i <;> simp [Saddle.toE2, Saddle.toE3, hy]

private theorem smooth_projection : ContDiff Real ∞ Saddle.toE2 := by
  apply (contDiff_piLp 2).mpr
  intro i
  fin_cases i
  · exact (EuclideanSpace.proj (𝕜 := Real) (0 : Fin 3)).contDiff
  · exact (EuclideanSpace.proj (𝕜 := Real) (1 : Fin 3)).contDiff

private theorem smooth_lift (z : Real) : ContDiff Real ∞ (fun x => Saddle.toE3 x z) := by
  apply (contDiff_piLp 2).mpr
  intro i
  fin_cases i
  · exact (EuclideanSpace.proj (𝕜 := Real) (0 : Fin 2)).contDiff
  · exact (EuclideanSpace.proj (𝕜 := Real) (1 : Fin 2)).contDiff
  · exact contDiff_const

private theorem exists_affine_height_fiber
    (G : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    {c scale : Real} (hscale : 0 < scale)
    (hheight : ∀ y, G y 2 = c + scale * (y 2 + 1)) (a : Real) :
    ∃ F : Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞,
      ∀ x, Saddle.toE3 (F x) (c + scale * (a + 1)) = G (Saddle.toE3 x a) := by
  let b := c + scale * (a + 1)
  let f : E2 → E2 := fun x => Saddle.toE2 (G (Saddle.toE3 x a))
  let g : E2 → E2 := fun x => Saddle.toE2 (G.symm (Saddle.toE3 x b))
  have hfheight (x : E2) : G (Saddle.toE3 x a) 2 = b := hheight _
  have hgheight (x : E2) : G.symm (Saddle.toE3 x b) 2 = a := by
    have he := hheight (G.symm (Saddle.toE3 x b))
    rw [G.apply_symm_apply] at he
    change c + scale * (a + 1) = c + scale * (G.symm (Saddle.toE3 x b) 2 + 1) at he
    nlinarith
  let F : Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞ :=
    { toEquiv :=
        { toFun := f
          invFun := g
          left_inv := by
            intro x
            dsimp [f, g]
            rw [lift_projection (hfheight x), G.symm_apply_apply, projection_lift]
          right_inv := by
            intro x
            dsimp [f, g]
            rw [lift_projection (hgheight x), G.apply_symm_apply, projection_lift] }
      contMDiff_toFun :=
        (smooth_projection.comp (G.contDiff.comp (smooth_lift a))).contMDiff
      contMDiff_invFun :=
        (smooth_projection.comp (G.symm.contDiff.comp (smooth_lift b))).contMDiff }
  exact ⟨F, fun x => lift_projection (hfheight x)⟩

private theorem nestedPair_postcomp
    (Q : Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞) {C D : S1 → E2}
    (h : NestedPair C D) : NestedPair (Q ∘ C) (Q ∘ D) := by
  obtain ⟨F, hF, hin⟩ := h
  refine ⟨F.trans Q, ?_, ?_⟩
  · change (Q ∘ F) '' sphere (0 : E2) 1 = range (Q ∘ D)
    rw [image_comp, hF, range_comp]
  · rintro x ⟨q, rfl⟩
    obtain ⟨u, hu, he⟩ := hin (mem_range_self q)
    exact ⟨u, hu, congrArg Q he⟩

variable {f : S2 → E3} {M : SphereMorseReduction f} {g : S2 → E3}
  {P : SphereSurgeryPath (M.v : E3) (fun q => M.D (f q)) g}
  {p : S2} {e : OpenPartialHomeomorph E2 S2}

private theorem standard_model_pair_not_nested
    (d : TerminalSaddleGeometry M P p e) (hmodel : d.model = Saddle.shear)
    (hform : ∀ x ∈ e.source, inner Real (M.v : E3) (g (e x)) =
      inner Real (M.v : E3) (g p) - x 0 ^ 2 + x 1 ^ 2)
    {t : Real} (ht : 0 < t) (htu : t < d.scale / 4)
    (C : Fin 2 → S1 → E2) (hC : ∀ i, Continuous (C i))
    (hcover : (⋃ i, range (C i)) = d.B (inner Real (M.v : E3) (g p) - t)) :
    ¬ NestedPair (C 0) (C 1) ∧ ¬ NestedPair (C 1) (C 0) := by
  let c := inner Real (M.v : E3) (g p)
  let s := t / d.scale
  let G := d.transport.trans d.flatten
  have hs : 0 < s := div_pos ht d.scale_pos
  have hsu : s < 1 / 4 := (div_lt_iff₀ d.scale_pos).mpr (by linarith)
  have hcenter := terminal_standard_model_chart_center d hmodel hform
  have hh : d.model (d.modelChart 0) 2 = -1 := by
    rw [hmodel, hcenter]
    exact Saddle.height_saddlePoint
  have hG (y : E3) : G y 2 = c + d.scale * (y 2 + 1) := by
    change d.frame (d.D (d.transport y)) 2 = _
    rw [d.frame_height, d.D_height, d.transport_height, hh]
    simp only [sub_neg_eq_add]
    rfl
  obtain ⟨F, hF⟩ := exists_affine_height_fiber G d.scale_pos hG (-1 - s)
  have hb : c + d.scale * (-1 - s + 1) = c - t := by
    dsimp [s]
    field_simp [d.scale_pos.ne']
    ring
  rw [hb] at hF
  have hspatial : d.flatten '' (d.filledModel '' sphere (0 : E3) 1) =
      G '' (Saddle.shear '' sphere (0 : E3) 1) := by
    simp only [image_image]
    congr 1
    funext x
    change d.flatten (d.transport (d.model x)) = d.flatten (d.transport (Saddle.shear x))
    rw [hmodel]
  have hmem (x : E2) : F x ∈ d.B (c - t) ↔
      Saddle.toE3 x (-1 - s) ∈ Saddle.shear '' sphere (0 : E3) 1 := by
    change Saddle.toE3 (F x) (c - t) ∈ d.flatten '' (d.filledModel '' sphere (0 : E3) 1) ↔ _
    rw [hF, hspatial]
    exact G.injective.mem_set_image
  let U : Fin 2 → S1 → E2 := fun i => F.symm ∘ C i
  have hU (i : Fin 2) : Continuous (U i) := F.symm.continuous.comp (hC i)
  have hUcover : (⋃ i, range (U i)) =
      {x : E2 | Saddle.toE3 x (-1 - s) ∈ Saddle.shear '' sphere (0 : E3) 1} := by
    ext x
    simp only [mem_ofPred_eq]
    rw [← hmem]
    constructor
    · intro hx
      obtain ⟨i, q, rfl⟩ := mem_iUnion.mp hx
      rw [show F (U i q) = C i q from F.apply_symm_apply _]
      exact hcover.subset (mem_iUnion_of_mem i (mem_range_self q))
    · intro hx
      obtain ⟨i, q, hq⟩ := mem_iUnion.mp (hcover.superset hx)
      exact mem_iUnion.mpr ⟨i, q, by change F.symm (C i q) = x; rw [hq, F.symm_apply_apply]⟩
  obtain ⟨h01, h10⟩ := raw_standard_pair_not_nested hs hsu U hU hUcover
  exact ⟨fun h => h01 (nestedPair_postcomp F.symm h),
    fun h => h10 (nestedPair_postcomp F.symm h)⟩

theorem exists_standard_model_negative_branch_circle_pairs_unnested
    (d : TerminalSaddleGeometry M P p e) (hmodel : d.model = Saddle.shear)
    (hform : ∀ x ∈ e.source, inner Real (M.v : E3) (g (e x)) =
      inner Real (M.v : E3) (g p) - x 0 ^ 2 + x 1 ^ 2) :
    ∃ r δ : Real, 0 < r ∧ closedSquare r ⊆ e.source ∧
      0 < δ ∧ δ < d.eta ∧ δ < r ^ 2 ∧
      ∀ t ∈ Ioc (0 : Real) δ,
        ∃ C : Fin 2 → S1 → E2,
          (∀ i, _root_.Manifold.IsSmoothEmbedding (𝓡 1) (𝓡 2) ∞ (C i)) ∧
          Injective (fun x : Fin 2 × S1 => C x.1 x.2) ∧
          (⋃ i, range (C i)) = d.B (inner Real (M.v : E3) (g p) - t) ∧
          (∀ i s, s ∈ Icc (-hyperbolaRadius r t) (hyperbolaRadius r t) →
            Saddle.toE2 (d.flatten (g (e (negativeLevelArc t i s)))) ∈ range (C i)) ∧
          ¬ NestedPair (C 0) (C 1) ∧ ¬ NestedPair (C 1) (C 0) := by
  obtain ⟨r, δ₀, hr, hrs, hδ₀, hη, hrδ, hpair⟩ :=
    exists_model_negative_branch_circle_pairs d hform
  let δ := min δ₀ (d.scale / 8)
  have hδ : 0 < δ := lt_min hδ₀ (div_pos d.scale_pos (by norm_num))
  have hδle : δ ≤ δ₀ := min_le_left _ _
  refine ⟨r, δ, hr, hrs, hδ, hδle.trans_lt hη, hδle.trans_lt hrδ, ?_⟩
  intro t ht
  obtain ⟨C, hC, hi, hc, hm⟩ := hpair t ⟨ht.1, ht.2.trans hδle⟩
  refine ⟨C, hC, hi, hc, hm, ?_⟩
  apply standard_model_pair_not_nested d hmodel hform ht.1
    (lt_of_le_of_lt (ht.2.trans (min_le_right _ _)) (by linarith [d.scale_pos])) C
    (fun i => (hC i).contMDiff.continuous) hc

end Poincare.Manifold.Schoenflies.PlaneArcs.Terminal
