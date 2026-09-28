import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Isotopy.Arcs.Terminal.PhysicalModelChart

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies.PlaneArcs.Terminal

open SaddleLevel Poincare.Geometry.Manifold

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S1 := sphere (0 : E2) 1
private abbrev S2 := sphere (0 : E3) 1

private theorem model_projection_smooth : ContDiff Real ∞ Saddle.toE2 := by
  apply (contDiff_piLp 2).mpr
  intro i
  fin_cases i
  · exact (EuclideanSpace.proj (𝕜 := Real) (0 : Fin 3)).contDiff
  · exact (EuclideanSpace.proj (𝕜 := Real) (1 : Fin 3)).contDiff

private theorem model_lift_smooth (z : Real) :
    ContDiff Real ∞ (fun x => Saddle.toE3 x z) := by
  apply (contDiff_piLp 2).mpr
  intro i
  fin_cases i
  · exact (EuclideanSpace.proj (𝕜 := Real) (0 : Fin 2)).contDiff
  · exact (EuclideanSpace.proj (𝕜 := Real) (1 : Fin 2)).contDiff
  · exact contDiff_const

theorem exists_source_circle_of_planar_model_circle
    (G : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞) (z : Real)
    (β : S1 → E2) (hβ : _root_.Manifold.IsSmoothEmbedding (𝓡 1) (𝓡 2) ∞ β)
    (hmem : ∀ q, Saddle.toE3 (β q) z ∈ G '' sphere (0 : E3) 1) :
    ∃ C : S1 → S2,
      ContMDiff (𝓡 1) (𝓡 2) ∞ C ∧ Injective C ∧
      (∀ q, Injective (mfderiv (𝓡 1) (𝓡 2) C q)) ∧
      ∀ q, G (C q) = Saddle.toE3 (β q) z := by
  have hsource (q : S1) : G.symm (Saddle.toE3 (β q) z) ∈ sphere (0 : E3) 1 := by
    obtain ⟨x, hx, heq⟩ := hmem q
    rw [← heq, G.symm_apply_apply]
    exact hx
  let C : S1 → S2 := fun q => ⟨G.symm (Saddle.toE3 (β q) z), hsource q⟩
  have hC : ContMDiff (𝓡 1) (𝓡 2) ∞ C :=
    (G.symm.contMDiff.comp ((model_lift_smooth z).contMDiff.comp hβ.contMDiff)).codRestrict_sphere
      hsource
  let L : S2 → E2 := fun q => Saddle.toE2 (G q)
  have hL : ContMDiff (𝓡 2) (𝓡 2) ∞ L := model_projection_smooth.contMDiff.comp
    (G.contMDiff.comp (contMDiff_coe_sphere (n := 2)))
  have hLC : L ∘ C = β := by
    funext q
    change Saddle.toE2 (G (G.symm (Saddle.toE3 (β q) z))) = β q
    rw [G.apply_symm_apply]
    ext i
    fin_cases i <;> rfl
  refine ⟨C, hC, ?_, ?_, ?_⟩
  · intro q r hqr
    apply hβ.isEmbedding.injective
    rw [← hLC]
    exact congrArg L hqr
  · intro q
    have hd := (hβ.isImmersion.isImmersionAt q).injective_mfderiv_modelWithCornersSelf
      (by simp)
    rw [← hLC, mfderiv_comp q (hL.mdifferentiable (by simp) (C q))
      (hC.mdifferentiable (by simp) q)] at hd
    intro a b hab
    exact hd (congrArg (mfderiv (𝓡 2) (𝓡 2) L (C q)) hab)
  · intro q
    exact G.apply_symm_apply _

variable {f : S2 → E3} {M : SphereMorseReduction f} {g : S2 → E3}
  {P : SphereSurgeryPath (M.v : E3) (fun q => M.D (f q)) g}
  {p : S2} {e : OpenPartialHomeomorph E2 S2}

private theorem sphere_coordinates (q : S2) :
    (q : E3) 0 ^ 2 + (q : E3) 1 ^ 2 + (q : E3) 2 ^ 2 = 1 := by
  have hn := EuclideanSpace.norm_sq_eq (q : E3)
  simpa [Fin.sum_univ_three, Real.norm_eq_abs, sq_abs] using hn.symm

private theorem standard_lower_separator {q : S2} (hq : Saddle.height q < -1) :
    (q : E3) 0 ≠ 0 := by
  intro hx
  rw [Saddle.height_apply, hx] at hq
  nlinarith [sphere_coordinates q, sq_nonneg ((q : E3) 1)]

private theorem standard_lower_signed_points {s : Real} (hs : 0 < s) (hsu : s < 1 / 4) :
    (∃ q : S2, Saddle.height q = -1 - s ∧ (q : E3) 0 < 0) ∧
    (∃ q : S2, Saddle.height q = -1 - s ∧ 0 < (q : E3) 0) := by
  let X := Real.sqrt (1 / 2 + s)
  let Y := Real.sqrt (1 / 4 - s)
  have hX : 0 < X := Real.sqrt_pos.mpr (by linarith)
  have hXsq : X ^ 2 = 1 / 2 + s := Real.sq_sqrt (by linarith)
  have hYsq : Y ^ 2 = 1 / 4 - s := Real.sq_sqrt (by linarith)
  have hmem (σ : Real) (hσ : σ ^ 2 = 1) :
      (WithLp.toLp 2 ![σ * X, Y, -1 / 2] : E3) ∈ sphere (0 : E3) 1 := by
    rw [mem_sphere_zero_iff_norm, ← sq_eq_sq₀ (norm_nonneg _) zero_le_one,
      EuclideanSpace.norm_sq_eq]
    simp only [Fin.sum_univ_three, Real.norm_eq_abs, sq_abs]
    change (σ * X) ^ 2 + Y ^ 2 + (-1 / 2 : Real) ^ 2 = 1 ^ 2
    rw [mul_pow, hσ, one_mul, hXsq, hYsq]
    ring
  constructor
  · refine ⟨⟨WithLp.toLp 2 ![-1 * X, Y, -1 / 2], hmem (-1) (by norm_num)⟩, ?_, ?_⟩
    · rw [Saddle.height_apply]
      change -1 / 2 - (-1 * X) ^ 2 = -1 - s
      nlinarith
    · change -1 * X < 0
      linarith
  · refine ⟨⟨WithLp.toLp 2 ![1 * X, Y, -1 / 2], hmem 1 (by norm_num)⟩, ?_, ?_⟩
    · rw [Saddle.height_apply]
      change -1 / 2 - (1 * X) ^ 2 = -1 - s
      nlinarith
    · change 0 < 1 * X
      linarith

private theorem nested_lower_separator {p q : S2}
    (hp : mfderiv (𝓡 2) 𝓘(Real, Real) Saddle.Nested.height p = 0)
    (hpz : (p : E3) 2 ∈ Ioo (3 / 5 : Real) (5 / 8))
    (hq : Saddle.Nested.height q < Saddle.Nested.height p) :
    (q : E3) 2 - (p : E3) 2 ≠ 0 := by
  intro hz
  have hz' : (q : E3) 2 = (p : E3) 2 := sub_eq_zero.mp hz
  obtain ⟨hpy, hpc⟩ := Saddle.Nested.critical_point_coordinates hp
  have hpx : (p : E3) 0 < 0 := by
    by_contra hn
    have hm := mul_nonneg (le_of_not_gt hn) (show 0 ≤ 2 * (p : E3) 2 - 1 by linarith [hpz.1])
    nlinarith [hpz.1]
  have hnormp := sphere_coordinates p
  have hnormq := sphere_coordinates q
  rw [hpy] at hnormp
  rw [hz'] at hnormq
  have hqx : (p : E3) 0 ≤ (q : E3) 0 := by
    by_contra hn
    have hlt := lt_of_not_ge hn
    have hprod := mul_pos (show 0 < (p : E3) 0 - (q : E3) 0 by linarith)
      (show 0 < -((p : E3) 0 + (q : E3) 0) by linarith)
    nlinarith [sq_nonneg ((q : E3) 1)]
  rw [Saddle.Nested.height_apply, Saddle.Nested.height_apply, hz', hpy] at hq
  nlinarith

private theorem nested_lower_signed_points {p : S2}
    (hp : mfderiv (𝓡 2) 𝓘(Real, Real) Saddle.Nested.height p = 0)
    (hpz : (p : E3) 2 ∈ Ioo (3 / 5 : Real) (5 / 8))
    {b : Real} (hb : 1 < b) (hbp : b < Saddle.Nested.height p) :
    (∃ q : S2, Saddle.Nested.height q = b ∧ (q : E3) 2 - (p : E3) 2 < 0) ∧
    (∃ q : S2, Saddle.Nested.height q = b ∧ 0 < (q : E3) 2 - (p : E3) 2) := by
  let H : Real → Real := fun z => 1 + z - z ^ 2 - (3 / 10) * Real.sqrt (1 - z ^ 2)
  have hH : Continuous H := by dsimp [H]; fun_prop
  obtain ⟨hpy, hpc⟩ := Saddle.Nested.critical_point_coordinates hp
  have hpx : (p : E3) 0 < 0 := by
    by_contra hn
    have hm := mul_nonneg (le_of_not_gt hn) (show 0 ≤ 2 * (p : E3) 2 - 1 by linarith [hpz.1])
    nlinarith [hpz.1]
  have hnormp := sphere_coordinates p
  rw [hpy] at hnormp
  have hroot : Real.sqrt (1 - (p : E3) 2 ^ 2) = -(p : E3) 0 := by
    rw [show 1 - (p : E3) 2 ^ 2 = (p : E3) 0 ^ 2 by nlinarith,
      Real.sqrt_sq_eq_abs, abs_of_neg hpx]
  have hcenter : H ((p : E3) 2) = Saddle.Nested.height p := by
    rw [Saddle.Nested.height_apply, hpy]
    dsimp [H]
    rw [hroot]
    nlinarith
  have hleft : H (-1) = -1 := by norm_num [H]
  have hright : H 1 = 1 := by norm_num [H]
  have hpoint (z : Real) (hz : z ∈ Icc (-1 : Real) 1) :
      ∃ q : S2, (q : E3) 2 = z ∧ Saddle.Nested.height q = H z := by
    have hzs : 0 ≤ 1 - z ^ 2 := by nlinarith [hz.1, hz.2]
    have hr := Real.sq_sqrt hzs
    have hmem : (WithLp.toLp 2 ![-Real.sqrt (1 - z ^ 2), 0, z] : E3) ∈ sphere (0 : E3) 1 := by
      rw [mem_sphere_zero_iff_norm, ← sq_eq_sq₀ (norm_nonneg _) zero_le_one,
        EuclideanSpace.norm_sq_eq]
      simp only [Fin.sum_univ_three, Real.norm_eq_abs, sq_abs]
      change (-Real.sqrt (1 - z ^ 2)) ^ 2 + 0 ^ 2 + z ^ 2 = 1 ^ 2
      nlinarith
    refine ⟨⟨WithLp.toLp 2 ![-Real.sqrt (1 - z ^ 2), 0, z], hmem⟩, rfl, ?_⟩
    rw [Saddle.Nested.height_apply]
    change z + (-Real.sqrt (1 - z ^ 2)) ^ 2 + 0 ^ 2 + (3 / 10) * -Real.sqrt (1 - z ^ 2) = H z
    dsimp [H]
    nlinarith
  obtain ⟨z₀, hz₀, he₀⟩ := intermediate_value_Icc
    (show (-1 : Real) ≤ (p : E3) 2 by linarith [hpz.1]) hH.continuousOn
    (show b ∈ Icc (H (-1)) (H ((p : E3) 2)) by rw [hleft, hcenter]; exact ⟨by linarith, hbp.le⟩)
  obtain ⟨z₁, hz₁, he₁⟩ := intermediate_value_Icc'
    (show (p : E3) 2 ≤ 1 by linarith [hpz.2]) hH.continuousOn
    (show b ∈ Icc (H 1) (H ((p : E3) 2)) by rw [hright, hcenter]; exact ⟨hb.le, hbp.le⟩)
  obtain ⟨q₀, hq₀z, hq₀⟩ := hpoint z₀ ⟨hz₀.1, hz₀.2.trans (by linarith [hpz.2])⟩
  obtain ⟨q₁, hq₁z, hq₁⟩ := hpoint z₁ ⟨(show (-1 : Real) ≤ (p : E3) 2 by linarith [hpz.1]).trans hz₁.1, hz₁.2⟩
  refine ⟨⟨q₀, hq₀.trans he₀, ?_⟩, ⟨q₁, hq₁.trans he₁, ?_⟩⟩
  · rw [hq₀z]
    have hne : z₀ ≠ (p : E3) 2 := by intro he; rw [he, hcenter] at he₀; linarith
    exact sub_neg.mpr (lt_of_le_of_ne hz₀.2 hne)
  · rw [hq₁z]
    have hne : z₁ ≠ (p : E3) 2 := by intro he; rw [he, hcenter] at he₁; linarith
    exact sub_pos.mpr (lt_of_le_of_ne hz₁.1 hne.symm)

theorem exists_model_lower_level_separator
    (d : TerminalSaddleGeometry M P p e)
    (hform : ∀ x ∈ e.source, inner Real (M.v : E3) (g (e x)) =
      inner Real (M.v : E3) (g p) - x 0 ^ 2 + x 1 ^ 2) :
    ∃ ε : Real, 0 < ε ∧ ∃ l : S2 → Real, Continuous l ∧
      (∀ q : S2, inner Real (M.v : E3) (d.filledModel q) <
        inner Real (M.v : E3) (g p) → l q ≠ 0) ∧
      ∀ t ∈ Ioc (0 : Real) ε,
        (∃ q : S2, inner Real (M.v : E3) (d.filledModel q) =
          inner Real (M.v : E3) (g p) - t ∧ l q < 0) ∧
        (∃ q : S2, inner Real (M.v : E3) (d.filledModel q) =
          inner Real (M.v : E3) (g p) - t ∧ 0 < l q) := by
  have hheight (q : S2) : inner Real (M.v : E3) (d.filledModel q) =
      inner Real (M.v : E3) (g p) + d.scale * (d.model q 2 - d.model (d.modelChart 0) 2) :=
    d.transport_height _
  rcases d.model_kind with hmodel | hmodel
  · refine ⟨d.scale / 8, div_pos d.scale_pos (by norm_num), fun q => (q : E3) 0, by fun_prop, ?_, ?_⟩
    have hc := terminal_standard_model_chart_center d hmodel hform
    · intro q hq
      have ht := hheight q
      rw [hmodel, hc] at ht
      change inner Real (M.v : E3) (d.filledModel q) =
        inner Real (M.v : E3) (g p) + d.scale * (Saddle.height q - Saddle.height Saddle.saddlePoint) at ht
      rw [Saddle.height_saddlePoint] at ht
      apply standard_lower_separator
      nlinarith [d.scale_pos]
    · intro t ht
      have hc := terminal_standard_model_chart_center d hmodel hform
      have hs : 0 < t / d.scale := div_pos ht.1 d.scale_pos
      have hsu : t / d.scale < 1 / 4 := (div_lt_iff₀ d.scale_pos).mpr (by linarith [ht.2, d.scale_pos])
      have heq (q : S2) (hq : Saddle.height q = -1 - t / d.scale) :
          inner Real (M.v : E3) (d.filledModel q) = inner Real (M.v : E3) (g p) - t := by
        rw [hheight, hmodel, hc]
        change _ + d.scale * (Saddle.height q - Saddle.height Saddle.saddlePoint) = _
        rw [hq, Saddle.height_saddlePoint]
        field_simp [d.scale_pos.ne']
        ring
      obtain ⟨⟨q₀, hq₀, hs₀⟩, ⟨q₁, hq₁, hs₁⟩⟩ := standard_lower_signed_points hs hsu
      exact ⟨⟨q₀, heq q₀ hq₀, hs₀⟩, ⟨q₁, heq q₁ hq₁, hs₁⟩⟩
  · have hc := terminal_model_chart_critical d hform
    rw [hmodel] at hc
    have hz := terminal_nested_model_chart_latitude d hmodel hform
    have hcenter : 1 < Saddle.Nested.height (d.modelChart 0) := by
      have hband := terminal_nested_model_chart_in_retainedBand d hmodel hform
      apply lt_of_le_of_ne hband.1
      intro he
      exact Saddle.Nested.height_one_regular _ he.symm hc
    refine ⟨d.scale * (Saddle.Nested.height (d.modelChart 0) - 1) / 2,
      div_pos (mul_pos d.scale_pos (sub_pos.mpr hcenter)) (by norm_num),
      fun q => (q : E3) 2 - (d.modelChart 0 : E3) 2, by fun_prop, ?_, ?_⟩
    · intro q hq
      have ht := hheight q
      apply nested_lower_separator hc hz
      rw [hmodel] at ht
      change inner Real (M.v : E3) (d.filledModel q) =
        inner Real (M.v : E3) (g p) + d.scale * (Saddle.Nested.height q - Saddle.Nested.height (d.modelChart 0)) at ht
      nlinarith [d.scale_pos]
    · intro t ht
      have hs : 0 < t / d.scale := div_pos ht.1 d.scale_pos
      have hsu : t / d.scale < Saddle.Nested.height (d.modelChart 0) - 1 :=
        (div_lt_iff₀ d.scale_pos).mpr (by nlinarith [ht.2, mul_pos d.scale_pos (sub_pos.mpr hcenter)])
      obtain ⟨⟨q₀, hq₀, hs₀⟩, ⟨q₁, hq₁, hs₁⟩⟩ := nested_lower_signed_points hc hz
        (b := Saddle.Nested.height (d.modelChart 0) - t / d.scale) (by linarith) (by linarith)
      have heq (q : S2) (hq : Saddle.Nested.height q = Saddle.Nested.height (d.modelChart 0) - t / d.scale) :
          inner Real (M.v : E3) (d.filledModel q) = inner Real (M.v : E3) (g p) - t := by
        rw [hheight, hmodel]
        change _ + d.scale * (Saddle.Nested.height q - Saddle.Nested.height (d.modelChart 0)) = _
        rw [hq]
        field_simp [d.scale_pos.ne']
        ring
      exact ⟨⟨q₀, heq q₀ hq₀, hs₀⟩, ⟨q₁, heq q₁ hq₁, hs₁⟩⟩

theorem exists_model_lower_source_circle_pair
    (d : TerminalSaddleGeometry M P p e)
    (hform : ∀ x ∈ e.source, inner Real (M.v : E3) (g (e x)) =
      inner Real (M.v : E3) (g p) - x 0 ^ 2 + x 1 ^ 2) :
    ∃ ε : Real, 0 < ε ∧ ∀ t ∈ Ioc (0 : Real) ε,
      ∃ C : Fin 2 → S1 → S2,
        (∀ i, ContMDiff (𝓡 1) (𝓡 2) ∞ (C i)) ∧
        (∀ i q, Injective (mfderiv (𝓡 1) (𝓡 2) (C i) q)) ∧
        Injective (fun x : Fin 2 × S1 => C x.1 x.2) ∧
        {q : S2 | inner Real (M.v : E3) (d.filledModel q) =
          inner Real (M.v : E3) (g p) - t} = range (C 0) ∪ range (C 1) := by
  obtain ⟨ε, hε, hcircles⟩ := exists_model_lower_slice_circle_pair d hform
  refine ⟨ε, hε, ?_⟩
  intro t ht
  obtain ⟨β, hβ, hβinj, hcover⟩ := hcircles (-t) ⟨by linarith [ht.2], by linarith [ht.1]⟩
  let z := inner Real (M.v : E3) (g p) - t
  let G := d.filledModel.trans d.flatten
  have hheight (q : S2) : G q 2 = inner Real (M.v : E3) (d.filledModel q) := by
    change d.frame (d.D (d.filledModel q)) 2 = _
    rw [d.frame_height, d.D_height]
  have hmem (i : Fin 2) (q : S1) : Saddle.toE3 (β i q) z ∈ G '' sphere (0 : E3) 1 := by
    have hq := hcover.subset (mem_iUnion_of_mem i (mem_range_self q))
    obtain ⟨_, ⟨y, hy, rfl⟩, heq⟩ := hq
    refine ⟨y, hy, ?_⟩
    change d.flatten (d.filledModel y) = Saddle.toE3 (β i q) (_ - t)
    simpa only [sub_eq_add_neg] using heq
  choose C hC hCi hCd hlift using fun i => exists_source_circle_of_planar_model_circle G z (β i) (hβ i) (hmem i)
  have hproject (i : Fin 2) (q : S1) : Saddle.toE2 (G (C i q)) = β i q := by
    rw [hlift]
    ext j
    fin_cases j <;> rfl
  refine ⟨C, hC, hCd, ?_, ?_⟩
  · intro x y hxy
    apply hβinj
    change β x.1 x.2 = β y.1 y.2
    rw [← hproject, ← hproject]
    exact congrArg (fun q : S2 => Saddle.toE2 (G q)) hxy
  · ext q
    constructor
    · intro hq
      have hqheight : G q 2 = z := (hheight q).trans hq
      have hcoords : G q = Saddle.toE3 (Saddle.toE2 (G q)) z := by
        ext j
        fin_cases j <;> simp_all [Saddle.toE2, Saddle.toE3]
      have hqB : Saddle.toE2 (G q) ∈ d.B (inner Real (M.v : E3) (g p) + -t) := by
        refine ⟨d.filledModel q, ⟨q, q.property, rfl⟩, ?_⟩
        change G q = Saddle.toE3 (Saddle.toE2 (G q)) (_ + -t)
        simpa only [z, sub_eq_add_neg] using hcoords
      obtain ⟨i, u, hu⟩ := mem_iUnion.mp (hcover.symm.subset hqB)
      have hqu : C i u = q := by
        apply Subtype.ext
        apply G.injective
        change G (C i u) = G q
        rw [hlift, hu, ← hcoords]
      fin_cases i
      · exact Or.inl ⟨u, hqu⟩
      · exact Or.inr ⟨u, hqu⟩
    · rintro (⟨u, rfl⟩ | ⟨u, rfl⟩)
      · exact (hheight _).symm.trans (congrArg (fun y : E3 => y 2) (hlift 0 u))
      · exact (hheight _).symm.trans (congrArg (fun y : E3 => y 2) (hlift 1 u))

private theorem circle_separator_sign (C : S1 → S2) (hC : Continuous C)
    (l : S2 → Real) (hl : Continuous l) (hne : ∀ q, l (C q) ≠ 0) :
    (∀ q, l (C q) < 0) ∨ (∀ q, 0 < l (C q)) := by
  let : ConnectedSpace S1 := isConnected_iff_connectedSpace.mp
    (isConnected_sphere (by simp [← Module.finrank_eq_rank, E2]) (0 : E2) zero_le_one)
  have hconn := isPreconnected_range (hl.comp hC)
  have hparts := isPreconnected_iff_subset_of_disjoint_closed.mp hconn
    (Iic (0 : Real)) (Ici (0 : Real)) isClosed_Iic isClosed_Ici
    (fun x _ => le_total x 0) (by
      rw [eq_empty_iff_forall_notMem]
      rintro x ⟨⟨q, rfl⟩, hle, hge⟩
      exact hne q (le_antisymm hle hge))
  rcases hparts with hneg | hpos
  · exact Or.inl (fun q => lt_of_le_of_ne (hneg (mem_range_self q)) (hne q))
  · exact Or.inr (fun q => lt_of_le_of_ne (hpos (mem_range_self q)) (hne q).symm)

theorem exists_model_lower_separated_source_circle_pair
    (d : TerminalSaddleGeometry M P p e)
    (hform : ∀ x ∈ e.source, inner Real (M.v : E3) (g (e x)) =
      inner Real (M.v : E3) (g p) - x 0 ^ 2 + x 1 ^ 2) :
    ∃ ε : Real, 0 < ε ∧ ∀ t ∈ Ioc (0 : Real) ε,
      ∃ (C : Fin 2 → S1 → S2) (l : S2 → Real),
        (∀ i, ContMDiff (𝓡 1) (𝓡 2) ∞ (C i)) ∧
        (∀ i, Injective (C i)) ∧
        (∀ i q, Injective (mfderiv (𝓡 1) (𝓡 2) (C i) q)) ∧
        {q : S2 | inner Real (M.v : E3) (d.filledModel q) =
          inner Real (M.v : E3) (g p) - t} = range (C 0) ∪ range (C 1) ∧
        Continuous l ∧
        (∀ q : S2, inner Real (M.v : E3) (d.filledModel q) ≤
          inner Real (M.v : E3) (g p) - t → l q ≠ 0) ∧
        (∀ q, l (C 0 q) < 0) ∧ (∀ q, 0 < l (C 1 q)) := by
  obtain ⟨ε₀, hε₀, hcircles⟩ := exists_model_lower_source_circle_pair d hform
  obtain ⟨ε₁, hε₁, l, hl, hnonzero, hpoints⟩ := exists_model_lower_level_separator d hform
  refine ⟨min ε₀ ε₁, lt_min hε₀ hε₁, ?_⟩
  intro t ht
  obtain ⟨C, hC, hCd, hCi, hlevel⟩ := hcircles t ⟨ht.1, ht.2.trans (min_le_left _ _)⟩
  obtain ⟨⟨q₀, hq₀, hl₀⟩, ⟨q₁, hq₁, hl₁⟩⟩ := hpoints t ⟨ht.1, ht.2.trans (min_le_right _ _)⟩
  have hi (i : Fin 2) : Injective (C i) := by
    intro q r hqr
    exact congrArg Prod.snd (hCi (show C (i, q).1 (i, q).2 = C (i, r).1 (i, r).2 from hqr))
  have hzero (q : S2) (hq : inner Real (M.v : E3) (d.filledModel q) ≤
      inner Real (M.v : E3) (g p) - t) : l q ≠ 0 := hnonzero q (by linarith [ht.1])
  have hClevel (i : Fin 2) (q : S1) : inner Real (M.v : E3) (d.filledModel (C i q)) =
      inner Real (M.v : E3) (g p) - t := by
    apply hlevel.superset
    fin_cases i
    · exact Or.inl (mem_range_self q)
    · exact Or.inr (mem_range_self q)
  have hsign (i : Fin 2) := circle_separator_sign (C i) (hC i).continuous l hl
    (fun q => hzero _ (hClevel i q).le)
  have hnneg : ¬ ((∀ q, l (C 0 q) < 0) ∧ (∀ q, l (C 1 q) < 0)) := by
    rintro ⟨h₀, h₁⟩
    rcases hlevel.subset hq₁ with ⟨q, rfl⟩ | ⟨q, rfl⟩
    · linarith [h₀ q]
    · linarith [h₁ q]
  have hnpos : ¬ ((∀ q, 0 < l (C 0 q)) ∧ (∀ q, 0 < l (C 1 q))) := by
    rintro ⟨h₀, h₁⟩
    rcases hlevel.subset hq₀ with ⟨q, rfl⟩ | ⟨q, rfl⟩
    · linarith [h₀ q]
    · linarith [h₁ q]
  rcases hsign 0 with h₀ | h₀
  · have h₁ := (hsign 1).resolve_left (fun h₁ => hnneg ⟨h₀, h₁⟩)
    exact ⟨C, l, hC, hi, hCd, hlevel, hl, hzero, h₀, h₁⟩
  · have h₁ := (hsign 1).resolve_right (fun h₁ => hnpos ⟨h₀, h₁⟩)
    refine ⟨![C 1, C 0], l, ?_, ?_, ?_, ?_, hl, hzero, h₁, h₀⟩
    · intro i
      fin_cases i <;> exact hC _
    · intro i
      fin_cases i <;> exact hi _
    · intro i q
      fin_cases i <;> exact hCd _ q
    · simpa only [Matrix.cons_val_zero, Matrix.cons_val_one, union_comm] using hlevel

end Poincare.Manifold.Schoenflies.PlaneArcs.Terminal
