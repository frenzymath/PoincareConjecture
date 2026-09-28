import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.LevelGraph.Resolution.Hyperbola
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.LevelGraph.Planar.Clearance
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.CirclePair.Connector

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.SaddleLevel

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S1 := sphere (0 : E2) 1
private abbrev S2 := sphere (0 : E3) 1

def positiveLevelConnector (t s : Real) : E2 :=
  WithLp.toLp 2 ![0, (2 * s - 1) * Real.sqrt t]

def negativeLevelConnector (t s : Real) : E2 :=
  saddleCoordinateSwap (positiveLevelConnector t s)

@[simp] theorem positiveLevelConnector_zero_coord (t s : Real) :
    positiveLevelConnector t s 0 = 0 := rfl

@[simp] theorem positiveLevelConnector_one_coord (t s : Real) :
    positiveLevelConnector t s 1 = (2 * s - 1) * Real.sqrt t := rfl

@[simp] theorem positiveLevelConnector_start (t : Real) :
    positiveLevelConnector t 0 = positiveLevelArc t 1 0 := by
  ext i
  fin_cases i <;> simp [positiveLevelConnector, positiveLevelArc]

@[simp] theorem positiveLevelConnector_finish (t : Real) :
    positiveLevelConnector t 1 = positiveLevelArc t 0 0 := by
  ext i
  fin_cases i <;> norm_num [positiveLevelConnector, positiveLevelArc]

@[simp] theorem negativeLevelConnector_start (t : Real) :
    negativeLevelConnector t 0 = negativeLevelArc t 1 0 := by
  simp [negativeLevelConnector, negativeLevelArc]

@[simp] theorem negativeLevelConnector_finish (t : Real) :
    negativeLevelConnector t 1 = negativeLevelArc t 0 0 := by
  simp [negativeLevelConnector, negativeLevelArc]

theorem contDiff_positiveLevelConnector (t : Real) :
    ContDiff Real ∞ (positiveLevelConnector t) := by
  apply (contDiff_piLp 2).mpr
  intro i
  fin_cases i
  · exact contDiff_const
  · exact ((contDiff_const.mul contDiff_id).sub contDiff_const).mul contDiff_const

theorem contDiff_negativeLevelConnector (t : Real) :
    ContDiff Real ∞ (negativeLevelConnector t) :=
  contDiff_saddleCoordinateSwap.comp (contDiff_positiveLevelConnector t)

theorem positiveLevelConnector_injective {t : Real} (ht : 0 < t) :
    Injective (positiveLevelConnector t) := by
  intro s u hsu
  have he := congrArg (fun x : E2 => x 1) hsu
  have hp := Real.sqrt_pos.2 ht
  simp only [positiveLevelConnector_one_coord] at he
  nlinarith

theorem negativeLevelConnector_injective {t : Real} (ht : 0 < t) :
    Injective (negativeLevelConnector t) :=
  saddleCoordinateSwap_injective.comp (positiveLevelConnector_injective ht)

theorem deriv_positiveLevelConnector_one (t s : Real) :
    deriv (positiveLevelConnector t) s 1 = 2 * Real.sqrt t := by
  have hd := (EuclideanSpace.proj (𝕜 := Real) (1 : Fin 2)).hasFDerivAt.comp_hasDerivAt s
    ((contDiff_positiveLevelConnector t).differentiable (by simp) s).hasDerivAt
  change HasDerivAt (fun s : Real => (2 * s - 1) * Real.sqrt t)
    (deriv (positiveLevelConnector t) s 1) s at hd
  have hc : HasDerivAt (fun s : Real => (2 * s - 1) * Real.sqrt t)
      (2 * Real.sqrt t) s := by
    simpa using (((hasDerivAt_id s).const_mul 2).sub_const 1).mul_const (Real.sqrt t)
  exact hd.unique hc

theorem deriv_negativeLevelConnector_zero (t s : Real) :
    deriv (negativeLevelConnector t) s 0 = 2 * Real.sqrt t := by
  have hd := (EuclideanSpace.proj (𝕜 := Real) (0 : Fin 2)).hasFDerivAt.comp_hasDerivAt s
    ((contDiff_negativeLevelConnector t).differentiable (by simp) s).hasDerivAt
  change HasDerivAt (fun s : Real => (2 * s - 1) * Real.sqrt t)
    (deriv (negativeLevelConnector t) s 0) s at hd
  have hc : HasDerivAt (fun s : Real => (2 * s - 1) * Real.sqrt t)
      (2 * Real.sqrt t) s := by
    simpa using (((hasDerivAt_id s).const_mul 2).sub_const 1).mul_const (Real.sqrt t)
  exact hd.unique hc

theorem deriv_positiveLevelConnector_ne_zero {t : Real} (ht : 0 < t) (s : Real) :
    deriv (positiveLevelConnector t) s ≠ 0 := by
  intro he
  have hh := deriv_positiveLevelConnector_one t s
  rw [he] at hh
  have := Real.sqrt_pos.2 ht
  change 0 = 2 * Real.sqrt t at hh
  linarith

theorem deriv_negativeLevelConnector_ne_zero {t : Real} (ht : 0 < t) (s : Real) :
    deriv (negativeLevelConnector t) s ≠ 0 := by
  intro he
  have hh := deriv_negativeLevelConnector_zero t s
  rw [he] at hh
  have := Real.sqrt_pos.2 ht
  change 0 = 2 * Real.sqrt t at hh
  linarith

theorem norm_positiveLevelConnector (t s : Real) :
    ‖positiveLevelConnector t s‖ = |2 * s - 1| * Real.sqrt t := by
  have hs := EuclideanSpace.real_norm_sq_eq (positiveLevelConnector t s)
  simp [Fin.sum_univ_two, positiveLevelConnector] at hs
  change ‖positiveLevelConnector t s‖ ^ 2 = ((2 * s - 1) * Real.sqrt t)^2 at hs
  have hp : 0 ≤ |2 * s - 1| * Real.sqrt t := mul_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)
  have he : (|2 * s - 1| * Real.sqrt t)^2 = ((2 * s - 1) * Real.sqrt t)^2 := by
    rw [mul_pow, sq_abs, ← mul_pow]
  nlinarith [norm_nonneg (positiveLevelConnector t s)]

theorem positiveLevelConnector_norm_le {t s : Real} (hs : s ∈ Icc 0 1) :
    ‖positiveLevelConnector t s‖ ≤ Real.sqrt t := by
  rw [norm_positiveLevelConnector]
  have h : |2 * s - 1| ≤ 1 := abs_le.mpr (by constructor <;> linarith [hs.1, hs.2])
  simpa using mul_le_mul_of_nonneg_right h (Real.sqrt_nonneg t)

theorem norm_negativeLevelConnector (t s : Real) :
    ‖negativeLevelConnector t s‖ = |2 * s - 1| * Real.sqrt t := by
  have hs := EuclideanSpace.real_norm_sq_eq (negativeLevelConnector t s)
  simp [Fin.sum_univ_two, negativeLevelConnector, saddleCoordinateSwap,
    positiveLevelConnector] at hs
  change ‖negativeLevelConnector t s‖ ^ 2 = ((2 * s - 1) * Real.sqrt t)^2 at hs
  have hp : 0 ≤ |2 * s - 1| * Real.sqrt t := mul_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)
  have he : (|2 * s - 1| * Real.sqrt t)^2 = ((2 * s - 1) * Real.sqrt t)^2 := by
    rw [mul_pow, sq_abs, ← mul_pow]
  nlinarith [norm_nonneg (negativeLevelConnector t s)]

theorem negativeLevelConnector_norm_le {t s : Real} (hs : s ∈ Icc 0 1) :
    ‖negativeLevelConnector t s‖ ≤ Real.sqrt t := by
  rw [norm_negativeLevelConnector, ← norm_positiveLevelConnector]
  exact positiveLevelConnector_norm_le hs

theorem positiveLevelConnector_mem_openSquare {r t s : Real}
    (hr : 0 < r) (ht : 0 < t) (htr : t < r^2) (hs : s ∈ Icc 0 1) :
    positiveLevelConnector t s ∈ openSquare r := by
  have hroot : Real.sqrt t < r := by
    nlinarith [Real.sq_sqrt ht.le, Real.sqrt_nonneg t]
  have hle : |(2 * s - 1) * Real.sqrt t| ≤ Real.sqrt t := by
    simpa [norm_positiveLevelConnector, abs_mul, abs_of_nonneg (Real.sqrt_nonneg t)]
      using positiveLevelConnector_norm_le (t := t) hs
  exact ⟨by simpa using hr, hle.trans_lt hroot⟩

theorem negativeLevelConnector_mem_openSquare {r t s : Real}
    (hr : 0 < r) (ht : 0 < t) (htr : t < r^2) (hs : s ∈ Icc 0 1) :
    negativeLevelConnector t s ∈ openSquare r :=
  (saddleCoordinateSwap_mem_openSquare r _).mpr
    (positiveLevelConnector_mem_openSquare hr ht htr hs)

theorem positiveLevelConnector_height_lt {t s : Real} (ht : 0 < t) (hs : s ∈ Ioo 0 1) :
    -(positiveLevelConnector t s 0)^2 + (positiveLevelConnector t s 1)^2 < t := by
  have hroot := Real.sq_sqrt ht.le
  have hsq : (2 * s - 1)^2 < 1 := by nlinarith [hs.1, hs.2]
  simp only [positiveLevelConnector_zero_coord, positiveLevelConnector_one_coord,
    zero_pow (by decide : 2 ≠ 0), neg_zero, zero_add, mul_pow, hroot]
  nlinarith

theorem negativeLevelConnector_height_gt {t s : Real} (ht : 0 < t) (hs : s ∈ Ioo 0 1) :
    -t < -(negativeLevelConnector t s 0)^2 + (negativeLevelConnector t s 1)^2 := by
  have hh := positiveLevelConnector_height_lt ht hs
  change -t < -(positiveLevelConnector t s 1)^2 + (positiveLevelConnector t s 0)^2
  linarith

theorem positiveLevelConnector_disjoint_level {t : Real} (ht : 0 < t) :
    Disjoint (positiveLevelConnector t '' Ioo 0 1)
      {x : E2 | -(x 0)^2 + (x 1)^2 = t} := by
  apply disjoint_left.mpr
  rintro x ⟨s, hs, rfl⟩ he
  exact (ne_of_lt (positiveLevelConnector_height_lt ht hs)) he

theorem negativeLevelConnector_disjoint_level {t : Real} (ht : 0 < t) :
    Disjoint (negativeLevelConnector t '' Ioo 0 1)
      {x : E2 | -(x 0)^2 + (x 1)^2 = -t} := by
  apply disjoint_left.mpr
  rintro x ⟨s, hs, rfl⟩ he
  exact (ne_of_gt (negativeLevelConnector_height_gt ht hs)) he

private theorem connector_graph_height {v : E3} (hv : ‖v‖ = 1)
    (J : E2 ≃ₗᵢ[Real] (Real ∙ v)ᗮ) (x : E2) (t : Real) :
    inner Real v ((J x : E3) + t • v) = t := by
  have h := Submodule.mem_orthogonal_singleton_iff_inner_right.mp (J x).property
  simp [inner_add_right, inner_smul_right, h, hv]

theorem exists_uniform_planar_clearance
    {f : S2 → E3} (hf : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ f)
    {v : E3} (hv : ‖v‖ = 1) (p : S2)
    (e : OpenPartialHomeomorph E2 S2) (hep : e 0 = p)
    {a : Real} (ha : 0 < a) (has : closedBall (0 : E2) a ⊆ e.source)
    (J : E2 ≃ₗᵢ[Real] (Real ∙ v)ᗮ)
    (D : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (hDheight : ∀ y : E3, inner Real v (D y) = inner Real v y)
    (hgraph : ∀ x ∈ closedBall (0 : E2) a,
      D (f (e x)) = (J x : E3) +
        (inner Real v (f p) - x 0 ^ 2 + x 1 ^ 2) • v)
    {ε : Real} (hε : 0 < ε) :
    ∃ r δ : Real, 0 < r ∧ r < ε ∧ 0 < δ ∧
      closedSquare r ⊆ ball (0 : E2) a ∧
      ∀ q : S2, |inner Real v (f q) - inner Real v (f p)| ≤ δ →
        planarProjection J (D (f q)) ∈ closedSquare r →
        q = e (planarProjection J (D (f q))) := by
  let F : S2 → E3 := D ∘ f
  let c := inner Real v (f p)
  have hFi : Topology.IsEmbedding F := D.toHomeomorph.isEmbedding.comp hf.isEmbedding
  have hU : IsOpen (e '' ball (0 : E2) a) :=
    e.isOpen_image_of_subset_source isOpen_ball (ball_subset_closedBall.trans has)
  obtain ⟨V, hV, hFV⟩ := hFi.isInducing.isOpen_iff.mp hU
  have hpV : F p ∈ V := by
    change p ∈ F ⁻¹' V
    rw [hFV]
    exact ⟨0, mem_ball_self ha, hep⟩
  obtain ⟨η, hη, hηV⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds hpV)
  let r := min ε (min a η) / 8
  let δ := η / 4
  have hr : 0 < r := by dsimp [r]; positivity
  have hrε : r < ε := by
    have := min_le_left ε (min a η)
    dsimp [r]
    linarith
  have hra : 2 * r < a := by
    have := (min_le_right ε (min a η)).trans (min_le_left a η)
    dsimp [r]
    linarith
  have hrη : 2 * r + δ < η := by
    have := (min_le_right ε (min a η)).trans (min_le_right a η)
    dsimp [r, δ]
    linarith
  have hrs : closedSquare r ⊆ ball (0 : E2) a := by
    intro x hx
    exact (closedSquare_subset_closedBall hr.le hx).trans_lt hra
  have hproj (x : E2) (hx : x ∈ closedBall (0 : E2) a) :
      planarProjection J (F (e x)) = x := by
    change planarProjection J (D (f (e x))) = x
    rw [hgraph x hx, planarProjection_graph]
  have hcenter : F p = c • v := by
    simpa [F, hep, c] using hgraph 0 (mem_closedBall_self ha.le)
  refine ⟨r, δ, hr, hrε, by dsimp [δ]; positivity, hrs, ?_⟩
  intro q hq hπ
  have hdec : F q = (J (planarProjection J (F q)) : E3) +
      inner Real v (F q) • v := by
    simpa [planarProjection, add_comm] using
      ((Poincare.Geometry.Euclidean.heightCoordinates hv).apply_symm_apply (F q)).symm
  have hdist : dist (F q) (F p) ≤
      ‖planarProjection J (F q)‖ + |inner Real v (f q) - c| := by
    rw [hcenter, dist_eq_norm]
    have hsub : F q - c • v = (J (planarProjection J (F q)) : E3) +
        (inner Real v (f q) - c) • v := by
      nth_rw 1 [hdec]
      rw [show inner Real v (F q) = inner Real v (f q) from hDheight (f q), sub_smul]
      abel
    rw [hsub]
    have hJn : ‖(J (planarProjection J (F q)) : E3)‖ = ‖planarProjection J (F q)‖ :=
      J.norm_map _
    simpa [norm_smul, hv, hJn] using norm_add_le
      (J (planarProjection J (F q)) : E3) ((inner Real v (f q) - c) • v)
  have hnorm := mem_closedBall_zero_iff.mp (closedSquare_subset_closedBall hr.le hπ)
  have hqV : F q ∈ V := hηV (by
    rw [mem_ball]
    exact (hdist.trans (add_le_add hnorm hq)).trans_lt hrη)
  have hlocal : q ∈ e '' ball (0 : E2) a := by
    change q ∈ F ⁻¹' V at hqV
    rwa [hFV] at hqV
  obtain ⟨x, hx, rfl⟩ := hlocal
  change e x = e (planarProjection J (F (e x)))
  rw [hproj x (ball_subset_closedBall hx)]

theorem exists_saddle_level_connectors
    {f : S2 → E3} (hf : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ f)
    {v : E3} (hv : ‖v‖ = 1) (p : S2)
    (e : OpenPartialHomeomorph E2 S2) (hep : e 0 = p)
    {a : Real} (ha : 0 < a) (has : closedBall (0 : E2) a ⊆ e.source)
    (J : E2 ≃ₗᵢ[Real] (Real ∙ v)ᗮ)
    (D : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (hDheight : ∀ y : E3, inner Real v (D y) = inner Real v y)
    (hgraph : ∀ x ∈ closedBall (0 : E2) a,
      D (f (e x)) = (J x : E3) +
        (inner Real v (f p) - x 0 ^ 2 + x 1 ^ 2) • v)
    {ε : Real} (hε : 0 < ε) :
    ∃ r δ : Real, 0 < r ∧ r < ε ∧ 0 < δ ∧ δ < r ^ 2 ∧
      closedSquare r ⊆ ball (0 : E2) a ∧
      ∀ t : Real, 0 < t → t < δ →
        positiveLevelConnector t '' Icc 0 1 ⊆ openSquare r ∧
        negativeLevelConnector t '' Icc 0 1 ⊆ openSquare r ∧
        (∀ s ∈ Icc (0 : Real) 1,
          planarProjection J (D (f (e (positiveLevelConnector t s)))) =
            positiveLevelConnector t s) ∧
        (∀ s ∈ Icc (0 : Real) 1,
          planarProjection J (D (f (e (negativeLevelConnector t s)))) =
            negativeLevelConnector t s) ∧
        Disjoint (positiveLevelConnector t '' Ioo 0 1)
          ((fun q : S2 => planarProjection J (D (f q))) ''
            {q | inner Real v (f q) = inner Real v (f p) + t}) ∧
        Disjoint (negativeLevelConnector t '' Ioo 0 1)
          ((fun q : S2 => planarProjection J (D (f q))) ''
            {q | inner Real v (f q) = inner Real v (f p) - t}) := by
  obtain ⟨r, η, hr, hrε, hη, hrs, hclear⟩ :=
    exists_uniform_planar_clearance hf hv p e hep ha has J D hDheight hgraph hε
  let δ := min η (r^2) / 2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδη : δ < η := by
    have := min_le_left η (r^2)
    dsimp [δ]
    linarith
  have hδr : δ < r^2 := by
    have := min_le_right η (r^2)
    dsimp [δ]
    nlinarith
  have hrc : closedSquare r ⊆ closedBall (0 : E2) a := hrs.trans ball_subset_closedBall
  have hproj (x : E2) (hx : x ∈ closedSquare r) :
      planarProjection J (D (f (e x))) = x := by
    rw [hgraph x (hrc hx), planarProjection_graph]
  have hheight (x : E2) (hx : x ∈ closedSquare r) :
      inner Real v (f (e x)) = inner Real v (f p) - (x 0)^2 + (x 1)^2 := by
    have hh := congrArg (inner Real v) (hgraph x (hrc hx))
    rwa [hDheight, connector_graph_height hv] at hh
  refine ⟨r, δ, hr, hrε, hδ, hδr, hrs, ?_⟩
  intro t ht htδ
  have htr := htδ.trans hδr
  have htη := htδ.trans hδη
  have hpos (s : Real) (hs : s ∈ Icc 0 1) :
      positiveLevelConnector t s ∈ closedSquare r :=
    openSquare_subset_closedSquare r (positiveLevelConnector_mem_openSquare hr ht htr hs)
  have hneg (s : Real) (hs : s ∈ Icc 0 1) :
      negativeLevelConnector t s ∈ closedSquare r :=
    openSquare_subset_closedSquare r (negativeLevelConnector_mem_openSquare hr ht htr hs)
  refine ⟨?_, ?_, (fun s hs => hproj _ (hpos s hs)),
    (fun s hs => hproj _ (hneg s hs)), ?_, ?_⟩
  · rintro x ⟨s, hs, rfl⟩
    exact positiveLevelConnector_mem_openSquare hr ht htr hs
  · rintro x ⟨s, hs, rfl⟩
    exact negativeLevelConnector_mem_openSquare hr ht htr hs
  · apply disjoint_left.mpr
    rintro x ⟨s, hs, rfl⟩ ⟨q, hq, hπ⟩
    dsimp only at hπ
    have hband : |inner Real v (f q) - inner Real v (f p)| ≤ η := by
      change inner Real v (f q) = inner Real v (f p) + t at hq
      rw [hq, add_sub_cancel_left, abs_of_pos ht]
      exact htη.le
    have hqchart := hclear q hband (hπ.symm ▸ hpos s (Ioo_subset_Icc_self hs))
    rw [hπ] at hqchart
    have hh := hheight _ (hpos s (Ioo_subset_Icc_self hs))
    rw [← hqchart] at hh
    have hlt := positiveLevelConnector_height_lt ht hs
    change inner Real v (f q) = inner Real v (f p) + t at hq
    linarith
  · apply disjoint_left.mpr
    rintro x ⟨s, hs, rfl⟩ ⟨q, hq, hπ⟩
    dsimp only at hπ
    have hband : |inner Real v (f q) - inner Real v (f p)| ≤ η := by
      change inner Real v (f q) = inner Real v (f p) - t at hq
      rw [hq, sub_sub_cancel_left, abs_neg, abs_of_pos ht]
      exact htη.le
    have hqchart := hclear q hband (hπ.symm ▸ hneg s (Ioo_subset_Icc_self hs))
    rw [hπ] at hqchart
    have hh := hheight _ (hneg s (Ioo_subset_Icc_self hs))
    rw [← hqchart] at hh
    have hlt := negativeLevelConnector_height_gt ht hs
    change inner Real v (f q) = inner Real v (f p) - t at hq
    linarith

theorem exists_saddle_circle_pair_connector_regions
    {f : S2 → E3} (hf : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ f)
    {v : E3} (hv : ‖v‖ = 1) (p : S2)
    (e : OpenPartialHomeomorph E2 S2) (hep : e 0 = p)
    {a : Real} (ha : 0 < a) (has : closedBall (0 : E2) a ⊆ e.source)
    (J : E2 ≃ₗᵢ[Real] (Real ∙ v)ᗮ)
    (D : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (hDheight : ∀ y : E3, inner Real v (D y) = inner Real v y)
    (hgraph : ∀ x ∈ closedBall (0 : E2) a,
      D (f (e x)) = (J x : E3) +
        (inner Real v (f p) - x 0 ^ 2 + x 1 ^ 2) • v)
    {ε : Real} (hε : 0 < ε) :
    ∃ r δ : Real, 0 < r ∧ r < ε ∧ 0 < δ ∧ δ < r ^ 2 ∧
      ∀ t : Real, 0 < t → t < δ → ∀ positive : Bool,
      ∀ (γ₀ γ₁ : S1 → E2),
        _root_.Manifold.IsSmoothEmbedding (𝓡 1) (𝓡 2) ∞ γ₀ →
        _root_.Manifold.IsSmoothEmbedding (𝓡 1) (𝓡 2) ∞ γ₁ →
        Disjoint (range γ₀) (range γ₁) →
        planarProjection J (D (f (e (if positive then positiveLevelArc t 1 0
          else negativeLevelArc t 1 0)))) ∈ range γ₀ →
        planarProjection J (D (f (e (if positive then positiveLevelArc t 0 0
          else negativeLevelArc t 0 0)))) ∈ range γ₁ →
        range γ₀ ∪ range γ₁ ⊆
          (fun q : S2 => planarProjection J (D (f q))) ''
            {q | inner Real v (f q) = inner Real v (f p) + (if positive then t else -t)} →
        let β := if positive then positiveLevelConnector t else negativeLevelConnector t
        ContDiff Real ∞ β ∧ Injective β ∧ β '' Icc 0 1 ⊆ openSquare r ∧
        β 0 ∈ range γ₀ ∧ β 1 ∈ range γ₁ ∧
        Disjoint (β '' Ioo 0 1) (range γ₀ ∪ range γ₁) ∧
        ∃ A₀ A₁ : Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞,
          A₀ '' sphere (0 : E2) 1 = range γ₀ ∧
          A₁ '' sphere (0 : E2) 1 = range γ₁ ∧
          let K₀ := A₀ '' closedBall (0 : E2) 1
          let K₁ := A₁ '' closedBall (0 : E2) 1
          let U₀ := A₀ '' ball (0 : E2) 1
          let U₁ := A₁ '' ball (0 : E2) 1
          (Disjoint K₀ K₁ ∧ β '' Ioo 0 1 ⊆ (K₀ ∪ K₁)ᶜ) ∨
          (K₁ ⊆ U₀ ∧ β '' Ioo 0 1 ⊆ U₀ \ K₁) ∨
          (K₀ ⊆ U₁ ∧ β '' Ioo 0 1 ⊆ U₁ \ K₀) := by
  obtain ⟨r, δ, hr, hrε, hδ, hδr, _, hconnect⟩ :=
    exists_saddle_level_connectors hf hv p e hep ha has J D hDheight hgraph hε
  refine ⟨r, δ, hr, hrε, hδ, hδr, ?_⟩
  intro t ht htδ positive γ₀ γ₁ hγ₀ hγ₁ hdisjoint hstart hfinish hcircles
  obtain ⟨hpos, hneg, hposπ, hnegπ, hposavoid, hnegavoid⟩ := hconnect t ht htδ
  let β := if positive then positiveLevelConnector t else negativeLevelConnector t
  have hβ : ContDiff Real ∞ β := by
    cases positive
    · exact contDiff_negativeLevelConnector t
    · exact contDiff_positiveLevelConnector t
  have hβinj : Injective β := by
    cases positive
    · exact negativeLevelConnector_injective ht
    · exact positiveLevelConnector_injective ht
  have hβsq : β '' Icc 0 1 ⊆ openSquare r := by
    cases positive
    · exact hneg
    · exact hpos
  have hβπ : ∀ s ∈ Icc (0 : Real) 1,
      planarProjection J (D (f (e (β s)))) = β s := by
    cases positive
    · exact hnegπ
    · exact hposπ
  have hβstart : β 0 = if positive then positiveLevelArc t 1 0
      else negativeLevelArc t 1 0 := by
    cases positive <;> simp [β]
  have hβfinish : β 1 = if positive then positiveLevelArc t 0 0
      else negativeLevelArc t 0 0 := by
    cases positive <;> simp [β]
  have hβ₀ : β 0 ∈ range γ₀ := by
    rw [← hβπ 0 (by simp)]
    simpa only [hβstart] using hstart
  have hβ₁ : β 1 ∈ range γ₁ := by
    rw [← hβπ 1 (by simp)]
    simpa only [hβfinish] using hfinish
  have hβavoid : Disjoint (β '' Ioo 0 1) (range γ₀ ∪ range γ₁) := by
    apply Disjoint.mono_right hcircles
    cases positive
    · simpa only [β, Bool.false_eq_true, ↓reduceIte, sub_eq_add_neg] using hnegavoid
    · simpa only [β, ↓reduceIte] using hposavoid
  exact ⟨hβ, hβinj, hβsq, hβ₀, hβ₁, hβavoid,
    exists_filled_planar_circle_pair_with_connector_region γ₀ γ₁ hγ₀ hγ₁ hdisjoint
      β hβ.continuous.continuousOn hβ₀ hβ₁ hβavoid⟩

end Poincare.Manifold.Schoenflies.SaddleLevel
