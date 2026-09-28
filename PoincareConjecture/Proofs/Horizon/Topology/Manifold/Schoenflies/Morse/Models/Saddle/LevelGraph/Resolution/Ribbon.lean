import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.LevelGraph.Resolution.Connector



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

private theorem isPreconnected_ribbon_parameters (r : Real) :
    IsPreconnected {z : E2 | |z 0| ≤ r / 2 ∧ z 1 ∈ Ioo 0 1} := by
  have he : {z : E2 | |z 0| ≤ r / 2 ∧ z 1 ∈ Ioo 0 1} =
      ((EuclideanSpace.proj (𝕜 := Real) (0 : Fin 2)) ⁻¹' Icc (-(r / 2)) (r / 2)) ∩
      ((EuclideanSpace.proj (𝕜 := Real) (1 : Fin 2)) ⁻¹' Ioo (0 : Real) 1) := by
    ext z
    change (|z 0| ≤ r / 2 ∧ z 1 ∈ Ioo 0 1) ↔
      (z 0 ∈ Icc (-(r / 2)) (r / 2) ∧ z 1 ∈ Ioo 0 1)
    simp only [mem_Icc, abs_le]
  have hconv : Convex Real {z : E2 | |z 0| ≤ r / 2 ∧ z 1 ∈ Ioo 0 1} := by
    rw [he]
    exact ((convex_Icc (-(r / 2)) (r / 2)).linear_preimage
      (EuclideanSpace.proj (𝕜 := Real) (0 : Fin 2)).toLinearMap).inter
      ((convex_Ioo (0 : Real) 1).linear_preimage
        (EuclideanSpace.proj (𝕜 := Real) (1 : Fin 2)).toLinearMap)
  exact hconv.isPreconnected

private theorem preconnected_region_subset
    {S K : Set E2} (hS : IsPreconnected S) (hK : IsClosed K)
    (havoid : Disjoint S (frontier K)) :
    S ⊆ interior K ∨ S ⊆ Kᶜ := by
  apply hS.subset_or_subset isOpen_interior hK.isOpen_compl
    (disjoint_left.mpr fun _ hx hy => hy (interior_subset hx))
  intro x hx
  by_cases hin : x ∈ interior K
  · exact Or.inl hin
  · right
    intro hxK
    exact disjoint_left.mp havoid hx (by rw [hK.frontier_eq]; exact ⟨hxK, hin⟩)

private theorem preconnected_region_subset_interior
    {S K : Set E2} (hS : IsPreconnected S) (hK : IsClosed K)
    (havoid : Disjoint S (frontier K)) {x : E2} (hx : x ∈ S) (hxK : x ∈ interior K) :
    S ⊆ interior K := by
  rcases preconnected_region_subset hS hK havoid with h | h
  · exact h
  · exact (h hx (interior_subset hxK)).elim

private theorem preconnected_region_subset_compl
    {S K : Set E2} (hS : IsPreconnected S) (hK : IsClosed K)
    (havoid : Disjoint S (frontier K)) {x : E2} (hx : x ∈ S) (hxK : x ∉ K) :
    S ⊆ Kᶜ := by
  rcases preconnected_region_subset hS hK havoid with h | h
  · exact (hxK (interior_subset (h hx))).elim
  · exact h

private theorem exists_filled_planar_circle_pair_with_ribbon_region
    (γ₀ γ₁ : S1 → E2)
    (hγ₀ : _root_.Manifold.IsSmoothEmbedding (𝓡 1) (𝓡 2) ∞ γ₀)
    (hγ₁ : _root_.Manifold.IsSmoothEmbedding (𝓡 1) (𝓡 2) ∞ γ₁)
    (hdisjoint : Disjoint (range γ₀) (range γ₁))
    (β : Real → E2) (hβ : ContinuousOn β (Icc 0 1))
    (hβ₀ : β 0 ∈ range γ₀) (hβ₁ : β 1 ∈ range γ₁)
    (S : Set E2) (hS : IsPreconnected S) (hβS : β '' Ioo 0 1 ⊆ S)
    (havoid : Disjoint S (range γ₀ ∪ range γ₁)) :
    ∃ A₀ A₁ : Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞,
      A₀ '' sphere (0 : E2) 1 = range γ₀ ∧
      A₁ '' sphere (0 : E2) 1 = range γ₁ ∧
      let K₀ := A₀ '' closedBall (0 : E2) 1
      let K₁ := A₁ '' closedBall (0 : E2) 1
      let U₀ := A₀ '' ball (0 : E2) 1
      let U₁ := A₁ '' ball (0 : E2) 1
      (Disjoint K₀ K₁ ∧ S ⊆ (K₀ ∪ K₁)ᶜ) ∨
      (K₁ ⊆ U₀ ∧ S ⊆ U₀ \ K₁) ∨
      (K₀ ⊆ U₁ ∧ S ⊆ U₁ \ K₀) := by
  obtain ⟨A₀, A₁, hA₀, hA₁, hregion⟩ :=
    exists_filled_planar_circle_pair_with_connector_region γ₀ γ₁ hγ₀ hγ₁ hdisjoint β hβ
      hβ₀ hβ₁ (havoid.mono_left hβS)
  have hmid : β (1 / 2) ∈ β '' Ioo 0 1 := ⟨1 / 2, by norm_num, rfl⟩
  have hmidS := hβS hmid
  have hK₀ : IsClosed (A₀ '' closedBall (0 : E2) 1) :=
    A₀.toHomeomorph.isClosedMap _ isClosed_closedBall
  have hK₁ : IsClosed (A₁ '' closedBall (0 : E2) 1) :=
    A₁.toHomeomorph.isClosedMap _ isClosed_closedBall
  have hf₀ : frontier (A₀ '' closedBall (0 : E2) 1) = range γ₀ := by
    have h := A₀.toHomeomorph.image_frontier (closedBall (0 : E2) 1)
    rw [frontier_closedBall _ (by norm_num : (1 : Real) ≠ 0)] at h
    exact h.symm.trans hA₀
  have hf₁ : frontier (A₁ '' closedBall (0 : E2) 1) = range γ₁ := by
    have h := A₁.toHomeomorph.image_frontier (closedBall (0 : E2) 1)
    rw [frontier_closedBall _ (by norm_num : (1 : Real) ≠ 0)] at h
    exact h.symm.trans hA₁
  have hi₀ : interior (A₀ '' closedBall (0 : E2) 1) = A₀ '' ball (0 : E2) 1 := by
    have h := A₀.toHomeomorph.image_interior (closedBall (0 : E2) 1)
    rw [interior_closedBall _ (by norm_num : (1 : Real) ≠ 0)] at h
    exact h.symm
  have hi₁ : interior (A₁ '' closedBall (0 : E2) 1) = A₁ '' ball (0 : E2) 1 := by
    have h := A₁.toHomeomorph.image_interior (closedBall (0 : E2) 1)
    rw [interior_closedBall _ (by norm_num : (1 : Real) ≠ 0)] at h
    exact h.symm
  have hav₀ : Disjoint S (frontier (A₀ '' closedBall (0 : E2) 1)) := by
    rw [hf₀]
    exact havoid.mono_right subset_union_left
  have hav₁ : Disjoint S (frontier (A₁ '' closedBall (0 : E2) 1)) := by
    rw [hf₁]
    exact havoid.mono_right subset_union_right
  refine ⟨A₀, A₁, hA₀, hA₁, ?_⟩
  rcases hregion with ⟨hsep, hout⟩ | ⟨hnest, hbetween⟩ | ⟨hnest, hbetween⟩
  · left
    have hm := hout hmid
    have hs₀ := preconnected_region_subset_compl hS hK₀ hav₀ hmidS
      (fun hx => hm (Or.inl hx))
    have hs₁ := preconnected_region_subset_compl hS hK₁ hav₁ hmidS
      (fun hx => hm (Or.inr hx))
    exact ⟨hsep, fun x hx hmem => hmem.elim (hs₀ hx) (hs₁ hx)⟩
  · right
    left
    have hs₀ := preconnected_region_subset_interior hS hK₀ hav₀ hmidS
      (hi₀.symm ▸ (hbetween hmid).1)
    have hs₁ := preconnected_region_subset_compl hS hK₁ hav₁ hmidS (hbetween hmid).2
    exact ⟨hnest, fun x hx => ⟨hi₀ ▸ hs₀ hx, hs₁ hx⟩⟩
  · right
    right
    have hs₁ := preconnected_region_subset_interior hS hK₁ hav₁ hmidS
      (hi₁.symm ▸ (hbetween hmid).1)
    have hs₀ := preconnected_region_subset_compl hS hK₀ hav₀ hmidS (hbetween hmid).2
    exact ⟨hnest, fun x hx => ⟨hi₁ ▸ hs₁ hx, hs₀ hx⟩⟩


def positiveLevelRibbon (t : Real) (z : E2) : E2 :=
  WithLp.toLp 2 ![z 0, (2 * z 1 - 1) * Real.sqrt (t + (z 0)^2)]


def negativeLevelRibbon (t : Real) (z : E2) : E2 :=
  saddleCoordinateSwap (positiveLevelRibbon t z)

@[simp] theorem positiveLevelRibbon_zero (t : Real) (z : E2) :
    positiveLevelRibbon t z 0 = z 0 := rfl

@[simp] theorem positiveLevelRibbon_one (t : Real) (z : E2) :
    positiveLevelRibbon t z 1 = (2 * z 1 - 1) * Real.sqrt (t + (z 0)^2) := rfl

@[simp] theorem positiveLevelRibbon_center (t s : Real) :
    positiveLevelRibbon t (WithLp.toLp 2 ![0, s]) = positiveLevelConnector t s := by
  ext i
  fin_cases i <;> simp [positiveLevelRibbon, positiveLevelConnector]

@[simp] theorem positiveLevelRibbon_start (t x : Real) :
    positiveLevelRibbon t (WithLp.toLp 2 ![x, 0]) = positiveLevelArc t 1 x := by
  ext i
  fin_cases i <;> norm_num [positiveLevelRibbon, positiveLevelArc]

@[simp] theorem positiveLevelRibbon_finish (t x : Real) :
    positiveLevelRibbon t (WithLp.toLp 2 ![x, 1]) = positiveLevelArc t 0 x := by
  ext i
  fin_cases i <;> norm_num [positiveLevelRibbon, positiveLevelArc]

@[simp] theorem negativeLevelRibbon_center (t s : Real) :
    negativeLevelRibbon t (WithLp.toLp 2 ![0, s]) = negativeLevelConnector t s := by
  simp [negativeLevelRibbon, negativeLevelConnector]

@[simp] theorem negativeLevelRibbon_start (t x : Real) :
    negativeLevelRibbon t (WithLp.toLp 2 ![x, 0]) = negativeLevelArc t 1 x := by
  simp [negativeLevelRibbon, negativeLevelArc]

@[simp] theorem negativeLevelRibbon_finish (t x : Real) :
    negativeLevelRibbon t (WithLp.toLp 2 ![x, 1]) = negativeLevelArc t 0 x := by
  simp [negativeLevelRibbon, negativeLevelArc]

theorem contDiff_positiveLevelRibbon {t : Real} (ht : 0 < t) :
    ContDiff Real ∞ (positiveLevelRibbon t) := by
  have h0 : ContDiff Real ∞ (fun x : E2 => x 0) :=
    (EuclideanSpace.proj (𝕜 := Real) (0 : Fin 2)).contDiff
  have h1 : ContDiff Real ∞ (fun x : E2 => x 1) :=
    (EuclideanSpace.proj (𝕜 := Real) (1 : Fin 2)).contDiff
  apply (contDiff_piLp 2).mpr
  intro i
  fin_cases i
  · exact h0
  · exact ((contDiff_const.mul h1).sub contDiff_const).mul
      ((contDiff_const.add (h0.pow 2)).sqrt (fun z => ne_of_gt (by positivity)))


def positiveLevelRibbonDiffeomorph {t : Real} (ht : 0 < t) :
    Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞ where
  toFun := positiveLevelRibbon t
  invFun y := WithLp.toLp 2 ![y 0, (y 1 / Real.sqrt (t + (y 0)^2) + 1) / 2]
  left_inv z := by
    have hp : Real.sqrt (t + (z 0)^2) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by positivity))
    ext i
    fin_cases i
    · rfl
    · simp [positiveLevelRibbon, hp]
  right_inv z := by
    have hp : Real.sqrt (t + (z 0)^2) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by positivity))
    ext i
    fin_cases i
    · rfl
    · simp [positiveLevelRibbon]
      field_simp
      ring
  contMDiff_toFun := (contDiff_positiveLevelRibbon ht).contMDiff
  contMDiff_invFun := by
    apply ContDiff.contMDiff
    have h0 : ContDiff Real ∞ (fun x : E2 => x 0) :=
      (EuclideanSpace.proj (𝕜 := Real) (0 : Fin 2)).contDiff
    have h1 : ContDiff Real ∞ (fun x : E2 => x 1) :=
      (EuclideanSpace.proj (𝕜 := Real) (1 : Fin 2)).contDiff
    apply (contDiff_piLp 2).mpr
    intro i
    fin_cases i
    · exact h0
    · exact ((h1.div
        ((contDiff_const.add (h0.pow 2)).sqrt (fun z => ne_of_gt (by positivity)))
        (fun z => ne_of_gt (Real.sqrt_pos.2 (by positivity)))).add contDiff_const).div_const 2

theorem contDiff_negativeLevelRibbon {t : Real} (ht : 0 < t) :
    ContDiff Real ∞ (negativeLevelRibbon t) :=
  contDiff_saddleCoordinateSwap.comp (contDiff_positiveLevelRibbon ht)


def negativeLevelRibbonDiffeomorph {t : Real} (ht : 0 < t) :
    Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞ :=
  (positiveLevelRibbonDiffeomorph ht).trans {
    toFun := saddleCoordinateSwap
    invFun := saddleCoordinateSwap
    left_inv := saddleCoordinateSwap_swap
    right_inv := saddleCoordinateSwap_swap
    contMDiff_toFun := contDiff_saddleCoordinateSwap.contMDiff
    contMDiff_invFun := contDiff_saddleCoordinateSwap.contMDiff }

@[simp] theorem positiveLevelRibbonDiffeomorph_apply {t : Real} (ht : 0 < t) (z : E2) :
    positiveLevelRibbonDiffeomorph ht z = positiveLevelRibbon t z := rfl

@[simp] theorem negativeLevelRibbonDiffeomorph_apply {t : Real} (ht : 0 < t) (z : E2) :
    negativeLevelRibbonDiffeomorph ht z = negativeLevelRibbon t z := rfl

theorem positiveLevelRibbon_injective {t : Real} (ht : 0 < t) :
    Injective (positiveLevelRibbon t) := (positiveLevelRibbonDiffeomorph ht).injective

theorem negativeLevelRibbon_injective {t : Real} (ht : 0 < t) :
    Injective (negativeLevelRibbon t) :=
  saddleCoordinateSwap_injective.comp (positiveLevelRibbon_injective ht)

theorem positiveLevelRibbon_mem_openSquare {r t : Real}
    (hr : 0 < r) (ht : 0 < t) (htr : t < r^2) {z : E2}
    (hz0 : z 0 ∈ Ioo (-hyperbolaRadius r t) (hyperbolaRadius r t))
    (hz1 : z 1 ∈ Icc 0 1) : positiveLevelRibbon t z ∈ openSquare r := by
  have harc := (positiveLevelArc_mem_openSquare hr ht htr (0 : Fin 2) (z 0)).mpr hz0
  have hroot : Real.sqrt (t + (z 0)^2) < r := by
    simpa [openSquare, positiveLevelArc, abs_of_nonneg (Real.sqrt_nonneg _)] using harc.2
  have hmul : |(2 * z 1 - 1) * Real.sqrt (t + (z 0)^2)| ≤
      Real.sqrt (t + (z 0)^2) := by
    rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
    have h : |2 * z 1 - 1| ≤ 1 := abs_le.mpr (by constructor <;> linarith [hz1.1, hz1.2])
    simpa using mul_le_mul_of_nonneg_right h (Real.sqrt_nonneg _)
  exact ⟨harc.1, hmul.trans_lt hroot⟩

theorem negativeLevelRibbon_mem_openSquare {r t : Real}
    (hr : 0 < r) (ht : 0 < t) (htr : t < r^2) {z : E2}
    (hz0 : z 0 ∈ Ioo (-hyperbolaRadius r t) (hyperbolaRadius r t))
    (hz1 : z 1 ∈ Icc 0 1) : negativeLevelRibbon t z ∈ openSquare r :=
  (saddleCoordinateSwap_mem_openSquare r _).mpr
    (positiveLevelRibbon_mem_openSquare hr ht htr hz0 hz1)

theorem positiveLevelRibbon_height_lt {t : Real} (ht : 0 < t) {z : E2}
    (hz : z 1 ∈ Ioo 0 1) :
    -(positiveLevelRibbon t z 0)^2 + (positiveLevelRibbon t z 1)^2 < t := by
  have hroot := Real.sq_sqrt (show 0 ≤ t + (z 0)^2 by positivity)
  have hsq : (2 * z 1 - 1)^2 < 1 := by nlinarith [hz.1, hz.2]
  have hp : 0 < t + (z 0)^2 := by positivity
  have hmul := mul_lt_mul_of_pos_right hsq hp
  simp only [positiveLevelRibbon_zero, positiveLevelRibbon_one, mul_pow, hroot]
  nlinarith

theorem negativeLevelRibbon_height_gt {t : Real} (ht : 0 < t) {z : E2}
    (hz : z 1 ∈ Ioo 0 1) :
    -t < -(negativeLevelRibbon t z 0)^2 + (negativeLevelRibbon t z 1)^2 := by
  have hh := positiveLevelRibbon_height_lt ht hz
  change -t < -(positiveLevelRibbon t z 1)^2 + (positiveLevelRibbon t z 0)^2
  linarith




theorem exists_saddle_level_ribbons
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
        positiveLevelRibbon t '' {z : E2 | |z 0| ≤ r / 2 ∧ z 1 ∈ Icc 0 1} ⊆
          openSquare r ∧
        negativeLevelRibbon t '' {z : E2 | |z 0| ≤ r / 2 ∧ z 1 ∈ Icc 0 1} ⊆
          openSquare r ∧
        (∀ z : E2, |z 0| ≤ r / 2 → z 1 ∈ Icc 0 1 →
          planarProjection J (D (f (e (positiveLevelRibbon t z)))) = positiveLevelRibbon t z) ∧
        (∀ z : E2, |z 0| ≤ r / 2 → z 1 ∈ Icc 0 1 →
          planarProjection J (D (f (e (negativeLevelRibbon t z)))) = negativeLevelRibbon t z) ∧
        Disjoint (positiveLevelRibbon t '' {z : E2 | |z 0| ≤ r / 2 ∧ z 1 ∈ Ioo 0 1})
          ((fun q : S2 => planarProjection J (D (f q))) ''
            {q | inner Real v (f q) = inner Real v (f p) + t}) ∧
        Disjoint (negativeLevelRibbon t '' {z : E2 | |z 0| ≤ r / 2 ∧ z 1 ∈ Ioo 0 1})
          ((fun q : S2 => planarProjection J (D (f q))) ''
            {q | inner Real v (f q) = inner Real v (f p) - t}) := by
  obtain ⟨r, η, hr, hrε, hη, hrs, hclear⟩ :=
    exists_uniform_planar_clearance hf hv p e hep ha has J D hDheight hgraph hε
  let δ := min η (r^2) / 4
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
    have hJ := Submodule.mem_orthogonal_singleton_iff_inner_right.mp (J x).property
    simpa [hDheight, inner_add_right, inner_smul_right, hJ, hv] using hh
  refine ⟨r, δ, hr, hrε, hδ, hδr, hrs, ?_⟩
  intro t ht htδ
  have htr := htδ.trans hδr
  have htη := htδ.trans hδη
  have hhalf : r / 2 < hyperbolaRadius r t := by
    have hrad := hyperbolaRadius_pos htr
    have hrad2 := hyperbolaRadius_sq htr.le
    have hm := min_le_right η (r^2)
    dsimp [δ] at htδ
    nlinarith
  have hwidth (z : E2) (hz : |z 0| ≤ r / 2) :
      z 0 ∈ Ioo (-hyperbolaRadius r t) (hyperbolaRadius r t) :=
    abs_lt.mp (hz.trans_lt hhalf)
  have hpos (z : E2) (hz : |z 0| ≤ r / 2) (hs : z 1 ∈ Icc 0 1) :
      positiveLevelRibbon t z ∈ closedSquare r :=
    openSquare_subset_closedSquare r
      (positiveLevelRibbon_mem_openSquare hr ht htr (hwidth z hz) hs)
  have hneg (z : E2) (hz : |z 0| ≤ r / 2) (hs : z 1 ∈ Icc 0 1) :
      negativeLevelRibbon t z ∈ closedSquare r :=
    openSquare_subset_closedSquare r
      (negativeLevelRibbon_mem_openSquare hr ht htr (hwidth z hz) hs)
  refine ⟨?_, ?_, (fun z hz hs => hproj _ (hpos z hz hs)),
    (fun z hz hs => hproj _ (hneg z hz hs)), ?_, ?_⟩
  · rintro x ⟨z, ⟨hz, hs⟩, rfl⟩
    exact positiveLevelRibbon_mem_openSquare hr ht htr (hwidth z hz) hs
  · rintro x ⟨z, ⟨hz, hs⟩, rfl⟩
    exact negativeLevelRibbon_mem_openSquare hr ht htr (hwidth z hz) hs
  · apply disjoint_left.mpr
    rintro x ⟨z, ⟨hz, hs⟩, rfl⟩ ⟨q, hq, hπ⟩
    dsimp only at hπ
    have hband : |inner Real v (f q) - inner Real v (f p)| ≤ η := by
      change inner Real v (f q) = inner Real v (f p) + t at hq
      rw [hq, add_sub_cancel_left, abs_of_pos ht]
      exact htη.le
    have hqchart := hclear q hband (hπ.symm ▸ hpos z hz (Ioo_subset_Icc_self hs))
    rw [hπ] at hqchart
    have hh := hheight _ (hpos z hz (Ioo_subset_Icc_self hs))
    rw [← hqchart] at hh
    have hlt := positiveLevelRibbon_height_lt ht hs
    change inner Real v (f q) = inner Real v (f p) + t at hq
    linarith
  · apply disjoint_left.mpr
    rintro x ⟨z, ⟨hz, hs⟩, rfl⟩ ⟨q, hq, hπ⟩
    dsimp only at hπ
    have hband : |inner Real v (f q) - inner Real v (f p)| ≤ η := by
      change inner Real v (f q) = inner Real v (f p) - t at hq
      rw [hq, sub_sub_cancel_left, abs_neg, abs_of_pos ht]
      exact htη.le
    have hqchart := hclear q hband (hπ.symm ▸ hneg z hz (Ioo_subset_Icc_self hs))
    rw [hπ] at hqchart
    have hh := hheight _ (hneg z hz (Ioo_subset_Icc_self hs))
    rw [← hqchart] at hh
    have hlt := negativeLevelRibbon_height_gt ht hs
    change inner Real v (f q) = inner Real v (f p) - t at hq
    linarith



theorem exists_saddle_circle_pair_ribbon_regions
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
        let R := if positive then positiveLevelRibbon t else negativeLevelRibbon t
        let S := R '' {z : E2 | |z 0| ≤ r / 2 ∧ z 1 ∈ Ioo 0 1}
        R '' {z : E2 | |z 0| ≤ r / 2 ∧ z 1 ∈ Icc 0 1} ⊆ openSquare r ∧
        Disjoint S (range γ₀ ∪ range γ₁) ∧
        ∃ A₀ A₁ : Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞,
          A₀ '' sphere (0 : E2) 1 = range γ₀ ∧
          A₁ '' sphere (0 : E2) 1 = range γ₁ ∧
          let K₀ := A₀ '' closedBall (0 : E2) 1
          let K₁ := A₁ '' closedBall (0 : E2) 1
          let U₀ := A₀ '' ball (0 : E2) 1
          let U₁ := A₁ '' ball (0 : E2) 1
          (Disjoint K₀ K₁ ∧ S ⊆ (K₀ ∪ K₁)ᶜ) ∨
          (K₁ ⊆ U₀ ∧ S ⊆ U₀ \ K₁) ∨
          (K₀ ⊆ U₁ ∧ S ⊆ U₁ \ K₀) := by
  obtain ⟨r, δ, hr, hrε, hδ, hδr, _, hribbon⟩ :=
    exists_saddle_level_ribbons hf hv p e hep ha has J D hDheight hgraph hε
  refine ⟨r, δ, hr, hrε, hδ, hδr, ?_⟩
  intro t ht htδ positive γ₀ γ₁ hγ₀ hγ₁ hdisjoint hstart hfinish hcircles
  obtain ⟨hpos, hneg, hposπ, hnegπ, hposavoid, hnegavoid⟩ := hribbon t ht htδ
  let β := if positive then positiveLevelConnector t else negativeLevelConnector t
  let R := if positive then positiveLevelRibbon t else negativeLevelRibbon t
  let S := R '' {z : E2 | |z 0| ≤ r / 2 ∧ z 1 ∈ Ioo 0 1}
  have hβ : ContDiff Real ∞ β := by
    cases positive
    · exact contDiff_negativeLevelConnector t
    · exact contDiff_positiveLevelConnector t
  have hR : ContDiff Real ∞ R := by
    cases positive
    · exact contDiff_negativeLevelRibbon ht
    · exact contDiff_positiveLevelRibbon ht
  have hRsq : R '' {z : E2 | |z 0| ≤ r / 2 ∧ z 1 ∈ Icc 0 1} ⊆ openSquare r := by
    cases positive
    · exact hneg
    · exact hpos
  have hRcenter (s : Real) : R (WithLp.toLp 2 ![0, s]) = β s := by
    cases positive <;> simp [R, β]
  have hβπ : ∀ s ∈ Icc (0 : Real) 1,
      planarProjection J (D (f (e (β s)))) = β s := by
    intro s hs
    have hz : |(WithLp.toLp 2 ![0, s] : E2) 0| ≤ r / 2 := by
      simpa using (show 0 ≤ r / 2 by positivity)
    rw [← hRcenter s]
    cases positive
    · exact hnegπ _ hz hs
    · exact hposπ _ hz hs
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
  have hβS : β '' Ioo 0 1 ⊆ S := by
    rintro x ⟨s, hs, rfl⟩
    refine ⟨WithLp.toLp 2 ![0, s], ?_, hRcenter s⟩
    refine ⟨?_, hs⟩
    simpa using (show 0 ≤ r / 2 by positivity)
  have hS : IsPreconnected S :=
    (isPreconnected_ribbon_parameters r).image R hR.continuous.continuousOn
  have havoid : Disjoint S (range γ₀ ∪ range γ₁) := by
    apply Disjoint.mono_right hcircles
    cases positive
    · simpa only [S, R, Bool.false_eq_true, ↓reduceIte, sub_eq_add_neg] using hnegavoid
    · simpa only [S, R, ↓reduceIte] using hposavoid
  exact ⟨hRsq, havoid, exists_filled_planar_circle_pair_with_ribbon_region γ₀ γ₁ hγ₀ hγ₁
    hdisjoint β hβ.continuous.continuousOn hβ₀ hβ₁ S hS hβS havoid⟩

end Poincare.Manifold.Schoenflies.SaddleLevel
