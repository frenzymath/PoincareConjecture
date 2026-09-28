import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Surgery.Iteration.Core.Regular







open _root_.AddCircle
open _root_.Poincare
open _root_.Poincare.Manifold
open _root_.Poincare.Manifold.Schoenflies
open _root_.PoincareConjecture

namespace M38Schoenflies



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Filter
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies.SphereSurgeryCoreCap

private abbrev E1 := EuclideanSpace Real (Fin 1)
private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S1 := sphere (0 : E2) 1
private abbrev S2 := sphere (0 : E3) 1
local notation "Iprod" => ModelWithCorners.prod (𝓡 1) 𝓘(Real, Real)
private instance : ChartedSpace (E1 × Real) (S1 × Real) :=
  prodChartedSpace E1 S1 Real Real

variable {v : E3} {g : S2 → E3} {B : Set Real}



theorem exists_small_belt_subset_open (D : SphereSurgeryCoreCap v g B)
    (hg : Continuous g) {U : Set S2} (hU : IsOpen U)
    (hboundary : D.chart '' sphere (0 : E2) 1 ⊆ U) :
    ∃ η : Real, 0 < η ∧ η < 1 ∧ ∀ p ∈ D.chart '' closedBall 0 1,
      (inner Real v (g p) - D.center) / D.scale ≤ η → p ∈ U := by
  let n : S2 → Real := fun p => (inner Real v (g p) - D.center) / D.scale
  have hn : Continuous n := (((innerSL Real v).continuous.comp hg).sub continuous_const).div_const _
  let K : Set S2 := (D.chart '' closedBall 0 1) ∩ Uᶜ
  have hK : IsCompact K := ((isCompact_closedBall 0 1).image_of_continuousOn
    (D.chart.continuousOn.mono D.source)).inter_right hU.isClosed_compl
  have hzero : (0 : Real) ∈ (n '' K)ᶜ := by
    rintro ⟨p, ⟨hpD, hpU⟩, hpzero⟩
    obtain ⟨x, hx, rfl⟩ := hpD
    have hxzero : (inner Real v (D.parametrization x) - D.center) / D.scale = 0 := by
      simpa only [n, D.parametrization_eq x hx] using hpzero
    exact hpU (hboundary (mem_image_of_mem D.chart
      ((D.normalized_height_eq_zero_iff hx).mp hxzero)))
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp
    ((hK.image hn).isClosed.isOpen_compl.mem_nhds hzero)
  let η := min ε 1 / 2
  have hη : 0 < η := half_pos (lt_min hε zero_lt_one)
  have hηε : η < ε := by dsimp [η]; linarith [min_le_left ε 1]
  have hη1 : η < 1 := by dsimp [η]; linarith [min_le_right ε 1]
  refine ⟨η, hη, hη1, ?_⟩
  intro p hpD hpn
  by_contra hpU
  have hnnonneg : 0 ≤ n p := by
    obtain ⟨x, hx, rfl⟩ := hpD
    change 0 ≤ (inner Real v (g (D.chart x)) - D.center) / D.scale
    rw [D.parametrization_eq x hx]
    exact D.normalized_height_nonneg hx
  apply hεsub (show n p ∈ ball 0 ε by
    rw [mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg hnnonneg]
    exact hpn.trans_lt hηε)
  exact ⟨p, ⟨hpD, hpU⟩, rfl⟩

private theorem annular_slice_deriv_injective
    (G : OpenPartialHomeomorph (S1 × Real) S2)
    (hG : ContMDiffOn Iprod (𝓡 2) ∞ G G.source)
    (hGi : ContMDiffOn (𝓡 2) Iprod ∞ G.symm G.target)
    (t : Real) (ht : ∀ q : S1, (q, t) ∈ G.source) (q : S1) :
    Function.Injective (mfderiv (𝓡 1) (𝓡 2) (fun p : S1 => G (p, t)) q) := by
  let d : PartialDiffeomorph Iprod (𝓡 2) (S1 × Real) S2 ∞ := {
    toPartialEquiv := G.toPartialEquiv
    open_source := G.open_source
    open_target := G.open_target
    contMDiffOn_toFun := hG
    contMDiffOn_invFun := hGi }
  have hloc : IsLocalDiffeomorphAt Iprod (𝓡 2) ∞ G (q, t) :=
    ⟨d, ht q, fun _ _ => rfl⟩
  have hp : MDifferentiableAt (𝓡 1) Iprod (fun p : S1 => (p, t)) q :=
    mdifferentiableAt_id.prodMk mdifferentiableAt_const
  have hpd := mfderiv_prodMk
    (mdifferentiableAt_id (I := 𝓡 1) (x := q))
    (mdifferentiableAt_const (I := 𝓡 1) (I' := 𝓘(Real, Real)) (c := t) (x := q))
  change mfderiv (𝓡 1) Iprod (fun p : S1 => (p, t)) q = _ at hpd
  change Function.Injective (mfderiv (𝓡 1) (𝓡 2) (G ∘ fun p : S1 => (p, t)) q)
  rw [mfderiv_comp q
    ((hG.contMDiffAt (G.open_source.mem_nhds (ht q))).mdifferentiableAt (by simp)) hp,
    hpd, mfderiv_id, mfderiv_const]
  apply (hloc.mfderivToContinuousLinearEquiv (by simp)).injective.comp
  intro x y hxy
  exact congrArg Prod.fst hxy



theorem cap_slice_eq_annular_slice (D : SphereSurgeryCoreCap v g B)
    (hg : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ g)
    (F : OpenPartialHomeomorph (S1 × Real) S2) {a b : Real}
    (hFs : F.source = univ ×ˢ Ioo a b)
    (hF : ContMDiffOn Iprod (𝓡 2) ∞ F F.source)
    (hFi : ContMDiffOn (𝓡 2) Iprod ∞ F.symm F.target)
    (hheight : ∀ q t, t ∈ Ioo a b → inner Real v (g (F (q, t))) = t)
    {θ : Real} (hθ : 0 < θ) (hθ1 : θ < 1)
    (hc : D.center + D.scale * θ ∈ Ioo a b)
    (htarget : (D.chart '' closedBall 0 1) ∩
      {p : S2 | inner Real v (g p) = D.center + D.scale * θ} ⊆ F.target) :
    (D.chart '' closedBall 0 1) ∩
      {p : S2 | inner Real v (g p) = D.center + D.scale * θ} =
        range (fun q : S1 => F (q, D.center + D.scale * θ)) := by
  obtain ⟨J, G, hGs, hG, hGi, hGg, hGt, _⟩ :=
    D.exists_cylindrical_belt_chart_of_width hg le_rfl
  let t := D.scale * (θ - 1 / 2)
  have ht : t ∈ Ioo (- (|D.scale| / 2)) (|D.scale| / 2) := by
    apply abs_lt.mp
    change |D.scale * (θ - 1 / 2)| < |D.scale| / 2
    rw [abs_mul]
    have hsmall : |θ - 1 / 2| < 1 / 2 := abs_lt.mpr ⟨by linarith, by linarith⟩
    nlinarith [mul_lt_mul_of_pos_left hsmall (abs_pos.mpr D.scale_ne_zero)]
  have htime : D.center + D.scale / 2 + t = D.center + D.scale * θ := by dsimp [t]; ring
  have hGtall (q : S1) : (q, t) ∈ G.source := hGs ▸ ⟨mem_univ _, ht⟩
  have hheightG (q : S1) : inner Real v (g (G (q, t))) = D.center + D.scale * θ := by
    rw [hGg q t ht]
    simp [inner_add_right, inner_smul_right, D.unit_v,
      Submodule.mem_orthogonal_singleton_iff_inner_right.mp (D.planeMap _).property, htime]
  have hrange : range (fun q : S1 => G (q, t)) = (D.chart '' closedBall 0 1) ∩
      {p : S2 | inner Real v (g p) = D.center + D.scale * θ} := by
    ext p
    constructor
    · rintro ⟨q, rfl⟩
      exact ⟨(hGt ▸ G.map_source (hGtall q)).1, hheightG q⟩
    · rintro ⟨hpD, hpheight⟩
      change inner Real v (g p) = D.center + D.scale * θ at hpheight
      have hpG : p ∈ G.target := by
        rw [hGt]
        refine ⟨hpD, ?_⟩
        change |inner Real v (g p) - (D.center + D.scale / 2)| < |D.scale| / 2
        rw [hpheight, ← htime]
        simpa only [add_sub_cancel_left] using abs_lt.mpr ht
      have hcoord := G.map_target hpG
      have hcoordheight : inner Real v (g (G (G.symm p))) =
          D.center + D.scale / 2 + (G.symm p).2 := by
        rw [hGg _ _ (hGs ▸ hcoord).2]
        simp [inner_add_right, inner_smul_right, D.unit_v,
          Submodule.mem_orthogonal_singleton_iff_inner_right.mp (D.planeMap _).property]
      rw [G.right_inv hpG, hpheight, ← htime] at hcoordheight
      have htcoord : (G.symm p).2 = t := by linarith
      refine ⟨(G.symm p).1, ?_⟩
      rw [← htcoord]
      exact G.right_inv hpG
  rw [← hrange]
  apply range_eq_annular_slice_of_immersed_circle F hFs hF hFi
    (h := fun p => inner Real v (g p)) hheight hc
    (fun q => G (q, t))
  · intro q
    exact (hG.contMDiffAt (G.open_source.mem_nhds (hGtall q))).comp q
      ((contMDiff_id.prodMk contMDiff_const) q)
  · exact annular_slice_deriv_injective G hG hGi t hGtall
  · rwa [hrange]
  · exact hheightG

theorem zero_slice_eq_boundary (D : SphereSurgeryCoreCap v g B) :
    (D.chart '' closedBall 0 1) ∩ {p : S2 | inner Real v (g p) = D.center} =
      D.chart '' sphere (0 : E2) 1 := by
  ext p
  constructor
  · rintro ⟨⟨x, hx, rfl⟩, hheight⟩
    refine mem_image_of_mem D.chart ((D.normalized_height_eq_zero_iff hx).mp ?_)
    change inner Real v (g (D.chart x)) = D.center at hheight
    rw [D.parametrization_eq x hx] at hheight
    rw [hheight, sub_self, zero_div]
  · intro hp
    exact ⟨image_mono sphere_subset_closedBall hp, D.height_eq_on_boundary p hp⟩

theorem cap_slice_eq_annular_slice_of_nonneg (D : SphereSurgeryCoreCap v g B)
    (hg : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ g)
    (F : OpenPartialHomeomorph (S1 × Real) S2) {a b : Real}
    (hFs : F.source = univ ×ˢ Ioo a b)
    (hF : ContMDiffOn Iprod (𝓡 2) ∞ F F.source)
    (hFi : ContMDiffOn (𝓡 2) Iprod ∞ F.symm F.target)
    (hheight : ∀ q t, t ∈ Ioo a b → inner Real v (g (F (q, t))) = t)
    {θ : Real} (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (hc : D.center + D.scale * θ ∈ Ioo a b)
    (htarget : (D.chart '' closedBall 0 1) ∩
      {p : S2 | inner Real v (g p) = D.center + D.scale * θ} ⊆ F.target) :
    (D.chart '' closedBall 0 1) ∩
      {p : S2 | inner Real v (g p) = D.center + D.scale * θ} =
        range (fun q : S1 => F (q, D.center + D.scale * θ)) := by
  rcases hθ.eq_or_lt with hzero | hpos
  · subst θ
    simp only [mul_zero, add_zero] at hc htarget ⊢
    rw [D.zero_slice_eq_boundary] at htarget ⊢
    exact D.boundary_eq_annular_slice F hFs hF hFi
      (h := fun p => inner Real v (g p)) hheight hc htarget D.height_eq_on_boundary
  · exact D.cap_slice_eq_annular_slice hg F hFs hF hFi hheight hpos hθ1 hc htarget



theorem image_cap_slice_eq_circle (D : SphereSurgeryCoreCap v g B)
    {θ : Real} (hθ : θ ∈ Ico (0 : Real) 1) :
    g '' ((D.chart '' closedBall 0 1) ∩
      {p : S2 | inner Real v (g p) = D.center + D.scale * θ}) =
        (fun x : Hemisphere.Plane v =>
          (D.center + D.scale * θ) • v + (D.planeMap x : E3)) ''
            sphere (0 : Hemisphere.Plane v) 1 := by
  change g '' ((D.chart '' closedBall 0 1) ∩
    g ⁻¹' {y : E3 | inner Real v y = D.center + D.scale * θ}) = _
  rw [image_inter_preimage, D.image_closedBall, D.range_eq]
  exact lifted_cap_slice_eq_circle D.unit_v D.center D.scale D.scale_ne_zero D.planeMap hθ



theorem exists_annular_cap_belt (D : SphereSurgeryCoreCap v g B)
    (hg : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ g)
    (F : OpenPartialHomeomorph (S1 × Real) S2) {a b : Real}
    (hFs : F.source = univ ×ˢ Ioo a b)
    (hF : ContMDiffOn Iprod (𝓡 2) ∞ F F.source)
    (hFi : ContMDiffOn (𝓡 2) Iprod ∞ F.symm F.target)
    (hheight : ∀ q t, t ∈ Ioo a b → inner Real v (g (F (q, t))) = t)
    (hc : D.center ∈ Ioo a b)
    (hboundary : D.chart '' sphere (0 : E2) 1 ⊆ F.target) :
    ∃ η : Real, 0 < η ∧ η < 1 ∧ ∀ θ ∈ Icc (0 : Real) η,
      D.center + D.scale * θ ∈ Ioo a b ∧
      ((D.chart '' closedBall 0 1) ∩
        {p : S2 | inner Real v (g p) = D.center + D.scale * θ} =
          range (fun q : S1 => F (q, D.center + D.scale * θ))) ∧
      g '' range (fun q : S1 => F (q, D.center + D.scale * θ)) =
        (fun x : Hemisphere.Plane v =>
          (D.center + D.scale * θ) • v + (D.planeMap x : E3)) ''
            sphere (0 : Hemisphere.Plane v) 1 := by
  obtain ⟨η₀, hη₀, hη₀1, hthin⟩ :=
    D.exists_small_belt_subset_open hg.contMDiff.continuous F.open_target hboundary
  let m := min (D.center - a) (b - D.center)
  have hm : 0 < m := lt_min (sub_pos.mpr hc.1) (sub_pos.mpr hc.2)
  have hs : 0 < |D.scale| := abs_pos.mpr D.scale_ne_zero
  have hdiv : 0 < m / (2 * |D.scale|) := div_pos hm (by positivity)
  let η := min η₀ (m / (2 * |D.scale|)) / 2
  have hη : 0 < η := half_pos (lt_min hη₀ hdiv)
  have hη₀le : η ≤ η₀ := by dsimp [η]; linarith [min_le_left η₀ (m / (2 * |D.scale|))]
  have hηm : η < m / (2 * |D.scale|) := by
    dsimp [η]
    linarith [min_le_right η₀ (m / (2 * |D.scale|))]
  refine ⟨η, hη, hη₀le.trans_lt hη₀1, ?_⟩
  intro θ hθ
  have hθ1 : θ < 1 := hθ.2.trans_lt (hη₀le.trans_lt hη₀1)
  have hmul : |D.scale| * θ < m := by
    have hx := (lt_div_iff₀ (by positivity : 0 < 2 * |D.scale|)).mp
      (hθ.2.trans_lt hηm)
    nlinarith [mul_nonneg (abs_nonneg D.scale) hθ.1]
  have habs : |D.scale * θ| < m := by rwa [abs_mul, abs_of_nonneg hθ.1]
  have hlevel : D.center + D.scale * θ ∈ Ioo a b := by
    have hlo := (abs_lt.mp habs).1
    have hhi := (abs_lt.mp habs).2
    have hma : m ≤ D.center - a := min_le_left _ _
    have hmb : m ≤ b - D.center := min_le_right _ _
    constructor <;> linarith
  have htarget : (D.chart '' closedBall 0 1) ∩
      {p : S2 | inner Real v (g p) = D.center + D.scale * θ} ⊆ F.target := by
    rintro p ⟨hpD, hpheight⟩
    apply hthin p hpD
    change inner Real v (g p) = D.center + D.scale * θ at hpheight
    rw [hpheight, add_sub_cancel_left, mul_div_cancel_left₀ _ D.scale_ne_zero]
    exact hθ.2.trans hη₀le
  have heq := D.cap_slice_eq_annular_slice_of_nonneg hg F hFs hF hFi hheight
    hθ.1 hθ1 hlevel htarget
  refine ⟨hlevel, heq, ?_⟩
  rw [← heq]
  exact D.image_cap_slice_eq_circle ⟨hθ.1, hθ1⟩

theorem projected_slice_eq_circle (D : SphereSurgeryCoreCap v g B)
    (F : OpenPartialHomeomorph (S1 × Real) S2) (t : Real)
    (hcircle : g '' range (fun q : S1 => F (q, t)) =
      (fun x : Hemisphere.Plane v => t • v + (D.planeMap x : E3)) ''
        sphere (0 : Hemisphere.Plane v) 1) :
    range (fun q : S1 => (Hemisphere.Plane v).orthogonalProjectionOnto (g (F (q, t)))) =
      D.planeMap '' sphere (0 : Hemisphere.Plane v) 1 := by
  have h := congrArg (fun S : Set E3 => (Hemisphere.Plane v).orthogonalProjectionOnto '' S) hcircle
  simpa [image_image, ← Set.range_comp, Function.comp_def, Hemisphere.Plane,
    Submodule.orthogonalProjectionOnto_orthogonalComplement_singleton_eq_zero] using h

end Poincare.Manifold.Schoenflies.SphereSurgeryCoreCap

end

end M38Schoenflies
