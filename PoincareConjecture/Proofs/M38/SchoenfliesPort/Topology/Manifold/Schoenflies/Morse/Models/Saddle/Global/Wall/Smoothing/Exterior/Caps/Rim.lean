import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Caps.EndBall.Topology
import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Caps.EndBall.UpperGeometry







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

namespace Poincare.Manifold.Schoenflies.Saddle.Wall.Smoothing.Exterior.Caps

open SphereSurgeryCoreCap

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S1 := sphere (0 : E2) 1
private abbrev S2 := sphere (0 : E3) 1
local notation "IP" => ModelWithCorners.prod (𝓡 1) 𝓘(Real, Real)



theorem exists_lower_physical_annulus_across_rim
    {v : E3} {g : S2 → E3} {P : Set Real}
    {D : SphereSurgeryCoreCap v g P} {C : Set S2} {h : S2 → Real} {a b : Real}
    (A : LowerAnnularEnd D C h a b) (haD : a ≤ D.center)
    {c : Real} (hDc : D.center < c) (hcb : c < b)
    (hgerm : ∀ p ∈ D.chart '' sphere (0 : E2) 1,
      h =ᶠ[𝓝 p] (fun q => inner Real v (g q))) :
    ∃ δ : Real, 0 < δ ∧
      ∃ T : OpenPartialHomeomorph (S1 × Real) S2,
        T.source = univ ×ˢ Ioo (D.center - δ) (c + δ) ∧
        ContMDiffOn IP (𝓡 2) ∞ T T.source ∧
        ContMDiffOn (𝓡 2) IP ∞ T.symm T.target ∧
        (∀ z, T z = A.chart z) ∧
        (∀ q t, t ∈ Ioo (D.center - δ) (c + δ) →
          inner Real v (g (T (q, t))) = t) ∧
        range (fun q : S1 => T (q, D.center)) = D.chart '' sphere (0 : E2) 1 := by
  have hnear : ∀ᶠ t in 𝓝 D.center, ∀ q : S1,
      inner Real v (g (A.chart (q, t))) = t := by
    have hh := (isCompact_univ : IsCompact (univ : Set S1)).eventually_forall_of_forall_eventually
      (x₀ := D.center) (P := fun t q => inner Real v (g (A.chart (q, t))) = t) (by
        intro q _
        have hqs := A.mem_source_of_mem_height_interval haD q ⟨le_rfl, hDc.le.trans hcb.le⟩
        have hqboundary : A.chart (q, D.center) ∈ D.chart '' sphere (0 : E2) 1 :=
          A.boundary ▸ mem_range_self q
        have hchart : ContinuousAt (fun z : Real × S1 => A.chart (z.2, z.1))
            (D.center, q) :=
          (A.chart.continuousAt hqs).comp (f := Prod.swap) continuous_swap.continuousAt
        have hsource : ∀ᶠ z : Real × S1 in 𝓝 (D.center, q),
            (z.2, z.1) ∈ A.chart.source :=
          continuous_swap.continuousAt.eventually (A.chart.open_source.mem_nhds hqs)
        filter_upwards [hchart.eventually (hgerm _ hqboundary), hsource] with z hz hzs
        exact hz.symm.trans (A.height z.2 z.1 (A.source ▸ hzs).2))
    simpa only [mem_univ, forall_const] using hh
  obtain ⟨η, hη, hηheight⟩ := Metric.mem_nhds_iff.mp hnear
  let δ := min (η / 2) (min (A.delta / 2) ((b - c) / 2))
  have hδ : 0 < δ := lt_min (half_pos hη)
    (lt_min (half_pos A.delta_pos) (half_pos (sub_pos.mpr hcb)))
  have hδη : δ < η := (min_le_left _ _).trans_lt (by linarith)
  have hδA : δ < A.delta :=
    ((min_le_right _ _).trans (min_le_left _ _)).trans_lt (by linarith [A.delta_pos])
  have hδb : δ < b - c :=
    ((min_le_right _ _).trans (min_le_right _ _)).trans_lt (by linarith)
  let W : Set (S1 × Real) := univ ×ˢ Ioo (D.center - δ) (c + δ)
  have hW : IsOpen W := isOpen_univ.prod isOpen_Ioo
  have hWs : W ⊆ A.chart.source := by
    rintro ⟨q, t⟩ ⟨_, ht⟩
    rw [A.source]
    exact ⟨mem_univ _, by linarith [ht.1], by linarith [ht.2, A.delta_pos]⟩
  let T := A.chart.restrOpen W hW
  refine ⟨δ, hδ, T, inter_eq_right.mpr hWs,
    A.smooth.mono inter_subset_left, A.symm_smooth.mono inter_subset_left,
    fun _ => rfl, ?_, A.boundary⟩
  intro q t ht
  change inner Real v (g (A.chart (q, t))) = t
  by_cases htc : t < D.center
  · apply hηheight (show t ∈ ball D.center η from ?_) q
    rw [mem_ball, Real.dist_eq, abs_lt]
    exact ⟨by linarith [ht.1], by linarith⟩
  · exact A.actual_height q t ⟨le_of_not_gt htc, by linarith [ht.2]⟩



theorem exists_upper_physical_annulus_across_rim
    {v : E3} {g : S2 → E3} {P : Set Real}
    {D : SphereSurgeryCoreCap v g P} {C : Set S2} {h : S2 → Real} {a b : Real}
    (A : UpperAnnularEnd D C h a b) (hDb : D.center ≤ b)
    {c : Real} (hac : a < c) (hcD : c < D.center)
    (hgerm : ∀ p ∈ D.chart '' sphere (0 : E2) 1,
      h =ᶠ[𝓝 p] (fun q => inner Real v (g q))) :
    ∃ δ : Real, 0 < δ ∧
      ∃ T : OpenPartialHomeomorph (S1 × Real) S2,
        T.source = univ ×ˢ Ioo (c - δ) (D.center + δ) ∧
        ContMDiffOn IP (𝓡 2) ∞ T T.source ∧
        ContMDiffOn (𝓡 2) IP ∞ T.symm T.target ∧
        (∀ z, T z = A.chart z) ∧
        (∀ q t, t ∈ Ioo (c - δ) (D.center + δ) →
          inner Real v (g (T (q, t))) = t) ∧
        range (fun q : S1 => T (q, D.center)) = D.chart '' sphere (0 : E2) 1 := by
  have hnear : ∀ᶠ t in 𝓝 D.center, ∀ q : S1,
      inner Real v (g (A.chart (q, t))) = t := by
    have hh := (isCompact_univ : IsCompact (univ : Set S1)).eventually_forall_of_forall_eventually
      (x₀ := D.center) (P := fun t q => inner Real v (g (A.chart (q, t))) = t) (by
        intro q _
        have hqs : (q, D.center) ∈ A.chart.source := by
          rw [A.source]
          exact ⟨mem_univ _, by linarith [A.reflected.delta_pos],
            by linarith [A.reflected.delta_pos]⟩
        have hqboundary : A.chart (q, D.center) ∈ D.chart '' sphere (0 : E2) 1 :=
          A.boundary ▸ mem_range_self q
        have hchart : ContinuousAt (fun z : Real × S1 => A.chart (z.2, z.1))
            (D.center, q) :=
          (A.chart.continuousAt hqs).comp (f := Prod.swap) continuous_swap.continuousAt
        have hsource : ∀ᶠ z : Real × S1 in 𝓝 (D.center, q),
            (z.2, z.1) ∈ A.chart.source :=
          continuous_swap.continuousAt.eventually (A.chart.open_source.mem_nhds hqs)
        filter_upwards [hchart.eventually (hgerm _ hqboundary), hsource] with z hz hzs
        exact hz.symm.trans (A.height z.2 z.1 (A.source ▸ hzs).2))
    simpa only [mem_univ, forall_const] using hh
  obtain ⟨η, hη, hηheight⟩ := Metric.mem_nhds_iff.mp hnear
  let δ := min (η / 2) (min (A.reflected.delta / 2) ((c - a) / 2))
  have hδ : 0 < δ := lt_min (half_pos hη)
    (lt_min (half_pos A.reflected.delta_pos) (half_pos (sub_pos.mpr hac)))
  have hδη : δ < η := (min_le_left _ _).trans_lt (by linarith)
  have hδA : δ < A.reflected.delta :=
    ((min_le_right _ _).trans (min_le_left _ _)).trans_lt
      (by linarith [A.reflected.delta_pos])
  have hδa : δ < c - a :=
    ((min_le_right _ _).trans (min_le_right _ _)).trans_lt (by linarith)
  let W : Set (S1 × Real) := univ ×ˢ Ioo (c - δ) (D.center + δ)
  have hW : IsOpen W := isOpen_univ.prod isOpen_Ioo
  have hWs : W ⊆ A.chart.source := by
    rintro ⟨q, t⟩ ⟨_, ht⟩
    rw [A.source]
    exact ⟨mem_univ _, by linarith [ht.1, A.reflected.delta_pos], by linarith [ht.2]⟩
  let T := A.chart.restrOpen W hW
  refine ⟨δ, hδ, T, inter_eq_right.mpr hWs,
    A.smooth.mono inter_subset_left, A.symm_smooth.mono inter_subset_left,
    fun _ => rfl, ?_, A.boundary⟩
  intro q t ht
  change inner Real v (g (A.chart (q, t))) = t
  by_cases htc : D.center < t
  · apply hηheight (show t ∈ ball D.center η from ?_) q
    rw [mem_ball, Real.dist_eq, abs_lt]
    exact ⟨by linarith, by linarith [ht.2]⟩
  · exact A.actual_height q t ⟨by linarith [ht.1], le_of_not_gt htc⟩

end Poincare.Manifold.Schoenflies.Saddle.Wall.Smoothing.Exterior.Caps

end

end M38Schoenflies
