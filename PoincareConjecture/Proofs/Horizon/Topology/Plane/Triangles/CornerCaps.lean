


import PoincareConjecture.Proofs.Horizon.Analysis.Calculus.ImplicitFunction.Quadrants
import PoincareConjecture.Proofs.Horizon.Topology.Plane.Triangles.CurvedCap








set_option autoImplicit false
open Set Metric Filter
open scoped ContDiff Topology Matrix

namespace Poincare.Topology.Plane.Triangles

private theorem coordinate_derivative_equiv
    (H : OpenPartialHomeomorph (ℝ × ℝ) (EuclideanSpace ℝ (Fin 2)))
    (h0 : (0 : ℝ × ℝ) ∈ H.source)
    (hH : ContDiffOn ℝ ∞ H H.source) (hI : ContDiffOn ℝ ∞ H.symm H.target) :
    ∃ L : (ℝ × ℝ) ≃L[ℝ] EuclideanSpace ℝ (Fin 2),
      HasFDerivAt H L.toContinuousLinearMap 0 ∧
      HasFDerivAt H.symm L.symm.toContinuousLinearMap (H 0) := by
  let A := fderiv ℝ H 0
  let B := fderiv ℝ H.symm (H 0)
  have hdH : HasFDerivAt H A 0 :=
    ((hH 0 h0).contDiffAt (H.open_source.mem_nhds h0)).differentiableAt
      (by simp) |>.hasFDerivAt
  have hdI : HasFDerivAt H.symm B (H 0) :=
    ((hI (H 0) (H.map_source h0)).contDiffAt
      (H.open_target.mem_nhds (H.map_source h0))).differentiableAt
      (by simp) |>.hasFDerivAt
  have hBA : B.comp A = ContinuousLinearMap.id ℝ (ℝ × ℝ) :=
    (hdI.comp 0 hdH).unique ((hasFDerivAt_id (0 : ℝ × ℝ)).congr_of_eventuallyEq
      (H.eventually_left_inverse h0))
  have hdH' : HasFDerivAt H A (H.symm (H 0)) := by
    simpa only [H.left_inv h0] using hdH
  have hAB : A.comp B = ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 2)) :=
    (hdH'.comp (H 0) hdI).unique ((hasFDerivAt_id (H 0)).congr_of_eventuallyEq
      (H.eventually_right_inverse (H.map_source h0)))
  exact ⟨ContinuousLinearEquiv.equivOfInverse' A B hAB hBA, hdH, hdI⟩





theorem exists_smooth_coordinate_corner_caps
    (H : OpenPartialHomeomorph (ℝ × ℝ) (EuclideanSpace ℝ (Fin 2)))
    (h0 : (0 : ℝ × ℝ) ∈ H.source)
    (hH : ContDiffOn ℝ ∞ H H.source) (hI : ContDiffOn ℝ ∞ H.symm H.target) :
    ∃ δ > 0, ∀ ε : ℝ, 0 < ε → ε < δ →
      ∃ F : OpenPartialHomeomorph (ℝ × ℝ) (EuclideanSpace ℝ (Fin 2)),
        {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 + q.2 ≤ ε} ⊆ F.source ∧
        F.target ⊆ H.target ∧
        ContDiffOn ℝ ∞ F F.source ∧ ContDiffOn ℝ ∞ F.symm F.target ∧
        (∀ s : ℝ, |s| < δ → F (s, 0) = H (s, 0)) ∧
        (∀ t : ℝ, |t| < δ → F (0, t) = H (0, t)) ∧
        (∀ t : ℝ, F (t * ε, (1 - t) * ε) =
          (1 - t) • H (0, ε) + t • H (ε, 0)) ∧
        (∀ s t : ℝ, |s| < δ → |t| < δ →
          ((0 < (H.symm (F (s, t))).1 ↔ 0 < s) ∧
            ((H.symm (F (s, t))).1 = 0 ↔ s = 0) ∧
            (0 ≤ (H.symm (F (s, t))).1 ↔ 0 ≤ s)) ∧
          ((0 < (H.symm (F (s, t))).2 ↔ 0 < t) ∧
            ((H.symm (F (s, t))).2 = 0 ↔ t = 0) ∧
            (0 ≤ (H.symm (F (s, t))).2 ↔ 0 ≤ t))) ∧
        F '' {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 + q.2 ≤ ε} ⊆
          H '' (H.source ∩ {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2}) ∧
        ∃ V : Set (EuclideanSpace ℝ (Fin 2)), IsOpen V ∧ H 0 ∈ V ∧ V ⊆ H.target ∧
          V ∩ H '' (H.source ∩ {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2}) ⊆
            F '' {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 + q.2 ≤ ε} := by
  let A : Set ℝ := (fun s : ℝ => (s, (0 : ℝ))) ⁻¹' H.source
  let B : Set ℝ := (fun t : ℝ => ((0 : ℝ), t)) ⁻¹' H.source
  have hA : IsOpen A := H.open_source.preimage (continuous_id.prodMk continuous_const)
  have hB : IsOpen B := H.open_source.preimage (continuous_const.prodMk continuous_id)
  have hA0 : 0 ∈ A := h0
  have hB0 : 0 ∈ B := h0
  obtain ⟨f, hf, hfeq⟩ := Poincare.Analysis.exists_global_contDiff_germ hA
    (hH.comp (contDiff_id.prodMk contDiff_const).contDiffOn (fun _ hs => hs)) hA0
  obtain ⟨g, hg, hgeq⟩ := Poincare.Analysis.exists_global_contDiff_germ hB
    (hH.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun _ ht => ht)) hB0
  have hbase : g 0 = f 0 := hgeq.eq_of_nhds.trans hfeq.eq_of_nhds.symm
  obtain ⟨L, hdH, hdI⟩ := coordinate_derivative_equiv H h0 hH hI
  have hpathf : HasDerivAt (fun s : ℝ => (s, (0 : ℝ))) (1, 0) 0 :=
    (hasDerivAt_id (0 : ℝ)).prodMk (hasDerivAt_const (0 : ℝ) (0 : ℝ))
  have hpathg : HasDerivAt (fun t : ℝ => ((0 : ℝ), t)) (0, 1) 0 :=
    (hasDerivAt_const (0 : ℝ) (0 : ℝ)).prodMk (hasDerivAt_id (0 : ℝ))
  have hdf : deriv f 0 = L (1, 0) :=
    hfeq.deriv_eq.trans (hdH.comp_hasDerivAt (f := fun s : ℝ => (s, 0)) 0 hpathf).deriv
  have hdg : deriv g 0 = L (0, 1) :=
    hgeq.deriv_eq.trans (hdH.comp_hasDerivAt (f := fun t : ℝ => (0, t)) 0 hpathg).deriv
  have hind : LinearIndependent ℝ
      (![deriv f 0, deriv g 0] : Fin 2 → EuclideanSpace ℝ (Fin 2)) := by
    rw [hdf, hdg, linearIndependent_fin2]
    constructor
    · simp
    · intro a ha
      have he : L (a • (0, 1)) = L (1, 0) := by rw [map_smul]; exact ha
      have := congrArg Prod.fst (L.injective he)
      simp at this
  have hL (q : ℝ × ℝ) : L q = q.1 • deriv f 0 + q.2 • deriv g 0 := by
    rw [hdf, hdg, ← map_smul, ← map_smul, ← map_add]
    congr 1
    ext <;> simp
  have haxis : ∀ᶠ u in 𝓝 (0 : ℝ),
      f u = H (u, 0) ∧ g u = H (0, u) ∧ (u, 0) ∈ H.source ∧ (0, u) ∈ H.source := by
    filter_upwards [hfeq, hgeq, hA.eventually_mem hA0, hB.eventually_mem hB0]
      with u hf' hg' hA' hB'
    exact ⟨hf', hg', hA', hB'⟩
  obtain ⟨η, hη, hηball⟩ := Metric.mem_nhds_iff.mp haxis
  have haxis' {u : ℝ} (hu : |u| < η) :=
    hηball (show u ∈ ball (0 : ℝ) η by simpa [mem_ball, Real.dist_eq] using hu)
  let C (p : ℝ × (ℝ × ℝ)) := curvedCapMap f g p.1 p.2
  have hC : ContDiff ℝ ∞ C := contDiff_curvedCapMap hf hg
  have hC0 : C (0, (0, 0)) = H 0 :=
    (curvedCapMap_first_axis f g hbase 0 0).trans hfeq.eq_of_nhds
  have hdC : HasFDerivAt C
      (L.toContinuousLinearMap.comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)))
      (0, (0, 0)) := (hasStrictFDerivAt_curvedCapMap_zero hf hg L hL).hasFDerivAt
  let K (p : ℝ × (ℝ × ℝ)) := H.symm (C p)
  have hIsmooth : ContDiffAt ℝ ∞ H.symm (C (0, (0, 0))) := by
    rw [hC0]
    exact (hI (H 0) (H.map_source h0)).contDiffAt
      (H.open_target.mem_nhds (H.map_source h0))
  have hKsmooth : ContDiffAt ℝ 1 K (0, (0, 0)) :=
    (hIsmooth.comp (0, (0, 0)) hC.contDiffAt).of_le (by simp)
  have hdI' : HasFDerivAt H.symm L.symm.toContinuousLinearMap (C (0, (0, 0))) := by
    simpa only [hC0] using hdI
  have hdK : HasFDerivAt K (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)) (0, (0, 0)) := by
    apply (hdI'.comp (0, (0, 0)) hdC).congr_fderiv
    apply ContinuousLinearMap.ext
    intro p
    change L.symm (L p.2) = p.2
    exact L.symm_apply_apply p.2
  have hKaxes : ∀ᶠ p in 𝓝 (0, (0, 0)),
      (p.2.1 = 0 → (K p).1 = 0) ∧ (p.2.2 = 0 → (K p).2 = 0) := by
    have hsT : ContinuousAt (fun p : ℝ × (ℝ × ℝ) => p.2.1) (0, (0, 0)) :=
      (continuous_fst.comp continuous_snd).continuousAt
    have htT : ContinuousAt (fun p : ℝ × (ℝ × ℝ) => p.2.2) (0, (0, 0)) :=
      (continuous_snd.comp continuous_snd).continuousAt
    filter_upwards [hsT.eventually haxis, htT.eventually haxis] with p hs ht
    rcases p with ⟨ε, s, t⟩
    constructor
    · intro hs0
      change s = 0 at hs0
      subst s
      change (H.symm (curvedCapMap f g ε (0, t))).1 = 0
      rw [curvedCapMap_second_axis, ht.2.1, H.left_inv ht.2.2.2]
    · intro ht0
      change t = 0 at ht0
      subst t
      change (H.symm (curvedCapMap f g ε (s, 0))).2 = 0
      rw [curvedCapMap_first_axis f g hbase, hs.1, H.left_inv hs.2.2.1]
  obtain ⟨r, hr, hsign⟩ :=
    Poincare.Analysis.exists_quadrant_preserving_radius hKsmooth hdK hKaxes
  obtain ⟨ρ, hρ, hcap⟩ := exists_smooth_triangular_cap_coordinates hf hg hbase hind
    H.open_target (hfeq.eq_of_nhds.symm ▸ H.map_source h0)
  let δ := min ρ (min r η)
  have hδ : 0 < δ := lt_min hρ (lt_min hr hη)
  have hδρ : δ ≤ ρ := min_le_left _ _
  have hδr : δ ≤ r := (min_le_right _ _).trans (min_le_left _ _)
  have hδη : δ ≤ η := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨δ, hδ, ?_⟩
  intro ε hε hεδ
  obtain ⟨F, hF, hsource, htarget, hFsmooth, hFinv, hfaxis, hgaxis, hchord⟩ :=
    hcap ε hε (hεδ.trans_le hδρ)
  have hεabs : |ε| < δ := by rwa [abs_of_pos hε]
  have hsignF : ∀ s t : ℝ, |s| < δ → |t| < δ →
      ((0 < (H.symm (F (s, t))).1 ↔ 0 < s) ∧
        ((H.symm (F (s, t))).1 = 0 ↔ s = 0) ∧
        (0 ≤ (H.symm (F (s, t))).1 ↔ 0 ≤ s)) ∧
      ((0 < (H.symm (F (s, t))).2 ↔ 0 < t) ∧
        ((H.symm (F (s, t))).2 = 0 ↔ t = 0) ∧
        (0 ≤ (H.symm (F (s, t))).2 ↔ 0 ≤ t)) := by
    intro s t hs ht
    simpa only [hF, K, C] using hsign ε s t (hεabs.trans_le hδr)
      (hs.trans_le hδr) (ht.trans_le hδr)
  refine ⟨F, hsource, htarget, hFsmooth, hFinv,
    (fun s hs => (hfaxis s).trans (haxis' (hs.trans_le hδη)).1),
    (fun t ht => (hgaxis t).trans (haxis' (ht.trans_le hδη)).2.1), ?_, hsignF, ?_, ?_⟩
  · intro t
    rw [hchord, (haxis' (hεabs.trans_le hδη)).1, (haxis' (hεabs.trans_le hδη)).2.1]
  · rintro z ⟨q, hq, rfl⟩
    have hs : |q.1| < δ := by
      rw [abs_of_nonneg hq.1]
      exact (by linarith [hq.2.1, hq.2.2] : q.1 ≤ ε).trans_lt hεδ
    have ht : |q.2| < δ := by
      rw [abs_of_nonneg hq.2.1]
      exact (by linarith [hq.1, hq.2.2] : q.2 ≤ ε).trans_lt hεδ
    have hz : F q ∈ H.target := htarget (F.map_source (hsource hq))
    exact ⟨H.symm (F q), ⟨H.map_target hz,
      (hsignF q.1 q.2 hs ht).1.2.2.mpr hq.1,
      (hsignF q.1 q.2 hs ht).2.2.2.mpr hq.2.1⟩, H.right_inv hz⟩
  · let W : Set (ℝ × ℝ) := {q | |q.1| < δ ∧ |q.2| < δ ∧ q.1 + q.2 < ε}
    have hW : IsOpen W := (isOpen_lt continuous_fst.abs continuous_const).inter
      ((isOpen_lt continuous_snd.abs continuous_const).inter
        (isOpen_lt (continuous_fst.add continuous_snd) continuous_const))
    refine ⟨F '' (F.source ∩ W), F.isOpen_image_source_inter hW, ?_, ?_, ?_⟩
    · refine ⟨0, ⟨hsource ?_, ?_⟩, ?_⟩
      · exact ⟨le_rfl, le_rfl, by simpa using hε.le⟩
      · simpa [W] using And.intro hδ (And.intro hδ hε)
      · exact (hfaxis 0).trans hfeq.eq_of_nhds
    · rintro z ⟨q, hq, rfl⟩
      exact htarget (F.map_source hq.1)
    · rintro z ⟨⟨q, ⟨hqsource, hqW⟩, rfl⟩, ⟨v, ⟨hvsource, hv⟩, hveq⟩⟩
      have hv' : H.symm (F q) = v := by rw [← hveq, H.left_inv hvsource]
      have hs := hsignF q.1 q.2 hqW.1 hqW.2.1
      refine ⟨q, ⟨hs.1.2.2.mp ?_, hs.2.2.2.mp ?_, hqW.2.2.le⟩, rfl⟩
      · simpa only [hv'] using hv.1
      · simpa only [hv'] using hv.2

end Poincare.Topology.Plane.Triangles
