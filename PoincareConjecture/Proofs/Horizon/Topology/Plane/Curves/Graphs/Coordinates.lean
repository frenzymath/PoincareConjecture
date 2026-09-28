import PoincareConjecture.Proofs.Horizon.Topology.Plane.Curves.Collar
import PoincareConjecture.Proofs.Horizon.Topology.Plane.Curves.TransverseLevels
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.InnerProductSpace.Calculus

set_option autoImplicit false

open Set
open scoped ContDiff Topology

namespace Poincare.Topology.Plane.Curves

theorem exists_smooth_interval_inverse_of_deriv_pos
    {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) {a b : ℝ} (hab : a ≤ b)
    (hpos : ∀ t ∈ Icc a b, 0 < deriv g t) :
    ∃ (l u : ℝ) (G : OpenPartialHomeomorph ℝ ℝ),
      l < a ∧ b < u ∧ G.source = Ioo l u ∧ (∀ t, G t = g t) ∧
      (∀ t ∈ G.source, 0 < deriv g t) ∧ StrictMonoOn g G.source ∧
      ContDiffOn ℝ ∞ G G.source ∧ ContDiffOn ℝ ∞ G.symm G.target ∧
      g '' Icc a b = Icc (g a) (g b) ∧ Icc (g a) (g b) ⊆ G.target := by
  let P : Set ℝ := {t | 0 < deriv g t}
  have hPopen : IsOpen P :=
    isOpen_lt continuous_const (contDiff_infty_iff_deriv.mp hg).2.continuous
  obtain ⟨l, r, ha, hlr⟩ := mem_nhds_iff_exists_Ioo_subset.mp
    (hPopen.mem_nhds (hpos a (left_mem_Icc.mpr hab)))
  obtain ⟨s, u, hb, hsu⟩ := mem_nhds_iff_exists_Ioo_subset.mp
    (hPopen.mem_nhds (hpos b (right_mem_Icc.mpr hab)))
  let W := Ioo l u
  have hWpos : ∀ t ∈ W, 0 < deriv g t := by
    intro t ht
    by_cases hta : t < a
    · exact hlr ⟨ht.1, hta.trans ha.2⟩
    by_cases hbt : b < t
    · exact hsu ⟨hb.1.trans hbt, ht.2⟩
    exact hpos t ⟨le_of_not_gt hta, le_of_not_gt hbt⟩
  have hWmono : StrictMonoOn g W :=
    strictMonoOn_of_deriv_pos (convex_Ioo _ _) hg.continuous.continuousOn
      (fun t ht => hWpos t (interior_subset ht))
  have hWsub : Icc a b ⊆ W :=
    fun _ ht => ⟨ha.1.trans_le ht.1, ht.2.trans_lt hb.2⟩
  have hopenmap : IsOpenMap (W.domRestrict g) := by
    apply isOpenMap_iff_nhds_le.mpr
    intro t
    have hd := (hg.hasStrictDerivAt (x := (t : ℝ)) (by simp)).hasStrictFDerivAt_equiv
      (ne_of_gt (hWpos t t.property))
    change 𝓝 (g t) ≤ Filter.map (g ∘ Subtype.val) (𝓝 t)
    rw [← Filter.map_map, isOpen_Ioo.isOpenEmbedding_subtypeVal.map_nhds_eq,
      hd.map_nhds_eq_of_equiv]
  let G := OpenPartialHomeomorph.ofContinuousOpenRestrict
    (hWmono.injOn.toPartialEquiv g W) hg.continuous.continuousOn hopenmap isOpen_Ioo
  have hGimage : g '' Icc a b = Icc (g a) (g b) :=
    hg.continuous.continuousOn.image_Icc_of_monotoneOn hab (hWmono.monotoneOn.mono hWsub)
  refine ⟨l, u, G, ha.1, hb.2, rfl, fun _ => rfl, hWpos, hWmono,
    hg.contDiffOn, ?_, hGimage, ?_⟩
  · intro x hx
    have hd := (hg.hasStrictDerivAt (x := G.symm x) (by simp)).hasStrictFDerivAt_equiv
      (ne_of_gt (hWpos (G.symm x) (G.map_target hx)))
    exact (G.contDiffAt_symm hx hd.hasFDerivAt hg.contDiffAt).contDiffWithinAt
  · rw [← hGimage]
    rintro _ ⟨t, ht, rfl⟩
    exact G.map_source (hWsub ht)

theorem exists_tangent_projection_coordinates
    {v : EuclideanSpace ℝ (Fin 2)} (hv : v ≠ 0) :
    ∃ L : EuclideanSpace ℝ (Fin 2) ≃L[ℝ] (ℝ × ℝ),
      ∀ z, L z = (inner ℝ v z, inner ℝ (quarterTurn v) z) := by
  have ha : innerSL ℝ v ≠ 0 := by
    intro h
    have hzero := congrArg (fun A : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ => A v) h
    exact (real_inner_self_pos.mpr hv).ne' hzero
  have hJv : quarterTurn v ≠ 0 := by
    intro h
    exact hv (quarterTurn.injective (by simpa using h))
  exact exists_equiv_of_transverse_functionals (a := innerSL ℝ v)
    (b := innerSL ℝ (quarterTurn v)) ha (inner_quarterTurn_self v)
    (real_inner_self_pos.mpr hJv).ne'

theorem exists_graph_coordinates_of_positive_projection
    {f : ℝ → EuclideanSpace ℝ (Fin 2)} (hf : ContDiff ℝ ∞ f)
    {a b : ℝ} (hab : a ≤ b) {v : EuclideanSpace ℝ (Fin 2)}
    (hpos : ∀ t ∈ Icc a b, 0 < inner ℝ v (deriv f t)) :
    ∃ (l u : ℝ) (G : OpenPartialHomeomorph ℝ ℝ)
      (L : EuclideanSpace ℝ (Fin 2) ≃L[ℝ] (ℝ × ℝ)) (h : ℝ → ℝ),
      l < a ∧ b < u ∧ G.source = Ioo l u ∧
      (∀ t, G t = inner ℝ v (f t)) ∧
      (∀ z, L z = (inner ℝ v z, inner ℝ (quarterTurn v) z)) ∧
      StrictMonoOn (fun t => inner ℝ v (f t)) G.source ∧
      ContDiffOn ℝ ∞ G G.source ∧ ContDiffOn ℝ ∞ G.symm G.target ∧
      (∀ x, h x = inner ℝ (quarterTurn v) (f (G.symm x))) ∧
      ContDiffOn ℝ ∞ h G.target ∧
      (∀ t ∈ G.source, L (f t) = (G t, h (G t))) ∧
      G '' Icc a b = Icc (G a) (G b) ∧ Icc (G a) (G b) ⊆ G.target ∧
      L '' (f '' Icc a b) = (fun x => (x, h x)) '' Icc (G a) (G b) := by
  let g : ℝ → ℝ := fun t => inner ℝ v (f t)
  have hg : ContDiff ℝ ∞ g := contDiff_const.inner ℝ hf
  have hgderiv (t : ℝ) : deriv g t = inner ℝ v (deriv f t) := by
    simpa [g] using ((hasDerivAt_const t v).inner ℝ
      ((hf.differentiable (by simp)) t).hasDerivAt).deriv
  have hgpos : ∀ t ∈ Icc a b, 0 < deriv g t := by
    intro t ht
    rw [hgderiv]
    exact hpos t ht
  obtain ⟨l, u, G, hla, hbu, hsource, hG, _, hmono, hGsmooth, hGinv, hGimage, htarget⟩ :=
    exists_smooth_interval_inverse_of_deriv_pos hg hab hgpos
  have hv : v ≠ 0 := by
    intro hv
    have h := hpos a (left_mem_Icc.mpr hab)
    simp [hv] at h
  obtain ⟨L, hL⟩ := exists_tangent_projection_coordinates hv
  let h : ℝ → ℝ := fun x => inner ℝ (quarterTurn v) (f (G.symm x))
  have hgraph (t : ℝ) (ht : t ∈ G.source) : L (f t) = (G t, h (G t)) := by
    rw [hL, hG]
    change (g t, inner ℝ (quarterTurn v) (f t)) =
      (g t, inner ℝ (quarterTurn v) (f (G.symm (g t))))
    rw [← hG t, G.left_inv ht]
  have himage : G '' Icc a b = Icc (G a) (G b) := by simpa only [hG] using hGimage
  have hIccsub : Icc a b ⊆ G.source := by
    rw [hsource]
    exact fun _ ht => ⟨hla.trans_le ht.1, ht.2.trans_lt hbu⟩
  refine ⟨l, u, G, L, h, hla, hbu, hsource, hG, hL, hmono, hGsmooth, hGinv,
    fun _ => rfl, ?_, hgraph, himage, ?_, ?_⟩
  · exact contDiffOn_const.inner ℝ (hf.comp_contDiffOn hGinv)
  · simpa only [hG] using htarget
  · rw [← himage, image_image, image_image]
    apply image_congr
    intro t ht
    exact hgraph t (hIccsub ht)

end Poincare.Topology.Plane.Curves
