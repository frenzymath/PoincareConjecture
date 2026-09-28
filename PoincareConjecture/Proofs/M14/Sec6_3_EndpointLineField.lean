import PoincareConjecture.Proofs.M14.Sec6_3_GaugeEndpointFamily
import PoincareConjecture.Proofs.M14.Sec6_2_LocalTestField
import PoincareConjecture.Proofs.M14.Sec6_4_FixedEndpointBoundary










set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T a b : ℝ} {x y : G.Point} {p : M14BackwardPath G T a b x y}
  {R : M14SquareRootPath G p}

private theorem horizontal_transport_val {q r : G.Point} (h : q = r)
    (v : G.Horizontal q) : (h.symm ▸ v : G.Horizontal r).val = v.val := by
  cases h
  rfl




theorem variationField_gauge_germ (V : M14LVariationData G p R) {s : ℝ}
    (hs : s ∈ M14SqrtParameterInterval a b) (j : G.gaugeCover.index)
    (t : (G.timeIntervals.interval (G.gaugeCover.interval j)).Point)
    (q : G.gaugeCover.spatial j) (w : EuclideanSpace ℝ (Fin n))
    (h : (fun u => V.squareFamily s u) =ᶠ[𝓝 0] fun u =>
      (G.gaugeCover.cylinder j).toSpacetime (t, (G.gaugeCover.spatial j).affineShift q (u • w))) :
    (M14VariationField V s).val = ((G.gaugeCover.metric j).spatialTangentEquiv t q w).val := by
  have h0 : (0 : ℝ) ∈ V.parameterDomain := by
    rw [V.parameterDomain_eq]
    exact ⟨neg_lt_zero.mpr V.radius_pos, V.radius_pos⟩
  have hv := (horizontal_transport_val (V.square_base s) (M14EndpointVariationField V s 0)).trans
    (endpointVariationField_val_eq_tangent V hs h0)
  rw [h.mfderiv_eq (I := 𝓘(ℝ, ℝ)) (I' := spacetimeModel n)] at hv
  exact hv.trans (gaugeShiftFamily_parameter_mfderiv R j (fun _ => (t, q)) (fun _ => w) s)

namespace GaugeEndpointFamily

variable {f : ℝ × ℝ → G.Point} {U : Set ℝ} {B c : ℝ}
  {j : G.gaugeCover.index}
  {lift : G.Point → (G.timeIntervals.interval (G.gaugeCover.interval j)).Point ×
    G.gaugeCover.spatial j}
  (D : GaugeEndpointFamily f U T 0 B c 0 j lift)




theorem variationField_line_marked (V : M14LVariationData G p R)
    (hc : c ∈ M14SqrtParameterInterval a b)
    (z d : ℝ × EuclideanSpace ℝ (Fin n)) (hz : z ∈ D.parameters)
    (hparam : ∀ u ∈ V.parameterDomain, z + u • d ∈ D.parameters)
    (hV : ∀ u, V.squareFamily c u = D.family (c, z + u • d)) :
    ∃ hy : z.2 ∈ G.gaugeCover.spatial j,
      (M14VariationField V c).val = ((G.gaugeCover.metric j).spatialTangentEquiv
        (lift (f (c, 0))).1 ⟨z.2, hy⟩ d.2).val := by
  obtain ⟨hy, _⟩ := D.marked z hz
  refine ⟨hy, variationField_gauge_germ V hc j (lift (f (c, 0))).1 ⟨z.2, hy⟩ d.2 ?_⟩
  have h0 : (0 : ℝ) ∈ V.parameterDomain := by
    rw [V.parameterDomain_eq]
    exact ⟨neg_lt_zero.mpr V.radius_pos, V.radius_pos⟩
  have hP : IsOpen V.parameterDomain := V.parameterDomain_eq ▸ isOpen_Ioo
  filter_upwards [hP.mem_nhds h0] with u hu
  obtain ⟨hyu, hmark⟩ := D.marked _ (hparam u hu)
  have hshift : (⟨(z + u • d).2, hyu⟩ : G.gaugeCover.spatial j) =
      (G.gaugeCover.spatial j).affineShift ⟨z.2, hy⟩ (u • d.2) :=
    Subtype.ext ((G.gaugeCover.spatial j).affineShift_val
      (x := ⟨z.2, hy⟩) (v := u • d.2) hyu).symm
  exact (hV u).trans (hmark.trans
    (congrArg (fun q => (G.gaugeCover.cylinder j).toSpacetime ((lift (f (c, 0))).1, q)) hshift))



theorem variationField_line_initial_zero (V : M14LVariationData G p R)
    (z d : ℝ × EuclideanSpace ℝ (Fin n))
    (hparam : ∀ u ∈ V.parameterDomain, z + u • d ∈ D.parameters)
    (hV : ∀ u, V.squareFamily 0 u = D.family (0, z + u • d))
    (hleft : ∀ r ∈ U, f (0, r) = x) : M14VariationField V 0 = 0 := by
  have hfixed (u : ℝ) (hu : u ∈ V.parameterDomain) : V.squareFamily 0 u = x :=
    (hV u).trans ((D.initial _ (hparam u hu)).trans
      (hleft _ (D.parameter_subset _ (hparam u hu))))
  have h0 : (0 : ℝ) ∈ V.parameterDomain := by
    rw [V.parameterDomain_eq]
    exact ⟨neg_lt_zero.mpr V.radius_pos, V.radius_pos⟩
  apply variationField_eq_zero_of_constant V
  intro u hu
  exact (hfixed u hu).trans (hfixed 0 h0).symm

end GaugeEndpointFamily

end PoincareConjecture.M14
