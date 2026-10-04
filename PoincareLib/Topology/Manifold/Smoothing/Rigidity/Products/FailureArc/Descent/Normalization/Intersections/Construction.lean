import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Descent.Normalization.Construction
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Descent.Normalization.Intersections.DoubleGraph
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Descent.Normalization.Intersections.Exceptional
import PoincareLib.Topology.Manifold.Smoothing.Dehn.General.Mathlib.FiniteAmbientFamilies

/-!
# Construct the full marked surface double graph and finite exceptional pairs

The actual normalization history constructs all intersection data. The source
and rim dimensions transfer through their exact finite carriers. No motion,
general-position comparison or finite double relation is supplied as input.
See Hudson1969, Lemma4.6, and Dehn032, sections6--8.
-/

set_option autoImplicit false
open Set Geometry Topology unitInterval

namespace Geometry.OriginalPLTower

local notation "V3" => (Fin 3 → ℝ)

variable {U V M ι : Type*}
  [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [TopologicalSpace M]
  {e : ι → OpenPartialHomeomorph M V3} {S : SimplicialComplex ℝ U}
  {f : U → M} {r : M → ℝ} {C : Set M}

theorem Step.exists_marked_surface_position_graph
    {s t : Stage e S f r C} (step : Step s t) {R Fmark : Set M}
    (K₀ A₀ : SimplicialComplex ℝ V) (hK₀ : K₀.faces.Finite) (hA₀ : A₀.faces.Finite)
    (hKdim : ∀ a ∈ K₀.faces, a.card ≤ 3) (hAdim : ∀ a ∈ A₀.faces, a.card ≤ 2)
    (hA₀K₀ : A₀.space ⊆ K₀.space)
    (he : PoincareMT.M76.PLDomain e R)
    (hF : Fmark ⊆ frontier R)
    (hopen : IsOpen ((Subtype.val : frontier R → M) ⁻¹' Fmark))
    {j : V → t.Carrier} (hj : PolyhedralPLInCharts t.charts j K₀.space)
    (hji : IsEmbedding (fun x : K₀.space => j x))
    (hjR : MapsTo j K₀.space (t.projection ⁻¹' R))
    (hproper : ∀ x : K₀.space, j x ∈ frontier (t.projection ⁻¹' R) ↔ (x : V) ∈ A₀.space)
    (hjF : ∀ x : A₀.space, t.projection (j x) ∈ Fmark) :
    ∃ (j' : V → t.Carrier) (ambient : I → t.Carrier ≃ₜ t.Carrier)
      (K : SimplicialComplex ℝ V) (L : SimplicialComplex ℝ (V × V))
      (D : SimplicialComplex ℝ V) (H : L.space ≃ₜ D.space),
      PolyhedralPLInCharts t.charts j' K₀.space ∧
      IsEmbedding (fun x : K₀.space => j' x) ∧
      MapsTo j' K₀.space (t.projection ⁻¹' R) ∧
      (∀ x : K₀.space, j' x ∈ frontier (t.projection ⁻¹' R) ↔ (x : V) ∈ A₀.space) ∧
      (∀ x : A₀.space, t.projection (j' x) ∈ Fmark) ∧
      Continuous (fun z : I × t.Carrier => ambient z.1 z.2) ∧
      Continuous (fun z : I × t.Carrier => (ambient z.1).symm z.2) ∧
      (∀ x, ambient 0 x = x) ∧
      (∀ a, (ambient a) ⁻¹' (t.projection ⁻¹' R) = t.projection ⁻¹' R ∧
        (ambient a) ⁻¹' (t.projection ⁻¹' Fmark) = t.projection ⁻¹' Fmark) ∧
      j' = ambient 1 ∘ j ∧
      K.faces.Finite ∧ K.space = K₀.space ∧
      L.faces.Finite ∧ D.faces.Finite ∧
      L.space = {z | z.1 ∈ K₀.space ∧ z.2 ∈ K₀.space ∧
        step.projection (step.inclusion (j' z.1)) =
          step.projection (step.inclusion (j' z.2)) ∧ z.1 ≠ z.2} ∧
      D.space = {x | x ∈ K₀.space ∧ ∃ y ∈ K₀.space, x ≠ y ∧
        step.projection (step.inclusion (j' x)) = step.projection (step.inclusion (j' y))} ∧
      (∀ a ∈ L.faces, a.card ≤ 2) ∧ (∀ a ∈ D.faces, a.card ≤ 2) ∧
      H.IsFinitePL ∧ H.symm.IsFinitePL ∧
      (∀ z : L.space, (H z : V) = z.val.1) ∧
      {z : V × V | z.1 ∈ K.space ∧ z.2 ∈ K.space ∧ z.1 ≠ z.2 ∧
        step.projection (step.inclusion (j' z.1)) =
          step.projection (step.inclusion (j' z.2)) ∧
        ∃ a ∈ K.faces, a.card ≤ 2 ∧
          (z.1 ∈ convexHull ℝ (a : Set V) ∨ z.2 ∈ convexHull ℝ (a : Set V))}.Finite := by
  classical
  obtain ⟨W, K, A, hW, hFW, hK, hKs, hA, hAK, hAs, hfull,
    n, order, horder, hbefore, hphase, P, hP, hP0, hPn, hPmono,
    boundary, Q, B, J, U, hboundary, hsucc, hphase', hcharts, hU, hUbox,
    states, hinit, hsteps, hstable, hcell⟩ :=
    step.exists_marked_surface_normalization_history K₀ A₀ hK₀ hA₀ hA₀K₀
      he hF hopen hj hji hjR hproper hjF
  have hKcard : ∀ a ∈ K.faces, a.card ≤ 3 := fun a ha =>
    K.face_card_le_of_hull_subset_finite_carrier K₀ hK₀ ha
      ((K.convexHull_subset_space ha).trans hKs.subset) hKdim
  have hAcard : ∀ a ∈ A.faces, a.card ≤ 2 := fun a ha =>
    A.face_card_le_of_hull_subset_finite_carrier A₀ hA₀ ha
      ((A.convexHull_subset_space ha).trans hAs.subset) hAdim
  choose motion htransition using fun i : Fin n => hsteps i.val i.isLt
  obtain ⟨L, D, H, hL, hD, hLs, hDs, hLcard, hDcard, hH, hHi, hHv⟩ :=
    step.exists_surface_history_double_graph hK hKcard A hAcard
      order horder hbefore hphase P (fun k => ⟨(hP k).2.1, (hP k).2.2⟩)
      hsucc boundary hboundary Q B J
      (fun i => (hcharts i).2.1) (fun i => (hcharts i).2.2.1)
      (fun i => (hcharts i).2.2.2.2.1) (fun i => (hcharts i).2.2.2.2.2.1)
      U (fun i _ hx => (hUbox i hx).1) states motion htransition hstable hcell
  have hexceptional := step.finite_surface_history_original_edge_pairs hK hKcard A hAcard
    order horder hbefore hphase P (fun k => ⟨(hP k).2.1, (hP k).2.2⟩)
    hsucc boundary hboundary Q B J (fun i => (hcharts i).2.1)
    (fun i => (hcharts i).2.2.2.2.1) (fun i => (hcharts i).2.2.2.2.2.1)
    U (fun i _ hx => (hUbox i hx).1) states motion htransition hstable hcell
  obtain ⟨ambient, hambient, hinverse, hzero, hsets, hfinal⟩ :=
    Homeomorph.exists_finite_family_history_composite
      (fun i => (motion i).ambient) (fun i => (motion i).continuous_ambient)
      (fun i => (motion i).continuous_inverse) (fun i => (motion i).zero)
      (fun i => (motion i).region) (fun i => (motion i).mark)
      (fun k => (states k).map) (fun i hi => htransition ⟨i, hi⟩)
  refine ⟨(states n).map, ambient, K, L, D, H, ?_, ?_, ?_, ?_, ?_,
    hambient, hinverse, hzero, hsets, ?_, hK, hKs, hL, hD, ?_, ?_,
    hLcard, hDcard, hH, hHi, hHv, hexceptional⟩
  · simpa only [← hKs] using (states n).original_PL
  · exact (states n).embedding.comp (Homeomorph.setCongr hKs.symm).isEmbedding
  · simpa only [← hKs] using (states n).region
  · intro x
    exact (states n).proper x (hKs.symm.subset x.property)
  · intro x
    exact (states n).mark x.property
  · rw [hfinal, hinit]
  · simpa only [hKs] using hLs
  · simpa only [hKs] using hDs

end Geometry.OriginalPLTower
