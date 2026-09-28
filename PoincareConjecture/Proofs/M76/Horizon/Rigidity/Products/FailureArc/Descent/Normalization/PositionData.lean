import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Normalization.Construction
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Normalization.Intersections.DoubleGraph
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Normalization.Intersections.Exceptional
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.FiniteAmbientFamilies










set_option autoImplicit false
open Set Geometry Topology

namespace Geometry.OriginalPLTower

local notation "V3" => (Fin 3 → ℝ)

variable {U V M ι : Type*}
  [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [TopologicalSpace M]
  {e : ι → OpenPartialHomeomorph M V3} {S : SimplicialComplex ℝ U}
  {f : U → M} {r : M → ℝ} {C : Set M}

structure MarkedSurfacePositionData {s t : Stage e S f r C} (step : Step s t)
    (K₀ A₀ : SimplicialComplex ℝ V) (j : V → t.Carrier) (R Fmark : Set M) where
  K : SimplicialComplex ℝ V
  A : SimplicialComplex ℝ V
  source_finite : K.faces.Finite
  source_space : K.space = K₀.space
  source_dimension : ∀ a ∈ K.faces, a.card ≤ 3
  boundary_finite : A.faces.Finite
  boundary_subcomplex : A ≤ K
  boundary_space : A.space = A₀.space
  boundary_dimension : ∀ a ∈ A.faces, a.card ≤ 2
  length : ℕ
  order : Fin length → K.faces
  previous : ℕ → SimplicialComplex ℝ V
  boundary : Fin length → Bool
  upperChart : Fin length → OpenPartialHomeomorph t.Carrier V3
  lowerChart : Fin length → OpenPartialHomeomorph s.Carrier V3
  carrier : Fin length → SimplicialComplex ℝ V3
  window : K.faces → Set t.Carrier
  states : ℕ → MarkedSurfaceState t K window R Fmark A₀.space
  initial : MarkedSurfaceState t K window R Fmark A₀.space
  motions : ∀ i : Fin length, MarkedSurfaceMotionData step K (previous i.val)
    (previous (i.val + 1)) (states i.val).map (upperChart i) (lowerChart i)
    (carrier i) window R Fmark (boundary i)
  order_bijective : Function.Bijective order
  order_before : ∀ i k, (order k).val ⊂ (order i).val → k < i
  boundary_phase : ∀ i k, k < i → (order i).val ∈ A.faces → (order k).val ∈ A.faces
  previous_faces : ∀ k, previous k ≤ K ∧
    (previous k).faces = {a | ∃ i : Fin length, i.val < k ∧ (order i).val = a}
  successor_space : ∀ i : Fin length, (previous (i.val + 1)).space =
    (previous i.val).space ∪ convexHull ℝ ((order i).val : Set V)
  boundary_iff : ∀ i, boundary i = true ↔ (order i).val ∈ A.faces
  upper_compatible : ∀ i k,
    (t.charts k).symm.trans (upperChart i) ∈ piecewiseAffineGroupoid V3
  lower_compatible : ∀ i k,
    (s.charts k).symm.trans (lowerChart i) ∈ piecewiseAffineGroupoid V3
  chart_values : ∀ i z,
    upperChart i z = lowerChart i (step.projection (step.inclusion z))
  chart_mapsTo : ∀ i, MapsTo (step.projection ∘ step.inclusion)
    (upperChart i).source (lowerChart i).source
  window_subset : ∀ i, window (order i) ⊆ (upperChart i).source
  first_state : (states 0).map = j
  final_state : initial.map = (states length).map
  transitions : ∀ i : Fin length,
    (states (i.val + 1)).map = (motions i).ambient 1 ∘ (states i.val).map
  stable : ∀ i k, i ≤ k → k ≤ length →
    EqOn (states k).map (states i).map (previous i).space
  cell_injective : ∀ a : K.faces,
    InjOn ((step.projection ∘ step.inclusion) ∘ initial.map)
      (convexHull ℝ (a.val : Set V))
  relation : SimplicialComplex ℝ (V × V)
  locus : SimplicialComplex ℝ V
  first : relation.space ≃ₜ locus.space
  exceptional : Set (V × V)
  relation_finite : relation.faces.Finite
  locus_finite : locus.faces.Finite
  relation_space : relation.space = {z | z.1 ∈ K₀.space ∧ z.2 ∈ K₀.space ∧
    step.projection (step.inclusion (initial.map z.1)) =
      step.projection (step.inclusion (initial.map z.2)) ∧ z.1 ≠ z.2}
  locus_space : locus.space = {x | x ∈ K₀.space ∧ ∃ y ∈ K₀.space, x ≠ y ∧
    step.projection (step.inclusion (initial.map x)) =
      step.projection (step.inclusion (initial.map y))}
  relation_dimension : ∀ a ∈ relation.faces, a.card ≤ 2
  locus_dimension : ∀ a ∈ locus.faces, a.card ≤ 2
  first_PL : first.IsFinitePL
  first_inverse_PL : first.symm.IsFinitePL
  first_value : ∀ z : relation.space, (first z : V) = z.val.1
  exceptional_finite : exceptional.Finite
  exceptional_eq : exceptional = {z | z ∈ relation.space ∧
    ∃ a ∈ K.faces, a.card ≤ 2 ∧
      (z.1 ∈ convexHull ℝ (a : Set V) ∨ z.2 ∈ convexHull ℝ (a : Set V))}

theorem Step.nonempty_markedSurfacePositionData
    {s t : Stage e S f r C} (step : Step s t) {R Fmark : Set M}
    (K₀ A₀ : SimplicialComplex ℝ V) (hK₀ : K₀.faces.Finite) (hA₀ : A₀.faces.Finite)
    (hKdim : ∀ a ∈ K₀.faces, a.card ≤ 3) (hAdim : ∀ a ∈ A₀.faces, a.card ≤ 2)
    (hA₀K₀ : A₀.space ⊆ K₀.space)
    (he : PoincareConjecture.M76.PLDomain e R)
    (hF : Fmark ⊆ frontier R)
    (hopen : IsOpen ((Subtype.val : frontier R → M) ⁻¹' Fmark))
    {j : V → t.Carrier} (hj : PolyhedralPLInCharts t.charts j K₀.space)
    (hji : IsEmbedding (fun x : K₀.space => j x))
    (hjR : MapsTo j K₀.space (t.projection ⁻¹' R))
    (hproper : ∀ x : K₀.space, j x ∈ frontier (t.projection ⁻¹' R) ↔ (x : V) ∈ A₀.space)
    (hjF : ∀ x : A₀.space, t.projection (j x) ∈ Fmark) :
    Nonempty (MarkedSurfacePositionData step K₀ A₀ j R Fmark) := by
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
  let E : Set (V × V) := {z | z ∈ L.space ∧
    ∃ a ∈ K.faces, a.card ≤ 2 ∧
      (z.1 ∈ convexHull ℝ (a : Set V) ∨ z.2 ∈ convexHull ℝ (a : Set V))}
  have hE : E.Finite := by
    apply hexceptional.subset
    intro z hz
    have hh := hLs.subset hz.1
    exact ⟨hh.1, hh.2.1, hh.2.2.2, hh.2.2.1, hz.2⟩
  refine ⟨{
    K := K, A := A, source_finite := hK, source_space := hKs,
    source_dimension := hKcard, boundary_finite := hA, boundary_subcomplex := hAK,
    boundary_space := hAs, boundary_dimension := hAcard,
    length := n, order := order, previous := P, boundary := boundary,
    upperChart := Q, lowerChart := B, carrier := J, window := U,
    states := states, initial := states n, motions := motion,
    order_bijective := horder, order_before := hbefore, boundary_phase := hphase,
    previous_faces := fun k => ⟨(hP k).2.1, (hP k).2.2⟩,
    successor_space := hsucc, boundary_iff := hboundary,
    upper_compatible := fun i => (hcharts i).2.1,
    lower_compatible := fun i => (hcharts i).2.2.1,
    chart_values := fun i => (hcharts i).2.2.2.2.1,
    chart_mapsTo := fun i => (hcharts i).2.2.2.2.2.1,
    window_subset := fun i _ hx => (hUbox i hx).1,
    first_state := hinit, final_state := rfl, transitions := htransition,
    stable := hstable, cell_injective := hcell,
    relation := L, locus := D, first := H, exceptional := E,
    relation_finite := hL, locus_finite := hD,
    relation_space := ?_, locus_space := ?_,
    relation_dimension := hLcard, locus_dimension := hDcard,
    first_PL := hH, first_inverse_PL := hHi, first_value := hHv,
    exceptional_finite := hE, exceptional_eq := rfl }⟩
  · simpa only [hKs] using hLs
  · simpa only [hKs] using hDs

end Geometry.OriginalPLTower
