


import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Faces.Bands.Polygonal
import PoincareConjecture.Proofs.Horizon.Topology.Plane.Curves.Graphs.ObliquePolygonalBoundary








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology Matrix
open Poincare.Topology.Plane.Curves Poincare.Topology.Plane.Triangles

namespace PoincareConjecture.Topology.Surface

universe u

variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]


noncomputable def obliqueSurfaceCoordinates
    (F : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) M)
    {lo : ℝ → ℝ} {a b ua wa ub wb : ℝ}
    (P : TransverseGraphCuts lo a b ua wa ub wb)
    {X : Set ℝ} (hX : IsOpen X) (hlo : ContDiffOn ℝ ∞ lo X) :
    OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) M :=
  (((collarParameterEquiv.toHomeomorph.toOpenPartialHomeomorph.trans
      (P.coordinates hX hlo)).trans
    collarParameterEquiv.symm.toHomeomorph.toOpenPartialHomeomorph).trans F)

omit [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M] in
theorem obliqueSurfaceCoordinates_apply
    (F : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) M)
    {lo : ℝ → ℝ} {a b ua wa ub wb : ℝ}
    (P : TransverseGraphCuts lo a b ua wa ub wb)
    {X : Set ℝ} (hX : IsOpen X) (hlo : ContDiffOn ℝ ∞ lo X)
    (z : EuclideanSpace ℝ (Fin 2)) :
    obliqueSurfaceCoordinates F P hX hlo z =
      F (collarParameterEquiv.symm (P.coordinates hX hlo (collarParameterEquiv z))) := rfl

omit [T2Space M] [IsManifold (𝓡 2) ∞ M] in
theorem smooth_obliqueSurfaceCoordinates
    (F : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) M)
    (hF : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F F.source)
    {lo : ℝ → ℝ} {a b ua wa ub wb : ℝ}
    (P : TransverseGraphCuts lo a b ua wa ub wb)
    {X : Set ℝ} (hX : IsOpen X) (hlo : ContDiffOn ℝ ∞ lo X) :
    ContMDiffOn (𝓡 2) (𝓡 2) ∞ (obliqueSurfaceCoordinates F P hX hlo)
      (obliqueSurfaceCoordinates F P hX hlo).source := by
  let H := (collarParameterEquiv.toHomeomorph.toOpenPartialHomeomorph.trans
    (P.coordinates hX hlo)).trans collarParameterEquiv.symm.toHomeomorph.toOpenPartialHomeomorph
  have hH : ContDiffOn ℝ ∞ H H.source := collarParameterEquiv.symm.contDiff.comp_contDiffOn
    ((P.smooth_coordinates hX hlo).comp collarParameterEquiv.contDiff.contDiffOn
      (fun _ hz => hz.1.2))
  exact hF.comp (hH.contMDiffOn.mono (fun _ hz => hz.1)) (fun _ hz => hz.2)

omit [T2Space M] [IsManifold (𝓡 2) ∞ M] in
theorem smooth_obliqueSurfaceCoordinates_symm
    (F : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) M)
    (hFinv : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F.symm F.target)
    {lo : ℝ → ℝ} {a b ua wa ub wb : ℝ}
    (P : TransverseGraphCuts lo a b ua wa ub wb)
    {X : Set ℝ} (hX : IsOpen X) (hlo : ContDiffOn ℝ ∞ lo X) :
    ContMDiffOn (𝓡 2) (𝓡 2) ∞ (obliqueSurfaceCoordinates F P hX hlo).symm
      (obliqueSurfaceCoordinates F P hX hlo).target := by
  let H := (collarParameterEquiv.toHomeomorph.toOpenPartialHomeomorph.trans
    (P.coordinates hX hlo)).trans collarParameterEquiv.symm.toHomeomorph.toOpenPartialHomeomorph
  have hH : ContDiffOn ℝ ∞ H.symm H.target := collarParameterEquiv.symm.contDiff.comp_contDiffOn
    ((P.smooth_coordinates_symm hX hlo).comp collarParameterEquiv.contDiff.contDiffOn
      (fun _ hz => hz.2.1))
  exact hH.contMDiffOn.comp (hFinv.mono (fun _ hz => hz.1)) (fun _ hz => hz.2)



structure ObliqueBandFaces
    (F : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) M)
    (lo : ℝ → ℝ) (a b ua wa ub wb ra rb : ℝ) where
  left_length_pos : 0 < ra
  right_length_pos : 0 < rb
  domain : Set ℝ
  open_domain : IsOpen domain
  smooth_lower : ContDiffOn ℝ ∞ lo domain
  interval_subset : Icc a b ⊆ domain
  cuts : TransverseGraphCuts lo a b ua wa ub wb
  interface : ObliquePolygonalBoundary cuts domain ra rb
  pair : ∀ i : Fin interface.count,
    SmoothGraphBandPair (obliqueSurfaceCoordinates F cuts open_domain smooth_lower)
      (fun _ => 0) (interface.pieceCoordinates open_domain smooth_lower i).upperGraph
      (interface.strictMono_parameterCut open_domain smooth_lower (Fin.castSucc_lt_succ (i := i)))



noncomputable def obliqueBandFacesOfInterface
    (F : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) M)
    (hF : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F F.source)
    (hFinv : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F.symm F.target)
    {lo : ℝ → ℝ} {X : Set ℝ} (hX : IsOpen X) (hlo : ContDiffOn ℝ ∞ lo X)
    {a b ua wa ub wb ra rb : ℝ} (hI : Icc a b ⊆ X)
    (P : TransverseGraphCuts lo a b ua wa ub wb) (hra : 0 < ra) (hrb : 0 < rb)
    (B : ObliquePolygonalBoundary P X ra rb)
    (htube : ∀ x ∈ X, ∀ z : ℝ, 0 ≤ z → z < P.radius →
      collarParameterEquiv.symm (x, lo x + z) ∈ F.source)
    (p : M) (hchart : F.target ⊆ (chartAt (EuclideanSpace ℝ (Fin 2)) p).source) :
    ObliqueBandFaces F lo a b ua wa ub wb ra rb := by
  classical
  let C := obliqueSurfaceCoordinates F P hX hlo
  have hpairs (i : Fin B.count) :
      Nonempty (SmoothGraphBandPair C (fun _ => 0)
        (B.pieceCoordinates hX hlo i).upperGraph
        (B.strictMono_parameterCut hX hlo (Fin.castSucc_lt_succ (i := i)))) := by
    let G := B.pieceCoordinates hX hlo i
    apply exists_smoothGraphBandPair C
      (smooth_obliqueSurfaceCoordinates F hF P hX hlo)
      (smooth_obliqueSurfaceCoordinates_symm F hFinv P hX hlo)
      G.parameter.open_target contDiffOn_const (G.smooth_upperGraph hlo)
      (B.strictMono_parameterCut hX hlo Fin.castSucc_lt_succ)
      (fun t ht => G.parameter_mem_target ht) (fun t ht => (G.upperGraph_bounds ht).1)
      ?_ p (fun z hz => hchart hz.1)
    intro z hz
    have hG := G.band_subset_coordinates_source hX hlo hz
    refine ⟨⟨⟨mem_univ _, hG⟩, mem_univ _⟩, ?_⟩
    change collarParameterEquiv.symm (P.coordinates hX hlo (collarParameterEquiv z)) ∈ F.source
    rw [P.coordinates_apply hX hlo]
    rw [TransverseGraphCuts.coordinates, obliqueStripCoordinates_source] at hG
    exact htube _ hG.2 _ hz.2.1 (hz.2.2.trans_lt (G.upperGraph_bounds hz.1).2)
  exact {
    left_length_pos := hra
    right_length_pos := hrb
    domain := X
    open_domain := hX
    smooth_lower := hlo
    interval_subset := hI
    cuts := P
    interface := B
    pair := fun i => Classical.choice (hpairs i) }

omit [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M] in


theorem exists_graph_coordinate_source_tube
    (F : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) M)
    {lo : ℝ → ℝ} {X : Set ℝ} (hX : IsOpen X) (hlo : ContDiffOn ℝ ∞ lo X)
    {a b : ℝ} (hI : Icc a b ⊆ X)
    (harc : ∀ x ∈ Icc a b, collarParameterEquiv.symm (x, lo x) ∈ F.source) :
    ∃ U : Set ℝ, IsOpen U ∧ U ⊆ X ∧ Icc a b ⊆ U ∧
      ∃ δ > 0, ∀ x ∈ U, ∀ z : ℝ, |z| < δ →
        collarParameterEquiv.symm (x, lo x + z) ∈ F.source := by
  let lift : ℝ × ℝ → EuclideanSpace ℝ (Fin 2) :=
    fun q => collarParameterEquiv.symm (q.1, lo q.1 + q.2)
  have hcont : ContinuousOn lift {q | q.1 ∈ X} :=
    collarParameterEquiv.symm.continuous.comp_continuousOn
      (continuousOn_fst.prodMk ((hlo.continuousOn.comp continuousOn_fst
        (fun _ hq => hq)).add continuousOn_snd))
  let W : Set (ℝ × ℝ) := {q | q.1 ∈ X} ∩ lift ⁻¹' F.source
  have hW : IsOpen W := hcont.isOpen_inter_preimage
    (hX.preimage continuous_fst) F.open_source
  have haxis : Icc a b ×ˢ {(0 : ℝ)} ⊆ W := by
    rintro ⟨x, z⟩ ⟨hx, hz⟩
    have hz0 : z = 0 := hz
    subst z
    exact ⟨hI hx, by simpa [lift] using harc x hx⟩
  obtain ⟨U, V, hU, hV, hIU, h0V, hUV⟩ :=
    generalized_tube_lemma isCompact_Icc isCompact_singleton hW haxis
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp
    (hV.mem_nhds (h0V (mem_singleton (0 : ℝ))))
  refine ⟨U ∩ X, hU.inter hX, inter_subset_right, fun x hx => ⟨hIU hx, hI hx⟩,
    δ, hδ, ?_⟩
  intro x hx z hz
  exact (hUV (a := (x, z)) ⟨hx.1, hball (by
    simpa only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] using hz)⟩).2



theorem exists_obliqueBandFaces
    (F : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) M)
    (hF : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F F.source)
    (hFinv : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F.symm F.target)
    {lo : ℝ → ℝ} {X : Set ℝ} (hX : IsOpen X) (hlo : ContDiffOn ℝ ∞ lo X)
    {a b ua wa ub wb : ℝ} (hab : a < b) (hI : Icc a b ⊆ X)
    (htransA : 0 < wa - deriv lo a * ua) (htransB : 0 < wb - deriv lo b * ub)
    (harc : ∀ x ∈ Icc a b, collarParameterEquiv.symm (x, lo x) ∈ F.source)
    (p : M) (hchart : F.target ⊆ (chartAt (EuclideanSpace ℝ (Fin 2)) p).source) :
    ∃ ε > 0, ∀ ra ∈ Ioo (0 : ℝ) ε, ∀ rb ∈ Ioo (0 : ℝ) ε,
      Nonempty (ObliqueBandFaces F lo a b ua wa ub wb ra rb) := by
  classical
  obtain ⟨U, hU, hUX, hIU, δ, hδ, hsource⟩ := exists_graph_coordinate_source_tube F hX hlo hI harc
  have hloU := hlo.mono hUX
  obtain ⟨P⟩ := exists_transverseGraphCuts hU hloU hU hloU hab
    (hIU (left_mem_Icc.mpr hab.le)) (hIU (right_mem_Icc.mpr hab.le)) htransA htransB
  let r := min P.radius (δ / 2)
  have hr : 0 < r := lt_min P.radius_pos (by positivity)
  have hrP : r ≤ P.radius := min_le_left _ _
  have hrδ : r < δ := (min_le_right _ _).trans_lt (by linarith)
  have hsub : Ioo (-r) r ⊆ Ioo (-P.radius) P.radius := by
    intro z hz
    exact ⟨by linarith [hz.1], hz.2.trans_le hrP⟩
  let Q : TransverseGraphCuts lo a b ua wa ub wb :=
    { left := P.left
      right := P.right
      radius := r
      radius_pos := hr
      height_subset := fun _ hz => P.height_subset (hsub hz)
      separated := fun z hz => P.separated z (hsub hz) }
  obtain ⟨ε, hε, hboundary⟩ := exists_obliquePolygonalBoundary Q hab hU hloU hIU
  refine ⟨ε, hε, fun ra hra rb hrb => ?_⟩
  obtain ⟨B⟩ := hboundary ra hra rb hrb
  refine ⟨obliqueBandFacesOfInterface F hF hFinv hU hloU hIU Q hra.1 hrb.1 B ?_ p hchart⟩
  intro x hx z hz hzQ
  apply hsource x hx z
  rw [abs_of_nonneg hz]
  exact hzQ.trans hrδ

namespace ObliqueBandFaces

variable {F : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) M}
  {lo : ℝ → ℝ} {a b ua wa ub wb ra rb : ℝ}
  (B : ObliqueBandFaces F lo a b ua wa ub wb ra rb)


noncomputable abbrev coordinates : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) M :=
  obliqueSurfaceCoordinates F B.cuts B.open_domain B.smooth_lower


noncomputable abbrev cut : Fin (B.interface.count + 1) → ℝ := B.interface.parameterCut


noncomputable abbrev upperGraph (i : Fin B.interface.count) : ℝ → ℝ :=
  (B.interface.pieceCoordinates B.open_domain B.smooth_lower i).upperGraph

omit [T2Space M] in
theorem cut_strictMono : StrictMono B.cut :=
  B.interface.strictMono_parameterCut B.open_domain B.smooth_lower

omit [T2Space M] in
@[simp] theorem cut_first : B.cut 0 = 0 := B.interface.parameterCut_first

omit [T2Space M] in
@[simp] theorem cut_last : B.cut (Fin.last B.interface.count) = 1 :=
  B.interface.parameterCut_last

omit [T2Space M] in
theorem upperGraph_endpoints (i : Fin B.interface.count) :
    B.upperGraph i (B.cut i.castSucc) = B.interface.height i.castSucc ∧
      B.upperGraph i (B.cut i.succ) = B.interface.height i.succ :=
  (B.interface.pieceCoordinates B.open_domain B.smooth_lower i).upperGraph_endpoints


noncomputable def face (i : Fin B.interface.count × Bool) : SmoothFace M := (B.pair i.1).face i.2


def band : Set (EuclideanSpace ℝ (Fin 2)) :=
  ⋃ i, coordinateGraphBand (fun _ => 0) (B.upperGraph i) (B.cut i.castSucc) (B.cut i.succ)


noncomputable def vertex (i : Fin (B.interface.count + 1) × Bool) : M :=
  B.coordinates (collarParameterEquiv.symm
    (B.cut i.1, if i.2 then B.interface.height i.1 else 0))

omit [T2Space M] in
theorem cover : (⋃ i, (B.face i).carrier) = B.coordinates '' B.band := by
  ext z
  constructor
  · rintro ⟨_, ⟨⟨i, side⟩, rfl⟩, hz⟩
    obtain ⟨w, hw, rfl⟩ := (B.pair i).carrier_subset side hz
    exact ⟨w, mem_iUnion.mpr ⟨i, hw⟩, rfl⟩
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨i, hi⟩ := mem_iUnion.mp hw
    have h := mem_image_of_mem B.coordinates hi
    rw [← (B.pair i).cover] at h
    rcases h with h | h
    · exact mem_iUnion.mpr ⟨(i, false), h⟩
    · exact mem_iUnion.mpr ⟨(i, true), h⟩

omit [T2Space M] in
theorem cut_interval_cover :
    (⋃ i : Fin B.interface.count, Icc (B.cut i.castSucc) (B.cut i.succ)) = Icc (0 : ℝ) 1 := by
  simpa only [B.cut_first, B.cut_last] using
    iUnion_Icc_consecutive B.interface.count_pos B.cut B.cut_strictMono.monotone

omit [T2Space M] in

theorem adjacent_edges {i j : Fin B.interface.count} (hij : (i : ℕ) + 1 = j) :
    (B.pair i).lower.boundary 0 = (B.pair j).upper.boundary 2 := by
  have he : i.succ = j.castSucc := Fin.ext hij
  apply (B.pair i).adjacent_edge_eq (B.pair j) (congrArg B.cut he)
  change B.upperGraph i (B.cut i.succ) = B.upperGraph j (B.cut j.castSucc)
  rw [(B.upperGraph_endpoints i).2, (B.upperGraph_endpoints j).1, he]

theorem adjacent_intersection {i j : Fin B.interface.count} (hij : (i : ℕ) + 1 = j) :
    (B.pair i).lower.carrier ∩ (B.pair j).upper.carrier =
      ((B.pair i).lower.boundary 0).map '' Icc (0 : ℝ) 1 := by
  have he : i.succ = j.castSucc := Fin.ext hij
  apply (B.pair i).adjacent_lower_upper_inter (B.pair j) (congrArg B.cut he)
  change B.upperGraph i (B.cut i.succ) = B.upperGraph j (B.cut j.castSucc)
  rw [(B.upperGraph_endpoints i).2, (B.upperGraph_endpoints j).1, he]

omit [T2Space M] in
theorem nonadjacent_disjoint {i j : Fin B.interface.count} (hij : (i : ℕ) + 1 < j)
    (s t : Bool) : Disjoint (B.face (i, s)).carrier (B.face (j, t)).carrier := by
  apply (B.pair i).disjoint_of_right_lt_left (B.pair j) ?_ s t
  exact B.cut_strictMono (show i.succ < j.castSucc from hij)

private theorem face_intersection_of_lt {i j : Fin B.interface.count} (hij : i < j) (s t : Bool) :
    (∃ k l : Fin 3, (B.face (i, s)).boundary k = (B.face (j, t)).boundary l ∧
      (B.face (i, s)).carrier ∩ (B.face (j, t)).carrier =
        ((B.face (i, s)).boundary k).map '' Icc (0 : ℝ) 1) ∨
    ∃ v : Fin (B.interface.count + 1) × Bool,
      (B.face (i, s)).carrier ∩ (B.face (j, t)).carrier ⊆ {B.vertex v} := by
  by_cases hnext : (i : ℕ) + 1 = j
  · have he : i.succ = j.castSucc := Fin.ext hnext
    have hx {z : M} (hz : z ∈ (B.face (i, s)).carrier ∩ (B.face (j, t)).carrier) :
        (collarParameterEquiv (B.coordinates.symm z)).1 = B.cut i.succ := by
      have hleft := (B.pair i).parameter_mem hz.1
      have hright := (B.pair j).parameter_mem hz.2
      exact le_antisymm hleft.1.2 (he ▸ hright.1.1)
    cases s <;> cases t
    · right
      refine ⟨(j.castSucc, false), ?_⟩
      intro z hz
      exact (B.pair j).lower_left_vertex hz.2 ((hx hz).trans (congrArg B.cut he))
    · exact Or.inl ⟨0, 2, B.adjacent_edges hnext, B.adjacent_intersection hnext⟩
    · right
      refine ⟨(i.succ, true), ?_⟩
      intro z hz
      have h := (B.pair i).upper_right_vertex hz.1 (hx hz)
      simpa [vertex, (B.upperGraph_endpoints i).2] using h
    · right
      refine ⟨(i.succ, true), ?_⟩
      intro z hz
      have h := (B.pair i).upper_right_vertex hz.1 (hx hz)
      simpa [vertex, (B.upperGraph_endpoints i).2] using h
  · right
    refine ⟨(0, false), ?_⟩
    have hsep : (i : ℕ) + 1 < j := by have hval : (i : ℕ) < j := hij; omega
    rw [disjoint_iff_inter_eq_empty.mp (B.nonadjacent_disjoint hsep s t)]
    exact empty_subset _


theorem face_intersection (i j : Fin B.interface.count × Bool) (hij : i ≠ j) :
    (∃ k l : Fin 3, (B.face i).boundary k = (B.face j).boundary l ∧
      (B.face i).carrier ∩ (B.face j).carrier =
        ((B.face i).boundary k).map '' Icc (0 : ℝ) 1) ∨
    ∃ v : Fin (B.interface.count + 1) × Bool, (B.face i).carrier ∩ (B.face j).carrier ⊆ {B.vertex v} := by
  rcases i with ⟨i, s⟩
  rcases j with ⟨j, t⟩
  by_cases heq : i = j
  · subst j
    cases s <;> cases t
    · exact False.elim (hij rfl)
    · exact Or.inl ⟨1, 1, (B.pair i).diagonal_eq, (B.pair i).diagonal_inter⟩
    · left
      refine ⟨1, 1, (B.pair i).diagonal_eq.symm, ?_⟩
      change (B.pair i).upper.carrier ∩ (B.pair i).lower.carrier = _
      rw [inter_comm, (B.pair i).diagonal_inter, (B.pair i).diagonal_eq]
      rfl
    · exact False.elim (hij rfl)
  · rcases lt_or_gt_of_ne heq with hlt | hgt
    · exact B.face_intersection_of_lt hlt s t
    · rcases B.face_intersection_of_lt hgt t s with ⟨k, l, hedge, hinter⟩ | ⟨v, hv⟩
      · left
        refine ⟨l, k, hedge.symm, ?_⟩
        rw [inter_comm, hinter, hedge]
      · right
        exact ⟨v, by rwa [inter_comm]⟩

private theorem image_interval_parameter {c d : ℝ} (hcd : c ≤ d) :
    (fun t : ℝ => c + t * (d - c)) '' Icc (0 : ℝ) 1 = Icc c d := by
  have he : (fun t : ℝ => c + t * (d - c)) = AffineMap.lineMap c d := by
    funext t
    simp only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, smul_eq_mul]
    ring
  rw [he, ← segment_eq_image_lineMap ℝ, segment_eq_Icc hcd]

omit [T2Space M] in
theorem coordinates_pair_apply (q : ℝ × ℝ) :
    B.coordinates (collarParameterEquiv.symm q) =
      F (collarParameterEquiv.symm (B.cuts.coordinates B.open_domain B.smooth_lower q)) := by
  rw [obliqueSurfaceCoordinates_apply, collarParameterEquiv.apply_symm_apply]

omit [T2Space M] in

theorem upper_edge_image (i : Fin B.interface.count) :
    ((B.pair i).upper.boundary 0).map '' Icc (0 : ℝ) 1 =
      (fun q : ℝ × ℝ => F (collarParameterEquiv.symm q)) ''
        segment ℝ
          (B.interface.cut i.castSucc,
            lo (B.interface.cut i.castSucc) + B.interface.height i.castSucc)
          (B.interface.cut i.succ,
            lo (B.interface.cut i.succ) + B.interface.height i.succ) := by
  let G := B.interface.pieceCoordinates B.open_domain B.smooth_lower i
  calc
    _ = (fun t => B.coordinates (collarParameterEquiv.symm (t, B.upperGraph i t))) ''
        Icc (B.cut i.castSucc) (B.cut i.succ) := by
      rw [← image_interval_parameter (B.cut_strictMono Fin.castSucc_lt_succ).le, image_image]
      congr 1
      funext t
      exact (B.pair i).upper_edge t
    _ = (fun q : ℝ × ℝ => F (collarParameterEquiv.symm q)) ''
        ((fun t => B.cuts.coordinates B.open_domain B.smooth_lower (t, G.upperGraph t)) ''
          Icc (B.cut i.castSucc) (B.cut i.succ)) := by
      rw [image_image]
      congr 1
    _ = _ := congrArg (fun S => (fun q : ℝ × ℝ => F (collarParameterEquiv.symm q)) '' S)
      (G.coordinates_image_upperGraph_eq_segment B.open_domain B.smooth_lower)

omit [T2Space M] in
theorem coordinates_bottom (t : ℝ) :
    B.coordinates (collarParameterEquiv.symm (t, 0)) =
      F (collarParameterEquiv.symm (a + t * (b - a), lo (a + t * (b - a)))) := by
  rw [B.coordinates_pair_apply, B.cuts.coordinates_apply,
    obliqueStripMap_bottom B.cuts.A_zero B.cuts.B_zero]

omit [T2Space M] in

theorem lower_edges_image :
    (⋃ i : Fin B.interface.count, ((B.pair i).lower.boundary 2).map '' Icc (0 : ℝ) 1) =
      (fun x => F (collarParameterEquiv.symm (x, lo x))) '' Icc a b := by
  have hcell (i : Fin B.interface.count) :
      ((B.pair i).lower.boundary 2).map '' Icc (0 : ℝ) 1 =
        (fun t => B.coordinates (collarParameterEquiv.symm (t, 0))) ''
          Icc (B.cut i.castSucc) (B.cut i.succ) := by
    rw [← image_interval_parameter (B.cut_strictMono Fin.castSucc_lt_succ).le, image_image]
    congr 1
    funext t
    exact (B.pair i).lower_edge t
  simp_rw [hcell]
  rw [← image_iUnion, B.cut_interval_cover]
  have hab : a ≤ b := by
    have hsep := B.cuts.separated 0 (show (0 : ℝ) ∈ Ioo (-B.cuts.radius) B.cuts.radius from
      ⟨by linarith [B.cuts.radius_pos], B.cuts.radius_pos⟩)
    simpa only [B.cuts.A_zero, B.cuts.B_zero] using hsep.le
  rw [← image_interval_parameter hab, image_image]
  congr 1
  funext t
  exact B.coordinates_bottom t

private theorem cut_height_image {f : ℝ → ℝ} {x u w r : ℝ}
    (C : TransverseCutCoordinates f x u w) (hr : 0 ≤ r) (hrsource : r ∈ C.parameter.source) :
    (fun z => (C.horizontal z, f (C.horizontal z) + z)) '' Icc (0 : ℝ) (C.parameter r) =
      segment ℝ (x, f x) (x + r * u, f x + r * w) := by
  have hI : Icc (0 : ℝ) r ⊆ C.parameter.source := by
    obtain ⟨l, hl, s, _, hs⟩ := C.source_interval
    rw [hs] at hrsource ⊢
    intro t ht
    exact ⟨hl.trans_le ht.1, ht.2.trans_lt hrsource.2⟩
  have himage : C.parameter '' Icc (0 : ℝ) r = Icc (0 : ℝ) (C.parameter r) := by
    simpa only [C.parameter_zero] using
      (C.parameter.continuousOn.mono hI).image_Icc_of_monotoneOn hr
        (C.strictMono.monotoneOn.mono hI)
  rw [← himage, image_image]
  calc
    _ = (fun t : ℝ => (x + t * u, f x + t * w)) '' Icc (0 : ℝ) r := by
      apply image_congr
      intro t ht
      rw [C.line_identity (C.parameter.map_source (hI ht)), C.parameter.left_inv (hI ht)]
    _ = (AffineMap.lineMap (x, f x) (x + u, f x + w)) '' segment ℝ (0 : ℝ) r := by
      rw [segment_eq_Icc hr]
      congr 1
      funext t
      ext <;> simp [AffineMap.lineMap_apply] <;> ring
    _ = _ := by
      rw [image_segment]
      congr 1
      · simp
      · ext <;> simp [AffineMap.lineMap_apply] <;> ring


def firstCell : Fin B.interface.count := ⟨0, B.interface.count_pos⟩


def lastCell : Fin B.interface.count := ⟨B.interface.count - 1, by
  have hn := B.interface.count_pos
  omega⟩

omit [T2Space M] in

theorem left_edge_image :
    ((B.pair B.firstCell).upper.boundary 2).map '' Icc (0 : ℝ) 1 =
      (fun q : ℝ × ℝ => F (collarParameterEquiv.symm q)) ''
        segment ℝ (a, lo a) (a + ra * ua, lo a + ra * wa) := by
  have hfirst : B.firstCell.castSucc = 0 := rfl
  have hheight : B.upperGraph B.firstCell (B.cut B.firstCell.castSucc) =
      B.cuts.left.parameter ra := by
    rw [(B.upperGraph_endpoints B.firstCell).1, hfirst, B.interface.height_first]
  have hη : 0 ≤ B.cuts.left.parameter ra := by
    rw [← B.interface.height_first]
    exact (B.interface.vertex_height_bounds 0).1.le
  calc
    _ = (fun z => B.coordinates (collarParameterEquiv.symm (0, z))) ''
        Icc (0 : ℝ) (B.cuts.left.parameter ra) := by
      rw [← image_interval_parameter hη, image_image]
      congr 1
      funext t
      rw [(B.pair B.firstCell).left_edge]
      change B.coordinates (collarParameterEquiv.symm
        (B.cut B.firstCell.castSucc, 0 + t * (B.upperGraph B.firstCell
          (B.cut B.firstCell.castSucc) - 0))) = _
      rw [hheight, hfirst, B.cut_first]
    _ = (fun q : ℝ × ℝ => F (collarParameterEquiv.symm q)) ''
        ((fun z => (B.cuts.left.horizontal z, lo (B.cuts.left.horizontal z) + z)) ''
          Icc (0 : ℝ) (B.cuts.left.parameter ra)) := by
      rw [image_image]
      congr 1
      funext z
      rw [B.coordinates_pair_apply, B.cuts.coordinates_apply, obliqueStripMap_left]
    _ = _ := congrArg (fun S => (fun q : ℝ × ℝ => F (collarParameterEquiv.symm q)) '' S)
      (cut_height_image B.cuts.left B.left_length_pos.le B.interface.left_parameter_mem)

omit [T2Space M] in

theorem right_edge_image :
    ((B.pair B.lastCell).lower.boundary 0).map '' Icc (0 : ℝ) 1 =
      (fun q : ℝ × ℝ => F (collarParameterEquiv.symm q)) ''
        segment ℝ (b, lo b) (b + rb * ub, lo b + rb * wb) := by
  have hlast : B.lastCell.succ = Fin.last B.interface.count := by
    apply Fin.ext
    dsimp [lastCell]
    have hn := B.interface.count_pos
    omega
  have hheight : B.upperGraph B.lastCell (B.cut B.lastCell.succ) =
      B.cuts.right.parameter rb := by
    rw [(B.upperGraph_endpoints B.lastCell).2, hlast, B.interface.height_last]
  have hη : 0 ≤ B.cuts.right.parameter rb := by
    rw [← B.interface.height_last]
    exact (B.interface.vertex_height_bounds (Fin.last B.interface.count)).1.le
  calc
    _ = (fun z => B.coordinates (collarParameterEquiv.symm (1, z))) ''
        Icc (0 : ℝ) (B.cuts.right.parameter rb) := by
      rw [← image_interval_parameter hη, image_image]
      congr 1
      funext t
      rw [(B.pair B.lastCell).right_edge]
      change B.coordinates (collarParameterEquiv.symm
        (B.cut B.lastCell.succ, 0 + t * (B.upperGraph B.lastCell
          (B.cut B.lastCell.succ) - 0))) = _
      rw [hheight, hlast, B.cut_last]
    _ = (fun q : ℝ × ℝ => F (collarParameterEquiv.symm q)) ''
        ((fun z => (B.cuts.right.horizontal z, lo (B.cuts.right.horizontal z) + z)) ''
          Icc (0 : ℝ) (B.cuts.right.parameter rb)) := by
      rw [image_image]
      congr 1
      funext z
      rw [B.coordinates_pair_apply, B.cuts.coordinates_apply, obliqueStripMap_right]
    _ = _ := congrArg (fun S => (fun q : ℝ × ℝ => F (collarParameterEquiv.symm q)) '' S)
      (cut_height_image B.cuts.right B.right_length_pos.le B.interface.right_parameter_mem)

end ObliqueBandFaces

end PoincareConjecture.Topology.Surface
