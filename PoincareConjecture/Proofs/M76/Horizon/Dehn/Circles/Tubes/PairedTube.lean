import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.Tubes.ModelDualContacts
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.Tubes.CyclicTubeMap
import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleArc.OriginalDoubleArcJointFamily
import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleArc.OriginalDoubleArcCanonicalBlockMaps
import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleCurve.Intervals.BranchInverses









set_option autoImplicit false
open Set Metric Geometry Geometry.SimplicialComplex Topology

namespace PoincareConjecture.M76.Dehn

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)

private theorem dualBlock_congr
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K L : SimplicialComplex ℝ E) [hK : Fintype K.faces] [hL : Fintype L.faces]
    (h : K = L) (s : Finset E) : K.barycentricDualBlock s = L.barycentricDualBlock s := by
  subst L
  have hi : hK = hL := Subsingleton.elim _ _
  cases hi
  rfl



theorem exists_translated_unit_diamond_block
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {B : Set E} (map : ↥(signedTubeDiamond ×ˢ Icc (0 : ℝ) 1) ≃ₜ B)
    (hmap : map.IsFinitePL) (a : ℝ) :
    ∃ shifted : ↥(signedTubeDiamond ×ˢ Icc a (a + 1)) ≃ₜ B,
      shifted.IsFinitePL ∧ ∀ x,
        (shifted x : E) = map ⟨((x : P2 × ℝ).1, (x : P2 × ℝ).2 - a),
          x.property.1, by constructor <;> linarith [x.property.2.1, x.property.2.2]⟩ := by
  let shift : (P2 × ℝ) →ᴬ[ℝ] (P2 × ℝ) :=
    (ContinuousLinearMap.fst ℝ P2 ℝ).toContinuousAffineMap.prod
      ((ContinuousLinearMap.snd ℝ P2 ℝ).toContinuousAffineMap +
        ContinuousAffineMap.const ℝ (P2 × ℝ) a)
  have hval (x : P2 × ℝ) : shift x = (x.1, x.2 + a) := rfl
  have hinj : Function.Injective shift := by
    intro x y h
    have h0 := congrArg Prod.fst h
    have h1 := congrArg Prod.snd h
    exact Prod.ext h0 (add_right_cancel h1)
  have himage : shift '' (signedTubeDiamond ×ˢ Icc (0 : ℝ) 1) =
      signedTubeDiamond ×ˢ Icc a (a + 1) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨hy.1, by change a ≤ y.2 + a; linarith [hy.2.1],
        by change y.2 + a ≤ a + 1; linarith [hy.2.2]⟩
    · intro hx
      refine ⟨(x.1, x.2 - a), ⟨hx.1, ?_, ?_⟩, ?_⟩
      · linarith [hx.2.1]
      · linarith [hx.2.2]
      · simp [hval]
  have hmap' := hmap
  obtain ⟨_, ⟨K, hK, hKs, _⟩, _⟩ := hmap'
  have hshift : FinitePiecewiseAffineOn shift (signedTubeDiamond ×ˢ Icc (0 : ℝ) 1) :=
    ⟨K, hK, hKs, K.affineOnFaces_affine shift⟩
  have he := hshift.exists_homeomorph_image hinj.injOn
  rw [himage] at he
  obtain ⟨e, he, heval⟩ := he
  refine ⟨e.symm.trans map, he.symm.trans hmap, ?_⟩
  intro x
  apply congrArg (fun z ↦ (map z : E))
  apply Subtype.ext
  have hv := heval (e.symm x)
  rw [e.apply_symm_apply] at hv
  have hv0 := congrArg Prod.fst hv
  have hv1 := congrArg Prod.snd hv
  exact Prod.ext hv0.symm (by change (e.symm x : P2 × ℝ).2 = x.val.2 - a; change x.val.2 = (e.symm x : P2 × ℝ).2 + a at hv1; linarith)

variable {X ι : Type*} [TopologicalSpace X]
  {e : ι → OpenPartialHomeomorph X V3} {f : V2 → X} {R : Set X}
  {old : OrdinaryDoubleCurveModel e f R} {i : old.Index}



theorem OrdinaryIntervalMarkedModel.region_eq_complex_of_core_interior
    (D : OrdinaryIntervalMarkedModel old i) (hcore : D.core ⊆ interior R) :
    D.marks (.inl false) = D.complex := by
  classical
  apply le_antisymm (D.marks_full (.inl false)).1
  intro s hs
  apply (D.marks_full (.inl false)).2.2 s hs
  intro v hv
  have hvK : v ∈ D.complex.vertices :=
    D.complex.down_closed hs (by simpa using hv) (Finset.singleton_nonempty _)
  have hvR : v ∈ (D.marks (.inl false)).space :=
    (D.mem_mark_image D.region_image v (D.complex.vertices_subset_space hvK)).mpr
      (interior_subset (hcore (D.inverse v).property))
  obtain ⟨t, ht, hvt⟩ := mem_space_iff.mp hvR
  have hvt' : v ∈ t := (D.complex.vertex_mem_convexHull_iff hvK
    ((D.marks_full (.inl false)).1 ht)).mp hvt
  exact (D.marks (.inl false)).down_closed ht
    (by simpa using hvt') (Finset.singleton_nonempty _)



theorem OrdinaryIntervalMarkedModel.exists_circle_joint_family
    (D : OrdinaryIntervalMarkedModel old i) (hcore : D.core ⊆ interior R) :
    letI : Fintype D.complex.faces := D.complex_finite.fintype
    let Edge := {s : Finset (D.sample → ℝ × V3) //
      s ∈ (D.marks (.inr 2)).faces ∧ s.card = 2}
    ∃ (B : (D.marks (.inr 2)).vertices → OpenPartialHomeomorph X V3)
      (G : ∀ s : Edge, signedTubeDiamond ≃ₜ (D.complex.barycentricDualBlock s).space)
      (eta : ∀ (s : Edge) (v : (D.marks (.inr 2)).vertices),
        (v : D.sample → ℝ × V3) ∈ (s : Finset (D.sample → ℝ × V3)) → Fin 2 → Bool),
      (∀ p : (D.marks (.inr 2)).vertices,
        MapsTo (fun z ↦ (D.inverse z : X)) (D.complex.closedStar p).space (B p).source ∧
        (D.complex.closedStar p).AffineOnFaces (fun z ↦ B p (D.inverse z)) ∧
        (∀ y ∈ (B p).source, y ∈ f '' old.pieces i ↔
          y ∈ R ∧ B p y 0 = 0 ∧ B p y 1 = 0) ∧
        ∀ j : Fin 2, ∀ y ∈ (B p).source,
          y ∈ f '' (D.source j.castSucc).space ↔ y ∈ R ∧ B p y j.castSucc = 0) ∧
      (∀ p, (B p).source ⊆ interior R ∨
        (∀ y ∈ (B p).source, y ∈ R ↔ 0 ≤ B p y 2) ∧
        ∀ y ∈ (B p).source, y ∈ frontier R ↔ B p y 2 = 0) ∧
      (∀ s, (G s).IsFinitePL) ∧
      (∀ s, (G s ⟨(0, 0), signedTubeRadius_subset_diamond 0 false
        (left_mem_segment ℝ _ _)⟩ : D.sample → ℝ × V3) =
          (s : Finset (D.sample → ℝ × V3)).centroid ℝ id) ∧
      ∀ (s : Edge) (v : (D.marks (.inr 2)).vertices) (hv : (v : D.sample → ℝ × V3) ∈
        (s : Finset (D.sample → ℝ × V3))) eps delta (x : signedTubeDiamond),
        (x : P2) ∈ signedTubeQuarter eps delta ↔
          (G s x : D.sample → ℝ × V3) ∈ signedCoordinateSector
            (D.complex.barycentricDualBlock s).space
            (fun j z ↦ B v (D.inverse z) j.castSucc) (eta s v hv) eps delta := by
  classical
  let _ : Fintype D.complex.faces := D.complex_finite.fintype
  let _ (j) : Fintype (D.marks j).faces := (D.marks_full j).2.1.fintype
  have hAR : f '' old.pieces i ⊆ R :=
    fun y hy ↦ interior_subset (hcore (interior_subset (D.core_neighborhood hy)))
  have hAF : ((f '' old.pieces i) ∩ frontier R).Finite := by
    have hzero : (f '' old.pieces i) ∩ frontier R = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro y hy
      exact (disjoint_interior_frontier.notMem_of_mem_left
        (hcore (interior_subset (D.core_neighborhood hy.1)))) hy.2
    rw [hzero]
    exact finite_empty
  have harc (z : D.sample → ℝ × V3) (hz : z ∈ D.complex.space) :
      z ∈ (D.marks (.inr 2)).space ↔ (D.inverse z : X) ∈ f '' old.pieces i := by
    simpa only [D.selected_source] using D.mem_mark_image (D.marks_image 2) z hz
  choose point hmap hface using fun p : (D.marks (.inr 2)).vertices ↦
    D.selected_stars p p.property
  let B (p : (D.marks (.inr 2)).vertices) := D.charts (point p)
  have hB (p : (D.marks (.inr 2)).vertices) :
      MapsTo (fun z ↦ (D.inverse z : X)) (D.complex.closedStar p).space (B p).source ∧
      (D.complex.closedStar p).AffineOnFaces (fun z ↦ B p (D.inverse z)) ∧
      (∀ y ∈ (B p).source, y ∈ f '' old.pieces i ↔
        y ∈ R ∧ B p y 0 = 0 ∧ B p y 1 = 0) ∧
      ∀ j : Fin 2, ∀ y ∈ (B p).source,
        y ∈ f '' (D.source j.castSucc).space ↔ y ∈ R ∧ B p y j.castSucc = 0 := by
    refine ⟨hmap p, hface p, D.chart_axis (point p), ?_⟩
    intro j y hy
    fin_cases j
    · exact (D.chart_left (point p) y hy).trans and_comm
    · exact (D.chart_right (point p) y hy).trans and_comm
  obtain ⟨G, eta, hG, hcenter, heta⟩ := exists_original_signed_tube_joint_family
    D.core_neighborhood hAR hAF (fun j : Fin 2 ↦ f '' (D.source j.castSucc).space)
    D.complex D.graph D.graph_continuous D.homeomorph D.homeomorph_value
    D.inverse D.inverse_value D.inverse_PL D.marks
    (fun j ↦ (D.marks_full j).1) (fun j ↦ (D.marks_full j).2.2)
    (.inl false) (.inl true) (.inr 2) (fun j : Fin 2 ↦ .inr j.castSucc)
    (D.mem_mark_image D.region_image) (D.mem_mark_image D.frontier_image) harc
    (fun j ↦ D.mem_mark_image (D.marks_image j.castSucc)) B (by
      convert hB using 1
      have hdec : (fun a b : D.sample → ℝ × V3 ↦ Fintype.decidablePiFintype a b) =
          Classical.decEq _ := Subsingleton.elim _ _
      rw [hdec])
  exact ⟨B, G, eta, hB, fun p ↦ D.chart_region (point p), hG, hcenter, heta⟩


structure PairedCircleBlockData (D : OrdinaryIntervalMarkedModel old i)
    [Fintype D.complex.faces] {n : ℕ} (p : Fin (n + 3) → D.sample → ℝ × V3) where
  joint : ∀ j, signedTubeDiamond ≃ₜ
    (D.complex.barycentricDualBlock {p j, p (finRotate (n + 3) j)}).space
  jointPL : ∀ j, (joint j).IsFinitePL
  left : Fin (n + 3) → Fin 2 → Bool
  right : Fin (n + 3) → Fin 2 → Bool
  map : ∀ j, ↥(signedTubeDiamond ×ˢ Icc (0 : ℝ) 1) ≃ₜ
    (D.complex.barycentricDualBlock {p j}).space
  mapPL : ∀ j, (map j).IsFinitePL
  lower : ∀ j (x : signedTubeDiamond),
    (map j ⟨(x, 0), x.property, le_rfl, zero_le_one⟩ : D.sample → ℝ × V3) =
      joint ((finRotate (n + 3)).symm j) (signedTubeDiamondReflection (left j) x)
  upper : ∀ j (x : signedTubeDiamond),
    (map j ⟨(x, 1), x.property, zero_le_one, le_rfl⟩ : D.sample → ℝ × V3) =
      joint j (signedTubeDiamondReflection (right j) x)
  sheets : ∀ j k (x : ↥(signedTubeDiamond ×ˢ Icc (0 : ℝ) 1)),
    (x : P2 × ℝ).1 ∈ signedTubeSheet k ↔
      (map j x : D.sample → ℝ × V3) ∈ (D.marks (.inr k.castSucc)).space
  axis : ∀ j (x : ↥(signedTubeDiamond ×ˢ Icc (0 : ℝ) 1)),
    (x : P2 × ℝ).1 = (0, 0) ↔
      (map j x : D.sample → ℝ × V3) ∈ (D.marks (.inr 2)).space



theorem OrdinaryIntervalMarkedModel.exists_circle_block_data
    (D : OrdinaryIntervalMarkedModel old i) (hcore : D.core ⊆ interior R)
    {m : ℕ} (P : Polygon V2 (m + 3)) (hP : P.HasSimplicialEdges)
    (hPi : Function.Injective P) (hPs : P.boundary ℝ = old.pieces i) :
    letI : Fintype D.complex.faces := D.complex_finite.fintype
    ∃ (n : ℕ) (p : Fin (n + 3) → D.sample → ℝ × V3),
      Function.Injective p ∧ range p = (D.marks (.inr 2)).vertices ∧
      (∀ s : Finset (D.sample → ℝ × V3), s ∈ (D.marks (.inr 2)).faces ↔
        s.Nonempty ∧ ∃ j : Fin (n + 3), s ⊆ {p j, p (finRotate (n + 3) j)}) ∧
      Nonempty (PairedCircleBlockData D p) := by
  classical
  let _ : Fintype D.complex.faces := D.complex_finite.fintype
  let _ (j) : Fintype (D.marks j).faces := (D.marks_full j).2.1.fintype
  obtain ⟨n, p, hpi, _, hpv, _, hpf, _⟩ := D.exists_exact_model_circle_order P hP hPi hPs
  obtain ⟨B, G, eta, hB, hregion, hG, hcenter, hquarter⟩ := D.exists_circle_joint_family hcore
  have hreg := D.region_eq_complex_of_core_interior hcore
  have hnext (j : Fin (n + 3)) : j ≠ finRotate (n + 3) j := by
    intro h
    have h' : (1 : Fin (n + 3)) = 0 := add_left_cancel
      (show j + 1 = j + 0 by simpa only [finRotate_apply, add_zero] using h.symm)
    have := congrArg Fin.val h'
    norm_num at this
  let vertex (j : Fin (n + 3)) : (D.marks (.inr 2)).vertices :=
    ⟨p j, hpv ▸ mem_range_self j⟩
  let Edge := {s : Finset (D.sample → ℝ × V3) //
    s ∈ (D.marks (.inr 2)).faces ∧ s.card = 2}
  let edge (j : Fin (n + 3)) : Edge :=
    ⟨{p j, p (finRotate (n + 3) j)},
      (hpf _).mpr ⟨Finset.insert_nonempty _ _, j, subset_rfl⟩,
      Finset.card_pair (hpi.ne (hnext j))⟩
  have hAR : f '' old.pieces i ⊆ R :=
    fun y hy ↦ interior_subset (hcore (interior_subset (D.core_neighborhood hy)))
  have hAF : ((f '' old.pieces i) ∩ frontier R).Finite := by
    apply (finite_empty : (∅ : Set X).Finite).subset
    rintro y ⟨hy, hyf⟩
    exact False.elim ((disjoint_interior_frontier.notMem_of_mem_left
      (hcore (interior_subset (D.core_neighborhood hy)))) hyf)
  have harc (z : D.sample → ℝ × V3) (hz : z ∈ D.complex.space) :
      z ∈ (D.marks (.inr 2)).space ↔ (D.inverse z : X) ∈ f '' old.pieces i := by
    simpa only [D.selected_source] using D.mem_mark_image (D.marks_image 2) z hz
  have hjointDisj := (D.complex.full_cyclic_dual_contacts (D.marks (.inr 2))
    (D.marks_full (.inr 2)).1 (D.marks_full (.inr 2)).2.2 p hpi hpv hpf).2.2.2.1
  let incident (j : Fin (n + 3)) (side : Bool) :=
    if side then j else (finRotate (n + 3)).symm j
  have hincident (j : Fin (n + 3)) (side : Bool) :
      (vertex j : D.sample → ℝ × V3) ∈ (edge (incident j side) : Finset _) := by
    cases side <;> simp [vertex, edge, incident]
  let sign (j : Fin (n + 3)) (side : Bool) :=
    eta (edge (incident j side)) (vertex j) (hincident j side)
  have hblock (j : Fin (n + 3)) :
      ∃ map : ↥(signedTubeDiamond ×ˢ Icc (0 : ℝ) 1) ≃ₜ
        (D.complex.barycentricDualBlock {p j}).space,
        map.IsFinitePL ∧
        (∀ side (x : signedTubeDiamond),
          (map ⟨(x, if side then 1 else 0), x.property, by cases side <;> norm_num⟩ :
            D.sample → ℝ × V3) = G (edge (incident j side))
              (signedTubeDiamondReflection (sign j side) x)) ∧
        (∀ k (x : ↥(signedTubeDiamond ×ˢ Icc (0 : ℝ) 1)),
          (x : P2 × ℝ).1 ∈ signedTubeSheet k ↔
            (map x : D.sample → ℝ × V3) ∈ (D.marks (.inr k.castSucc)).space) ∧
        ∀ x : ↥(signedTubeDiamond ×ˢ Icc (0 : ℝ) 1),
          (x : P2 × ℝ).1 = (0, 0) ↔
            (map x : D.sample → ℝ × V3) ∈ (D.marks (.inr 2)).space := by
    have hne : (finRotate (n + 3)).symm j ≠ j := by
      intro h
      exact hnext j (by simpa only [Equiv.apply_symm_apply] using congrArg (finRotate (n + 3)) h)
    have hdisj := hjointDisj ((finRotate (n + 3)).symm j) j hne
    have hdisj' : Disjoint
        (D.complex.barycentricDualBlock (edge (incident j false))).space
        (D.complex.barycentricDualBlock (edge (incident j true))).space := by
      simpa only [edge, incident, Bool.false_eq_true, ↓reduceIte] using hdisj
    have hvfr : (D.inverse (vertex j) : X) ∉ frontier R :=
      disjoint_interior_frontier.notMem_of_mem_left (hcore (D.inverse (vertex j)).property)
    let s : Bool → Finset (D.sample → ℝ × V3) := fun side ↦ edge (incident j side)
    let Gj : ∀ side : Bool, signedTubeDiamond ≃ₜ
        (D.complex.barycentricDualBlock (s side)).space :=
      fun side ↦ G (edge (incident j side))
    obtain ⟨b, map, hb, hb0, hb1, hm, hend, haxis, hquarter', haxis', hsheet⟩ :=
      exists_original_local_interior_block_map D.core_neighborhood hAR hAF
        (fun k : Fin 2 ↦ f '' (D.source k.castSucc).space)
        D.complex D.graph D.graph_continuous D.homeomorph D.homeomorph_value
        D.inverse D.inverse_value D.inverse_PL D.marks
        (fun k ↦ (D.marks_full k).1) (fun k ↦ (D.marks_full k).2.2)
        (.inl false) (.inl true) (.inr 2) (fun k : Fin 2 ↦ .inr k.castSucc)
        (D.mem_mark_image D.region_image) (D.mem_mark_image D.frontier_image) harc
        (fun k ↦ D.mem_mark_image (D.marks_image k.castSucc)) B (by
          convert hB using 1
          have hdec : (fun a b : D.sample → ℝ × V3 ↦ Fintype.decidablePiFintype a b) =
              Classical.decEq _ := Subsingleton.elim _ _
          rw [hdec])
        (vertex j) hvfr (hregion (vertex j))
        s
        (fun side ↦ (edge (incident j side)).property.1)
        (fun side ↦ (edge (incident j side)).property.2) (hincident j)
        (by exact hdisj') Gj
        (fun side ↦ hG (edge (incident j side))) (sign j)
        (fun side ↦ hquarter (edge (incident j side)) (vertex j) (hincident j side))
        (fun side ↦ hcenter (edge (incident j side)))
    have hcarrier := congrArg SimplicialComplex.space
      (dualBlock_congr _ _ hreg {(vertex j : D.sample → ℝ × V3)})
    let map' := (Homeomorph.setCongr rfl).trans (map.trans (Homeomorph.setCongr hcarrier))
    refine ⟨map', hm.setCongr rfl hcarrier, hend, hsheet, ?_⟩
    intro x
    exact (haxis' x).trans (and_iff_right (hcarrier ▸ (map x).property))
  choose map hmap hend hsheet haxis using hblock
  refine ⟨n, p, hpi, hpv, hpf, ⟨{
    joint := fun j ↦ G (edge j)
    jointPL := fun j ↦ hG (edge j)
    left := fun j ↦ sign j false
    right := fun j ↦ sign j true
    map := map
    mapPL := hmap
    lower := fun j x ↦ hend j false x
    upper := fun j x ↦ hend j true x
    sheets := hsheet
    axis := haxis }⟩⟩

end PoincareConjecture.M76.Dehn
