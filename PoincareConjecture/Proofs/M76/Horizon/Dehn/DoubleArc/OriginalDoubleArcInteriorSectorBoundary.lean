import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleArc.OriginalDoubleArcIncidentSectorGeometry
import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleArc.OriginalDoubleArcInteriorSectorExterior
import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleArc.OriginalInteriorVertexRegion
import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleArc.TwoEndedSectorBoundary

set_option autoImplicit false

open Set Geometry Geometry.SimplicialComplex

namespace PoincareConjecture.M76.Dehn

local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)

open Classical in
theorem exists_original_interior_sector_boundary_disk
    {E X ι κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {R C A : Set X}
    (hAC : A ⊆ interior C) (hAR : A ⊆ R) (hAF : (A ∩ frontier R).Finite)
    (S : Fin 2 → Set X) (K : SimplicialComplex ℝ E) [Fintype K.faces]
    (F : X → E) (hF : Continuous F) (H : C ≃ₜ K.space)
    (hH : ∀ x : C, (H x : E) = F x) (g : E → C)
    (hg : ∀ z : K.space, (g z : X) = (H.symm z : X))
    (hgPL : PolyhedralPLInCharts e (fun z => (g z : X)) K.space)
    (M : κ → SimplicialComplex ℝ E) [∀ i, Fintype (M i).faces]
    (hMK : ∀ i, M i ≤ K)
    (hfull : ∀ i t, t ∈ K.faces → (∀ v ∈ t, v ∈ (M i).vertices) → t ∈ (M i).faces)
    (reg fr arc : κ) (sheet : Fin 2 → κ)
    (hreg : ∀ z ∈ K.space, z ∈ (M reg).space ↔ (g z : X) ∈ R)
    (hfr : ∀ z ∈ K.space, z ∈ (M fr).space ↔ (g z : X) ∈ frontier R)
    (harc : ∀ z ∈ K.space, z ∈ (M arc).space ↔ (g z : X) ∈ A)
    (hsheet : ∀ i z, z ∈ K.space → (z ∈ (M (sheet i)).space ↔ (g z : X) ∈ S i))
    (B : (M arc).vertices → OpenPartialHomeomorph X V3)
    (hB : ∀ p : (M arc).vertices,
      MapsTo (fun z => (g z : X)) (K.closedStar p).space (B p).source ∧
      (K.closedStar p).AffineOnFaces (fun z => B p (g z)) ∧
      (∀ y ∈ (B p).source, y ∈ A ↔ y ∈ R ∧ B p y 0 = 0 ∧ B p y 1 = 0) ∧
      ∀ i y, y ∈ (B p).source → (y ∈ S i ↔ y ∈ R ∧ B p y i.castSucc = 0))
    (v : (M arc).vertices) (hvFr : (g v : X) ∉ frontier R)
    (hregion : (B v).source ⊆ interior R ∨
      (∀ y ∈ (B v).source, y ∈ R ↔ 0 ≤ B v y 2) ∧
      ∀ y ∈ (B v).source, y ∈ frontier R ↔ B v y 2 = 0)
    (s : Bool → Finset E) (hs : ∀ j, s j ∈ (M arc).faces)
    (hcard : ∀ j, (s j).card = 2) (hvs : ∀ j, (v : E) ∈ s j)
    (hdisj : Disjoint (K.barycentricDualBlock (s false)).space
      (K.barycentricDualBlock (s true)).space) (signs : Fin 2 → Bool) :
    let V := K.barycentricDualBlock {(v : E)}
    let D := (M reg).barycentricDualBlock {(v : E)}
    let cuts := {z | ∀ i : Fin 2,
      if signs i then 0 ≤ B v (g z) i.castSucc else B v (g z) i.castSucc ≤ 0}
    let faces := fun i : Fin 2 => {z | z ∈ D.space ∧ z ∈ (M (sheet i)).space ∧
      if signs i.rev then 0 ≤ B v (g z) i.rev.castSucc else B v (g z) i.rev.castSucc ≤ 0}
    let Q := fun j => (K.barycentricDualBlock (s j)).space ∩ cuts
    let prescribed := (faces 0 ∪ faces 1) ∪ (Q false ∪ Q true)
    let boundary := {z | z ∈ D.space ∧ z ∈ cuts ∧
      (z ∈ (V.link v).space ∨ z ∈ (M fr).space ∨ ∃ i, z ∈ (M (sheet i)).space)}
    ∃ rim, IsFinitePLBallPair P2 prescribed rim ∧ prescribed ⊆ boundary ∧
      (boundary \ prescribed).Nonempty ∧ IsFinitePLBallPair V3 (D.space ∩ cuts) boundary ∧
      IsFinitePLBallPair P2 (boundary \ (prescribed \ rim)) rim ∧
      faces 0 ∩ faces 1 = V.space ∩ (M arc).space ∧
      (∀ j i, Q j ∩ faces i = Q j ∩ (M (sheet i)).space) ∧ Disjoint (Q false) (Q true) := by
  classical
  dsimp only
  let V := K.barycentricDualBlock {(v : E)}
  let D := (M reg).barycentricDualBlock {(v : E)}
  let Lp := (V.link v).space
  let Z := V.space ∩ (M arc).space
  let bZ := {z | z ∈ Z ∧ (z ∈ Lp ∨ z ∈ (M fr).space)}
  let cuts := {z | ∀ i : Fin 2,
    if signs i then 0 ≤ B v (g z) i.castSucc else B v (g z) i.castSucc ≤ 0}
  let faces := fun i : Fin 2 => {z | z ∈ D.space ∧ z ∈ (M (sheet i)).space ∧
    if signs i.rev then 0 ≤ B v (g z) i.rev.castSucc else B v (g z) i.rev.castSucc ≤ 0}
  let outer := fun i => {z | z ∈ faces i ∧ (z ∈ Lp ∨ z ∈ (M fr).space)}
  let Q := fun j => (K.barycentricDualBlock (s j)).space ∩ cuts
  let U := fun j => (Q j ∩ (M (sheet 0)).space) ∪ (Q j ∩ (M (sheet 1)).space)
  let O := fun j => Q j ∩ ((K.barycentricDualBlock (s j)).link ((s j).centroid ℝ id)).space
  let prescribed := (faces 0 ∪ faces 1) ∪ (Q false ∪ Q true)
  let boundary := {z | z ∈ D.space ∧ z ∈ cuts ∧
    (z ∈ Lp ∨ z ∈ (M fr).space ∨ ∃ i, z ∈ (M (sheet i)).space)}
  obtain ⟨C0, L, theta, hC, hcv, hzero, hL, hrep, htheta, hthetaInv,
    hlink, hmarks, hZ, hfaces, hfeet⟩ := exists_original_signed_tube_faces
      hAC hAR S K H g hg hgPL M hMK reg fr arc sheet hreg hfr harc hsheet v (B v)
      (hB v).1 (hB v).2.1 (hB v).2.2.1 (hB v).2.2.2 hregion
  have hgeometry (j : Bool) := exists_original_incident_joint_sector_geometry
    hAC hAR hAF S K F hF H hH g hg hgPL M hMK hfull reg fr arc sheet
      hreg hfr harc hsheet B hB (s j) (hs j) (hcard j) v (hvs j) signs
  choose a b hab hQball hUball hQD hQlink using hgeometry
  obtain ⟨hD, hmiss, hinside⟩ := original_interior_vertex_region_eq hAC hAR K H g hg hgPL
    M hMK reg fr arc hreg hfr harc v (B v) (hB v).1 (hB v).2.1 hvFr
  have hvK : (v : E) ∈ K.vertices := hMK arc v.property
  have hVK : V.space ⊆ K.space :=
    (space_subset_of_le (K.barycentricDualBlock_le {(v : E)})).trans
      K.barycentricSubdivision_isSubdivision.space_eq.subset
  have hVB : MapsTo (fun z => (g z : X)) V.space (B v).source := by
    intro z hz
    obtain ⟨t, ht, hzt⟩ := mem_space_iff.mp hz
    obtain ⟨u, hu, htu⟩ := K.exists_original_star_face_of_vertex_dual_face hvK ht
    exact (hB v).1 ((K.closedStar v).convexHull_subset_space hu (htu hzt))
  have hcoord (z : E) (hz : z ∈ D.space) (i : Fin 2) :
      z ∈ (M (sheet i)).space ↔ B v (g z) i.castSucc = 0 := by
    rw [hsheet i z (hVK (hD.subset hz)), (hB v).2.2.2 i (g z) (hVB (hD.subset hz))]
    exact and_iff_right (interior_subset (hinside z (hD.subset hz)))
  have hZF (i : Fin 2) : Z ⊆ faces i :=
    fun z hz => (hfaces i (signs i.rev)).1.1 (Or.inl hz)
  have hOZ (i : Fin 2) : outer i ∩ Z = bZ := by
    ext z
    exact ⟨fun h => ⟨h.2, h.1.2⟩, fun h => ⟨⟨hZF i h.1, h.2⟩, h.1⟩⟩
  have hFF : faces 0 ∩ faces 1 = Z := by
    ext z
    constructor
    · rintro ⟨h₀, h₁⟩
      refine ⟨hD.subset h₀.1, (harc z (hVK (hD.subset h₀.1))).mpr ?_⟩
      exact ((hB v).2.2.1 (g z) (hVB (hD.subset h₀.1))).mpr
        ⟨interior_subset (hinside z (hD.subset h₀.1)),
          (hcoord z h₀.1 0).mp h₀.2.1, (hcoord z h₁.1 1).mp h₁.2.1⟩
    · exact fun hz => ⟨hZF 0 hz, hZF 1 hz⟩
  have hsheetDisk : IsFinitePLBallPair P2 (faces 0 ∪ faces 1) (outer 0 ∪ outer 1) := by
    apply IsFinitePLBallPair.union_of_interval_attachment (d := Z) (q := bZ)
    · simpa [faces, outer, Z, V, D, Lp, Fin.rev, Fin.last, union_comm] using (hfaces 0 (signs 1)).1
    · simpa [faces, outer, Z, V, D, Lp, Fin.rev, Fin.last, union_comm] using (hfaces 1 (signs 0)).1
    · exact (hfaces 0 (signs 1)).2
    · exact (hfaces 1 (signs 0)).2
    · exact hZ
    · exact hOZ 0
    · exact hOZ 1
    · exact hFF
  have hcontact (j : Bool) (i : Fin 2) : Q j ∩ faces i = Q j ∩ (M (sheet i)).space := by
    ext z
    exact ⟨fun hz => ⟨hz.1, hz.2.2.1⟩,
      fun hz => ⟨hz.1, hQD j hz.1, hz.2, hz.1.2 i.rev⟩⟩
  have hmeet (j : Bool) : (faces 0 ∪ faces 1) ∩ Q j = U j := by
    rw [inter_comm, inter_union_distrib_left, hcontact j 0, hcontact j 1]
  have hUrim (j : Bool) : U j ⊆ outer 0 ∪ outer 1 := by
    rintro z (hz | hz)
    · exact Or.inl ⟨((hcontact j 0).superset hz).2, Or.inl (hQlink j hz.1)⟩
    · exact Or.inr ⟨((hcontact j 1).superset hz).2, Or.inl (hQlink j hz.1)⟩
  have hQdisj : Disjoint (Q false) (Q true) :=
    hdisj.mono inter_subset_left inter_subset_left
  have hjoined := isFinitePLBallPair_two_ended_sector_boundary Q O U a b hsheetDisk
    hQball hUball hab hUrim hmeet hQdisj
  obtain ⟨rim, hdisk⟩ : ∃ rim, IsFinitePLBallPair P2 prescribed rim :=
    ⟨_, by simpa only [prescribed, union_assoc] using hjoined⟩
  have hfaceCut (i : Fin 2) {z : E} (hz : z ∈ faces i) : z ∈ cuts := by
    intro j
    have hzero := (hcoord z hz.1 i).mp hz.2.1
    fin_cases i <;> fin_cases j
    · change if signs 0 then 0 ≤ B v (g z) 0 else B v (g z) 0 ≤ 0
      change B v (g z) 0 = 0 at hzero
      rw [hzero]
      cases signs 0 <;> exact le_rfl
    · exact hz.2.2
    · exact hz.2.2
    · change if signs 1 then 0 ≤ B v (g z) 1 else B v (g z) 1 ≤ 0
      change B v (g z) 1 = 0 at hzero
      rw [hzero]
      cases signs 1 <;> exact le_rfl
  have hsub : prescribed ⊆ boundary := by
    rintro z ((hz | hz) | hz | hz)
    · exact ⟨hz.1, hfaceCut 0 hz, Or.inr (Or.inr ⟨0, hz.2.1⟩)⟩
    · exact ⟨hz.1, hfaceCut 1 hz, Or.inr (Or.inr ⟨1, hz.2.1⟩)⟩
    · exact ⟨hQD false hz, hz.2, Or.inl (hQlink false hz)⟩
    · exact ⟨hQD true hz, hz.2, Or.inl (hQlink true hz)⟩
  have hvstar : (v : E) ∈ (K.closedStar v).space := by
    apply (K.closedStar v).vertices_subset_space
    change {(v : E)} ∈ K.faces ∧ insert (v : E) {(v : E)} ∈ K.faces
    simpa only [Finset.insert_eq_of_mem (Finset.mem_singleton_self (v : E)), and_self]
      using (show {(v : E)} ∈ K.faces from hvK)
  have hvA : (g v : X) ∈ A := (harc v (K.vertices_subset_space hvK)).mp
    ((M arc).vertices_subset_space v.property)
  have hvzero (i : Fin 2) : B v (g v) i.castSucc = 0 := by
    have hz := (((hB v).2.2.1 (g v) ((hB v).1 hvstar)).mp hvA).2
    fin_cases i
    · exact hz.1
    · exact hz.2
  have hmarks' (i : Fin 2) (z : V.space) :
      ((theta z : V3) i.castSucc = 0 ↔ B v (g z) i.castSucc = 0) ∧
      (0 ≤ (theta z : V3) i.castSucc ↔ 0 ≤ B v (g z) i.castSucc) := by
    simpa only [Pi.sub_apply, hvzero i, sub_zero] using hmarks i.castSucc z
  have hout : (boundary \ prescribed).Nonempty := by
    obtain ⟨z, hzD, hzlink, hzJ, hzfr, hzsheet, hzstrict⟩ :=
      exists_original_interior_sector_exterior_point hAC hAR hAF S K F hF H hH g hg hgPL
        M hMK hfull reg fr arc sheet hreg hfr harc hsheet B hB v hvFr s hs hcard hvs
        hdisj C0 theta hC hcv hzero hlink hmarks' signs
    have hweak (i : Fin 2) :
        if signs i then 0 ≤ B v (g z) i.castSucc else B v (g z) i.castSucc ≤ 0 := by
      have hi := hzstrict i
      cases hiSign : signs i <;> simp only [hiSign, Bool.false_eq_true, ↓reduceIte] at hi ⊢ <;>
        exact hi.le
    refine ⟨z, ⟨hzD, hweak, Or.inl hzlink⟩, ?_⟩
    rintro ((hz | hz) | hz | hz)
    · exact hzsheet 0 hz.2.1
    · exact hzsheet 1 hz.2.1
    · exact hzJ false hz.1
    · exact hzJ true hz.1
  have hball := isFinitePLBallPair_original_interior_sector hAC hAR S K H g hg hgPL M hMK
    reg fr arc sheet hreg hfr harc hsheet v (B v) (hB v).1 (hB v).2.1
    (hB v).2.2.1 (hB v).2.2.2 hvFr signs
  exact ⟨rim, hdisk, hsub, hout, hball,
    hball.boundary_disk_complement (by simp) hdisk hsub hout, hFF, hcontact, hQdisj⟩

end PoincareConjecture.M76.Dehn
