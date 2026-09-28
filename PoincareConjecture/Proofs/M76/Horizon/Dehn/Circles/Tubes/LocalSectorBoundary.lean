import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.Tubes.LocalVertexExterior
import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleArc.TwoEndedSectorBoundary

set_option autoImplicit false
open Set Metric Geometry Topology Geometry.SimplicialComplex

namespace PoincareConjecture.M76.Dehn

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)

open Classical in
set_option maxHeartbeats 800000 in

theorem ComponentBranchModel.exists_local_sector_boundary
    {X ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {f : V2 → X} {R : Set X}
    {old : OrdinaryDoubleCurveModel e f R} {i : old.Index}
    (D : ComponentBranchModel old i) [Fintype D.complex.faces]
    (hcore : D.core ⊆ interior R)
    (v : D.sample → ℝ × V3) (hv : v ∈ D.axis.vertices)
    {x y : V2} (C : RawCrossingChart e f R x y)
    (hC : MapsTo (fun z ↦ (D.inverse z : X)) (D.complex.closedStar v).space C.chart.source)
    (hface : (D.complex.closedStar v).AffineOnFaces (fun z ↦ C.chart (D.inverse z)))
    (haxis : ∀ z ∈ (D.complex.closedStar v).space,
      z ∈ D.axis.space ↔ (D.inverse z : X) ∈ R ∧
        C.chart (D.inverse z) 0 = 0 ∧ C.chart (D.inverse z) 1 = 0)
    (hsheet : ∀ j : Fin 2,
      ((D.complex.closedStar v).vertexSubcomplex
        {z | (D.inverse z : X) ∈ R ∧ C.chart (D.inverse z) j.castSucc = 0}).space =
      (D.complex.closedStar v).space ∩
        {z | (D.inverse z : X) ∈ R ∧ C.chart (D.inverse z) j.castSucc = 0})
    (s : Bool → Finset (D.sample → ℝ × V3)) (hs : ∀ j, s j ∈ D.axis.faces)
    (hcard : ∀ j, (s j).card = 2) (hvs : ∀ j, v ∈ s j)
    (hdisj : Disjoint (D.complex.barycentricDualBlock (s false)).space
      (D.complex.barycentricDualBlock (s true)).space) (signs : Fin 2 → Bool) :
    let V := D.complex.barycentricDualBlock {v}
    let cuts := {z | ∀ j : Fin 2, SignedJointCross.side (signs j) (C.chart (D.inverse z) j.castSucc)}
    let face := fun j : Fin 2 => {z | z ∈ V.space ∧ C.chart (D.inverse z) j.castSucc = 0 ∧
      SignedJointCross.side (signs j.rev) (C.chart (D.inverse z) j.rev.castSucc)}
    let Q := fun b => (D.complex.barycentricDualBlock (s b)).space ∩ cuts
    let prescribed := (face 0 ∪ face 1) ∪ (Q false ∪ Q true)
    let boundary := {z | z ∈ V.space ∧ z ∈ cuts ∧
      (z ∈ (V.link v).space ∨ ∃ j : Fin 2, C.chart (D.inverse z) j.castSucc = 0)}
    ∃ rim, IsFinitePLBallPair P2 prescribed rim ∧ prescribed ⊆ boundary ∧
      (boundary \ prescribed).Nonempty ∧ IsFinitePLBallPair V3 (V.space ∩ cuts) boundary ∧
      IsFinitePLBallPair P2 (boundary \ (prescribed \ rim)) rim ∧
      face 0 ∩ face 1 = V.space ∩ D.axis.space ∧
      (∀ b j, Q b ∩ face j = Q b ∩ {z | C.chart (D.inverse z) j.castSucc = 0}) ∧
      Disjoint (Q false) (Q true) := by
  classical
  let V := D.complex.barycentricDualBlock {v}
  let Z := V.space ∩ D.axis.space
  let bZ := Z ∩ (V.link v).space
  let cuts := {z | ∀ j : Fin 2, SignedJointCross.side (signs j) (C.chart (D.inverse z) j.castSucc)}
  let face := fun j : Fin 2 => {z | z ∈ V.space ∧ C.chart (D.inverse z) j.castSucc = 0 ∧
    SignedJointCross.side (signs j.rev) (C.chart (D.inverse z) j.rev.castSucc)}
  let outer := fun j => face j ∩ (V.link v).space
  let Q := fun b => (D.complex.barycentricDualBlock (s b)).space ∩ cuts
  let U := fun b => (Q b ∩ {z | C.chart (D.inverse z) 0 = 0}) ∪
    (Q b ∩ {z | C.chart (D.inverse z) 1 = 0})
  let O := fun b => Q b ∩
    ((D.complex.barycentricDualBlock (s b)).link ((s b).centroid ℝ id)).space
  let prescribed := (face 0 ∪ face 1) ∪ (Q false ∪ Q true)
  let boundary := {z | z ∈ V.space ∧ z ∈ cuts ∧
    (z ∈ (V.link v).space ∨ ∃ j : Fin 2, C.chart (D.inverse z) j.castSucc = 0)}
  obtain ⟨hZ, hfaces⟩ := D.local_vertex_faces hcore v hv C hC hface haxis
  have hgeometry (b : Bool) := D.local_incident_quarter hcore (s b) (hs b) (hcard b)
    v (hvs b) C hC hface haxis hsheet signs
  choose a b hab hQball hUball hOball hUO hQV hQlink using hgeometry
  have hZF (j : Fin 2) : Z ⊆ face j := by
    rintro z ⟨hz, ha⟩
    have hzero := ((haxis z (D.vertex_dual_subset_star v hv hz)).mp ha).2
    fin_cases j <;> cases he : signs (0 : Fin 2) <;> cases he' : signs (1 : Fin 2) <;>
      simp [face, SignedJointCross.side, hz, hzero.1, hzero.2]
  have hZO (j : Fin 2) : outer j ∩ Z = bZ := by
    ext z
    exact ⟨fun h => ⟨h.2, h.1.2⟩, fun h => ⟨⟨hZF j h.1, h.2⟩, h.1⟩⟩
  have hFF : face 0 ∩ face 1 = Z := by
    ext z
    constructor
    · rintro ⟨h0, h1⟩
      exact ⟨h0.1, (haxis z (D.vertex_dual_subset_star v hv h0.1)).mpr
        ⟨interior_subset (hcore (D.inverse z).property), h0.2.1, h1.2.1⟩⟩
    · exact fun hz => ⟨hZF 0 hz, hZF 1 hz⟩
  have hsheetDisk : IsFinitePLBallPair P2 (face 0 ∪ face 1) (outer 0 ∪ outer 1) := by
    apply IsFinitePLBallPair.union_of_interval_attachment (d := Z) (q := bZ)
    · simpa [face, outer, Z, V, SignedJointCross.side, union_comm] using (hfaces 0 (signs 1)).1
    · simpa [face, outer, Z, V, SignedJointCross.side, union_comm] using (hfaces 1 (signs 0)).1
    · exact (hfaces 0 (signs 1)).2
    · exact (hfaces 1 (signs 0)).2
    · exact hZ
    · exact hZO 0
    · exact hZO 1
    · exact hFF
  have hcontact (b : Bool) (j : Fin 2) :
      Q b ∩ face j = Q b ∩ {z | C.chart (D.inverse z) j.castSucc = 0} := by
    ext z
    exact ⟨fun hz => ⟨hz.1, hz.2.2.1⟩,
      fun hz => ⟨hz.1, hQV b hz.1, hz.2, hz.1.2 j.rev⟩⟩
  have hmeet (b : Bool) : (face 0 ∪ face 1) ∩ Q b = U b := by
    rw [inter_comm, inter_union_distrib_left, hcontact b 0, hcontact b 1]
    rfl
  have hUrim (b : Bool) : U b ⊆ outer 0 ∪ outer 1 := by
    rintro z (hz | hz)
    · exact Or.inl ⟨((hcontact b 0).superset hz).2, hQlink b hz.1⟩
    · exact Or.inr ⟨((hcontact b 1).superset hz).2, hQlink b hz.1⟩
  have hQdisj : Disjoint (Q false) (Q true) := hdisj.mono inter_subset_left inter_subset_left
  have hjoined := isFinitePLBallPair_two_ended_sector_boundary Q O U a b hsheetDisk
    hQball hUball hab hUrim hmeet hQdisj
  obtain ⟨rim, hdisk⟩ : ∃ rim, IsFinitePLBallPair P2 prescribed rim :=
    ⟨_, by simpa only [prescribed, union_assoc] using hjoined⟩
  have hfaceCut (j : Fin 2) {z : D.sample → ℝ × V3} (hz : z ∈ face j) : z ∈ cuts := by
    intro k
    have hj := hz.2.1
    fin_cases j <;> fin_cases k
    · change SignedJointCross.side (signs 0) (C.chart (D.inverse z) 0)
      change C.chart (D.inverse z) 0 = 0 at hj
      rw [hj]
      cases signs 0 <;> exact le_rfl
    · exact hz.2.2
    · exact hz.2.2
    · change SignedJointCross.side (signs 1) (C.chart (D.inverse z) 1)
      change C.chart (D.inverse z) 1 = 0 at hj
      rw [hj]
      cases signs 1 <;> exact le_rfl
  have hsub : prescribed ⊆ boundary := by
    rintro z ((hz | hz) | hz | hz)
    · exact ⟨hz.1, hfaceCut 0 hz, Or.inr ⟨0, hz.2.1⟩⟩
    · exact ⟨hz.1, hfaceCut 1 hz, Or.inr ⟨1, hz.2.1⟩⟩
    · exact ⟨hQV false hz, hz.2, Or.inl (hQlink false hz)⟩
    · exact ⟨hQV true hz, hz.2, Or.inl (hQlink true hz)⟩
  have hout : (boundary \ prescribed).Nonempty := by
    obtain ⟨z, hzV, hzlink, hzJ, hzstrict⟩ := D.exists_local_vertex_exterior_point
      hcore v hv C hC hface haxis hsheet s hs hcard hvs hdisj signs
    have hweak (j : Fin 2) : SignedJointCross.side (signs j)
        (C.chart (D.inverse z) j.castSucc) := by
      have hj := hzstrict j
      cases he : signs j <;> simp only [SignedJointCross.side, he, Bool.false_eq_true,
        if_false, if_true] at hj ⊢ <;> exact hj.le
    have hn (j : Fin 2) : C.chart (D.inverse z) j.castSucc ≠ 0 := by
      intro he
      have hj := hzstrict j
      cases signs j <;> simp [he] at hj
    refine ⟨z, ⟨hzV, hweak, Or.inl hzlink⟩, ?_⟩
    rintro ((hz | hz) | hz | hz)
    · exact hn 0 hz.2.1
    · exact hn 1 hz.2.1
    · exact hzJ false hz.1
    · exact hzJ true hz.1
  have hvstar : v ∈ (D.complex.closedStar v).space := by
    apply (D.complex.closedStar v).vertices_subset_space
    exact ⟨D.axis_le hv, by simpa using (show {v} ∈ D.complex.faces from D.axis_le hv)⟩
  have hvzero := ((haxis v hvstar).mp (D.axis.vertices_subset_space hv)).2
  have hball := isFinitePLBallPair_original_vertex_coordinate_sector D.complex D.homeomorph
    D.inverse D.inverse_value v (D.axis_le hv) (D.vertex_mem_interior_core v hv) C.chart
    (by convert hC using 1; congr 3; exact Subsingleton.elim _ _)
    (by convert hface using 1; congr 2; exact Subsingleton.elim _ _)
    (by intro j; fin_cases j; exact hvzero.1; exact hvzero.2) signs
  have hball' : IsFinitePLBallPair V3 (V.space ∩ cuts) boundary := by
    dsimp only [V, cuts, boundary, SignedJointCross.side]
    convert hball using 1
    congr 8
    funext z
    congr 6
    exact Subsingleton.elim _ _
  exact ⟨rim, hdisk, hsub, hout, hball',
    hball'.boundary_disk_complement (by simp) hdisk hsub hout, hFF, hcontact, hQdisj⟩

end PoincareConjecture.M76.Dehn
