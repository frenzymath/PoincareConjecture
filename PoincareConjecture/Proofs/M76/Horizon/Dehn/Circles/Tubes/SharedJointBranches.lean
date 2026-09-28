import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.Tubes.SignedJointQuarters

set_option autoImplicit false
open Set Metric Geometry Topology

namespace PoincareConjecture.M76.Dehn

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D2" => closedBall (0 : V2) 1

open Classical in

theorem ComponentBranchModel.joint_subset_star
    {X ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {f : V2 → X} {R : Set X}
    {old : OrdinaryDoubleCurveModel e f R} {i : old.Index}
    (D : ComponentBranchModel old i) [Fintype D.complex.faces]
    {s : Finset (D.sample → ℝ × V3)} (hs : s ∈ D.axis.faces)
    {p : D.sample → ℝ × V3} (hps : p ∈ s) :
    (D.complex.barycentricDualBlock s).space ⊆ (D.complex.closedStar p).space := by
  intro z hz
  have hzV := SimplicialComplex.space_subset_of_le
    (D.complex.barycentricDualBlock_antitone (Finset.singleton_subset_iff.mpr hps)) hz
  obtain ⟨v, hv, hzv⟩ := SimplicialComplex.mem_space_iff.mp hzV
  obtain ⟨w, hw, hvw⟩ := D.complex.exists_original_star_face_of_vertex_dual_face
    (D.axis_le (D.axis.face_subset_vertices hs hps)) hv
  exact (D.complex.closedStar p).convexHull_subset_space hw (hvw hzv)

theorem ComponentBranchModel.exists_joint_sheet_swap
    {X ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {f : V2 → X} {R : Set X}
    {old : OrdinaryDoubleCurveModel e f R} {i : old.Index}
    (D : ComponentBranchModel old i) (hcore : D.core ⊆ interior R)
    (L : SimplicialComplex ℝ (D.sample → ℝ × V3)) (hL : L.faces.Finite)
    (hLK : L.space ⊆ D.complex.space)
    {x y x' y' : V2} (C : RawCrossingChart e f R x y) (C' : RawCrossingChart e f R x' y')
    (hLC : MapsTo (fun z ↦ (D.inverse z : X)) L.space C.chart.source)
    (hLC' : MapsTo (fun z ↦ (D.inverse z : X)) L.space C'.chart.source)
    (J : SignedJointCross (D.sample → ℝ × V3)) (hJ : J.disk = L.space)
    (hcoord : J.coordinate = fun j z => C.chart (D.inverse z) j.castSucc) :
    ∃ swap : Bool, ∀ (j : Bool) z, z ∈ L.space →
      (C.chart (D.inverse z) (if j then 1 else 0) = 0 ↔
        C'.chart (D.inverse z) (if Bool.xor swap j then 1 else 0) = 0) := by
  classical
  obtain ⟨P, u, hP, hPs, huPL, hu, huinv, hcover⟩ :=
    D.exists_local_branch_inverses L hL hLK C hLC
  let sheet (j : Bool) := L.space ∩
    {z | (D.inverse z : X) ∈ R ∧ C.chart (D.inverse z) (if j then 1 else 0) = 0}
  have hsheet (j : Bool) : sheet j = J.axis (if j then 1 else 0) := by
    ext z
    simp only [sheet, SignedJointCross.axis, hJ, hcoord]
    have hzR : (D.inverse z : X) ∈ R := interior_subset (hcore (D.inverse z).property)
    cases j <;> simp [hzR]
  have hconn (j : Bool) : IsPreconnected (P j).space := by
    have hc : IsPreconnected (sheet j) := by
      rw [hsheet j]
      exact (J.axis_ball _).isConnected.isPreconnected
    let : PreconnectedSpace (sheet j) := isPreconnected_iff_preconnectedSpace.mp hc
    have hrange : range (fun z : sheet j => (u j z : V2)) = (P j).space := by
      ext a
      constructor
      · rintro ⟨z, rfl⟩
        exact (u j z).property
      · intro ha
        obtain ⟨z, hz⟩ := (u j).surjective ⟨a, ha⟩
        exact ⟨z, congrArg Subtype.val hz⟩
    rw [← hrange]
    exact isPreconnected_range (continuous_subtype_val.comp (u j).continuous)
  have hPD (j : Bool) : (P j).space ⊆ D2 :=
    fun _ ha => ((hPs j).subset ha).1.1
  have hPf (j : Bool) (a : (P j).space) : f a = (D.inverse ((u j).symm a) : X) := by
    have he := (hu j ((u j).symm a)).1
    simpa only [Homeomorph.apply_symm_apply] using he
  have hPC' (j : Bool) : MapsTo f (P j).space C'.chart.source := by
    intro a ha
    rw [hPf j ⟨a, ha⟩]
    exact hLC' ((u j).symm ⟨a, ha⟩).property.1
  have hm (j : Bool) : J.center ∈ sheet j := by
    rw [hsheet j]
    exact (J.center_interior _).1
  let a : (P false).space := u false ⟨J.center, hm false⟩
  let b : (P true).space := u true ⟨J.center, hm true⟩
  have hab : (a : V2) ≠ b := by
    intro he
    exact C.disjoint.notMem_of_mem_left ((hPs false).subset a.property).2
      (he ▸ ((hPs true).subset b.property).2)
  obtain ⟨swap, hswap0, hswap1⟩ := C'.exists_connected_lift_swap
    (hconn false) (hconn true) (hPD false) (hPD true) (hPC' false) (hPC' true)
    ⟨a, a.property, b, b.property, hab,
      (hu false ⟨J.center, hm false⟩).1.trans (hu true ⟨J.center, hm true⟩).1.symm⟩
  let branch (j : Bool) := if j then C'.right else C'.left
  have hswap (j : Bool) : (P j).space ⊆ branch (Bool.xor swap j) := by
    cases j <;> cases swap <;> assumption
  have hbranchD (j : Bool) : branch j ⊆ D2 := by
    cases j
    · exact C'.left_subset
    · exact C'.right_subset
  have himage (j : Bool) (z : X) (hz : z ∈ C'.chart.source) :
      z ∈ f '' branch j ↔ z ∈ R ∧ C'.chart z (if j then 1 else 0) = 0 := by
    cases j
    · exact (C'.left_image z hz).trans and_comm
    · exact (C'.right_image z hz).trans and_comm
  refine ⟨swap, fun j z hz => ⟨?_, ?_⟩⟩
  · intro hz0
    let z' : sheet j := ⟨z, hz, interior_subset (hcore (D.inverse z).property), hz0⟩
    exact ((himage (Bool.xor swap j) (D.inverse z) (hLC' hz)).mp
      ⟨u j z', hswap j (u j z').property, (hu j z').1⟩).2
  · intro hz0
    obtain ⟨a, ha, haf⟩ := (himage (Bool.xor swap j) (D.inverse z) (hLC' hz)).mpr
      ⟨interior_subset (hcore (D.inverse z).property), hz0⟩
    have hgraph : D.graph (f a) = z := (congrArg D.graph haf).trans (D.graph_inverse z (hLK hz))
    have hacover : a ∈ (P false).space ∪ (P true).space := hcover.symm.subset
      ⟨hbranchD _ ha, show D.graph (f a) ∈ L.space from hgraph.symm ▸ hz⟩
    have haP : a ∈ (P j).space := by
      cases j
      · rcases hacover with h | h
        · exact h
        · cases swap
          · exact (disjoint_left.mp C'.disjoint ha (hswap true h)).elim
          · exact (disjoint_left.mp C'.disjoint (hswap true h) ha).elim
      · rcases hacover with h | h
        · cases swap
          · exact (disjoint_left.mp C'.disjoint (hswap false h) ha).elim
          · exact (disjoint_left.mp C'.disjoint ha (hswap false h)).elim
        · exact h
    have hzsheet := ((u j).symm ⟨a, haP⟩).property.2.2
    have hval : ((u j).symm ⟨a, haP⟩ : D.sample → ℝ × V3) = z :=
      (huinv j ⟨a, haP⟩).trans hgraph
    simpa only [hval] using hzsheet

end PoincareConjecture.M76.Dehn
