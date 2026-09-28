import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.Tubes.IncidentJointSigns
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surgery.Tubes.Joints.SharedBranches

set_option autoImplicit false
open Set Metric Geometry Topology Geometry.SimplicialComplex

namespace PoincareConjecture.M76.Dehn.Annuli

local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)

open Classical in
theorem ComponentBranchModel.exists_incident_joint_signs
    {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace X] {S : Set E}
    {e : ι → OpenPartialHomeomorph X V3} {f : E → X} {R : Set X}
    {old : SourceCircleDecomposition f S} {i : old.Index}
    (D : ComponentBranchModel (e := e) (R := R) old i) [Fintype D.complex.faces]
    (hcore : D.core ⊆ interior R)
    (s : Finset (D.sample → ℝ × V3)) (hs : s ∈ D.axis.faces) (hcard : s.card = 2)
    (v : D.sample → ℝ × V3) (hvs : v ∈ s)
    {x y : E} (C : RawSourceCrossing e f S R x y)
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
    (J : SignedJointCross (D.sample → ℝ × V3))
    (hJ : J.disk = (D.complex.barycentricDualBlock s).space)
    (hcoface : ∀ j b, ∃ t : Finset (D.sample → ℝ × V3),
      t ∈ D.complex.faces ∧ s ⊆ t ∧ t.card = 3 ∧ J.endpoint j b = t.centroid ℝ id)
    (swap : Bool)
    (hzero : ∀ j z, z ∈ J.disk → (J.coordinate j z = 0 ↔
      C.chart (D.inverse z) (jointSheetIndex swap j).castSucc = 0)) :
    ∃ eta : Fin 2 → Bool, ∀ j : Fin 2,
      if eta j then
        C.chart (D.inverse (J.endpoint j.rev false)) (jointSheetIndex swap j).castSucc < 0 ∧
          0 < C.chart (D.inverse (J.endpoint j.rev true)) (jointSheetIndex swap j).castSucc
      else
        0 < C.chart (D.inverse (J.endpoint j.rev false)) (jointSheetIndex swap j).castSucc ∧
          C.chart (D.inverse (J.endpoint j.rev true)) (jointSheetIndex swap j).castSucc < 0 := by
  classical
  have hex (j : Fin 2) : ∃ b : Bool,
      if b then
        C.chart (D.inverse (J.endpoint j.rev false)) (jointSheetIndex swap j).castSucc < 0 ∧
          0 < C.chart (D.inverse (J.endpoint j.rev true)) (jointSheetIndex swap j).castSucc
      else
        0 < C.chart (D.inverse (J.endpoint j.rev false)) (jointSheetIndex swap j).castSucc ∧
          C.chart (D.inverse (J.endpoint j.rev true)) (jointSheetIndex swap j).castSucc < 0 := by
    let k := jointSheetIndex swap j.rev
    let N := (D.complex.closedStar v).vertexSubcomplex
      {z | (D.inverse z : X) ∈ R ∧ C.chart (D.inverse z) k.castSucc = 0}
    have hNK : N ≤ D.complex.closedStar v := (D.complex.closedStar v).vertexSubcomplex_le _
    have hND : N ≤ D.complex := fun _ ht => (hNK ht).1
    let : Fintype N.faces := ((D.complex.closedStar v).vertexSubcomplex_finite _
      (SimplicialComplex.finite_closedStar_faces D.complex_finite v)).fintype
    have hcentroid (b : Bool) : J.endpoint j.rev b ∈ N.space := by
      have haI := J.radius_subset_axis j.rev b (right_mem_segment ℝ _ _)
      apply (hsheet k).symm.subset
      exact ⟨D.joint_subset_star hs hvs (hJ.subset haI.1),
        interior_subset (hcore (D.inverse _).property), (hzero j.rev _ haI.1).mp haI.2⟩
    obtain ⟨t, ht, hst, htc, hat⟩ := hcoface j.rev false
    obtain ⟨u, hu, hsu, huc, hau⟩ := hcoface j.rev true
    have htN : t ∈ N.faces := D.complex.face_mem_subcomplex_of_centroid N hND ht
      (hat ▸ hcentroid false)
    have huN : u ∈ N.faces := D.complex.face_mem_subcomplex_of_centroid N hND hu
      (hau ▸ hcentroid true)
    have hsN : s ∈ N.faces := N.down_closed htN hst (D.axis.nonempty_of_mem_faces hs)
    have htu : t ≠ u := by
      intro he
      exact J.endpoints_ne j.rev (hat.trans ((congrArg (fun t => t.centroid ℝ id) he).trans hau.symm))
    let r : V3 →ᴬ[ℝ] P2 := ((ContinuousLinearMap.proj k.rev.castSucc).prod
      (ContinuousLinearMap.proj (2 : Fin 3))).toContinuousAffineMap
    let ell : (D.sample → ℝ × V3) → P2 := fun z => r (C.chart (D.inverse z))
    have hell : N.AffineOnFaces ell :=
      (show N.AffineOnFaces (fun z => C.chart (D.inverse z)) from
        fun t ht => hface t (hNK ht)).postcomp r
    have hNz (z : D.sample → ℝ × V3) (hz : z ∈ N.space) :
        C.chart (D.inverse z) k.castSucc = 0 := ((hsheet k).subset hz).2.2
    have hchartinj : InjOn (fun z => C.chart (D.inverse z)) (D.complex.closedStar v).space := by
      intro z hz w hw he
      have hzw := C.chart.injOn (hC hz) (hC hw) he
      have hzK := SimplicialComplex.space_subset_of_le
        (show D.complex.closedStar v ≤ D.complex from fun _ ht => ht.1) hz
      have hwK := SimplicialComplex.space_subset_of_le
        (show D.complex.closedStar v ≤ D.complex from fun _ ht => ht.1) hw
      exact (D.graph_inverse z hzK).symm.trans ((congrArg D.graph hzw).trans (D.graph_inverse w hwK))
    have helli : InjOn ell N.space := by
      intro z hz w hw he
      apply hchartinj (SimplicialComplex.space_subset_of_le hNK hz)
        (SimplicialComplex.space_subset_of_le hNK hw)
      have he0 := congrArg Prod.fst he
      have he1 := congrArg Prod.snd he
      change C.chart (D.inverse z) k.rev.castSucc = C.chart (D.inverse w) k.rev.castSucc at he0
      change C.chart (D.inverse z) 2 = C.chart (D.inverse w) 2 at he1
      have hk : k = 0 ∨ k = 1 := by omega
      have hez := (hNz z hz).trans (hNz w hw).symm
      rcases hk with hk | hk
      · ext l
        fin_cases l
        · simpa [hk] using hez
        · simpa [hk] using he0
        · exact he1
      · ext l
        fin_cases l
        · simpa [hk] using he0
        · simpa [hk] using hez
        · exact he1
    have hsign := hell.opposite_centroid_signs helli hsN htN huN
      (by simpa using hcard) (by simpa using htc) (by simpa using huc) hst hsu htu
      (LinearMap.fst ℝ ℝ ℝ).toAffineMap
      (by intro hz; have h := congrArg (fun L : P2 →ₗ[ℝ] ℝ => L (1, 0)) hz; norm_num at h)
      (by
        intro z hzs
        have hzstar := SimplicialComplex.space_subset_of_le hNK (N.subset_space hsN hzs)
        have hzA := (haxis z hzstar).mp (D.axis.subset_space hs hzs)
        change C.chart (D.inverse z) k.rev.castSucc = 0
        have hk : k = 0 ∨ k = 1 := by omega
        rcases hk with hk | hk
        · simpa [hk] using hzA.2.2
        · simpa [hk] using hzA.2.1)
    change (C.chart (D.inverse (t.centroid ℝ id)) k.rev.castSucc < 0 ∧
        0 < C.chart (D.inverse (u.centroid ℝ id)) k.rev.castSucc) ∨
      (0 < C.chart (D.inverse (t.centroid ℝ id)) k.rev.castSucc ∧
        C.chart (D.inverse (u.centroid ℝ id)) k.rev.castSucc < 0) at hsign
    have hk : k.rev = jointSheetIndex swap j := by simp [k, jointSheetIndex_rev]
    rw [hk, ← hat, ← hau] at hsign
    exact hsign.elim (fun h => ⟨true, h⟩) (fun h => ⟨false, h⟩)
  exact Classical.axiomOfChoice hex

end PoincareConjecture.M76.Dehn.Annuli
