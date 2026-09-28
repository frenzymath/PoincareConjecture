import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.Tubes.LocalEdgeJoints
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.Tubes.LocalJointRadii
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.EmbeddedStarDualInterval
import PoincareConjecture.Proofs.M76.Mathlib.BarycentricDualSubcomplex
import PoincareConjecture.Proofs.M76.Mathlib.PairedFacetChartSigns

set_option autoImplicit false
open Set Metric Geometry Topology

namespace PoincareConjecture.M76.Dehn

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)

open Classical in


theorem ComponentBranchModel.exists_local_sheet_interval
    {X ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {f : V2 → X} {R : Set X}
    {old : OrdinaryDoubleCurveModel e f R} {i : old.Index}
    (D : ComponentBranchModel old i) (hcore : D.core ⊆ interior R)
    (s : Finset (D.sample → ℝ × V3)) (hs : s ∈ D.axis.faces) (hcard : s.card = 2)
    (p : D.sample → ℝ × V3) (hps : p ∈ s)
    {x y : V2} (C : RawCrossingChart e f R x y)
    (hC : MapsTo (fun z ↦ (D.inverse z : X)) (D.complex.closedStar p).space C.chart.source)
    (hface : (D.complex.closedStar p).AffineOnFaces (fun z ↦ C.chart (D.inverse z)))
    (haxis : ∀ z ∈ (D.complex.closedStar p).space,
      z ∈ D.axis.space ↔ (D.inverse z : X) ∈ R ∧
        C.chart (D.inverse z) 0 = 0 ∧ C.chart (D.inverse z) 1 = 0)
    (j : Fin 2)
    (hsheet : ((D.complex.closedStar p).vertexSubcomplex
        {z | (D.inverse z : X) ∈ R ∧ C.chart (D.inverse z) j.castSucc = 0}).space =
      (D.complex.closedStar p).space ∩
        {z | (D.inverse z : X) ∈ R ∧ C.chart (D.inverse z) j.castSucc = 0}) :
    letI : Fintype D.complex.faces := D.complex_finite.fintype
    let N := (D.complex.closedStar p).vertexSubcomplex
      {z | (D.inverse z : X) ∈ R ∧ C.chart (D.inverse z) j.castSucc = 0}
    letI : Fintype N.faces := ((D.complex.closedStar p).vertexSubcomplex_finite _
      (SimplicialComplex.finite_closedStar_faces D.complex_finite p)).fintype
    ∃ t ∈ N.faces, ∃ u ∈ N.faces,
      s ⊆ t ∧ s ⊆ u ∧ t.card = 3 ∧ u.card = 3 ∧ t ≠ u ∧
      (∀ v ∈ N.faces, s ⊆ v → v.card = 3 → v = t ∨ v = u) ∧
      IsFinitePLBallPair ℝ (N.barycentricDualBlock s).space
        {t.centroid ℝ id, u.centroid ℝ id} ∧
      s.centroid ℝ id ∈ (N.barycentricDualBlock s).space \
        {t.centroid ℝ id, u.centroid ℝ id} ∧
      ((N.barycentricDualBlock s).link (s.centroid ℝ id)).space =
        {t.centroid ℝ id, u.centroid ℝ id} ∧
      (N.barycentricDualBlock s).space = (D.complex.barycentricDualBlock s).space ∩
        {z | C.chart (D.inverse z) j.castSucc = 0} ∧
      (N.barycentricDualBlock s).space ∩
          ((D.complex.barycentricDualBlock s).link (s.centroid ℝ id)).space =
        {t.centroid ℝ id, u.centroid ℝ id} ∧
      C.chart (D.inverse (t.centroid ℝ id)) j.rev.castSucc < 0 ∧
      0 < C.chart (D.inverse (u.centroid ℝ id)) j.rev.castSucc ∧
      (N.barycentricDualBlock s).space =
        segment ℝ (s.centroid ℝ id) (t.centroid ℝ id) ∪
          segment ℝ (s.centroid ℝ id) (u.centroid ℝ id) ∧
      segment ℝ (s.centroid ℝ id) (t.centroid ℝ id) ∩
          segment ℝ (s.centroid ℝ id) (u.centroid ℝ id) = {s.centroid ℝ id} := by
  classical
  let : Fintype D.complex.faces := D.complex_finite.fintype
  let K := D.complex.closedStar p
  let N := K.vertexSubcomplex
    {z | (D.inverse z : X) ∈ R ∧ C.chart (D.inverse z) j.castSucc = 0}
  have hNfinite : N.faces.Finite := K.vertexSubcomplex_finite _
    (SimplicialComplex.finite_closedStar_faces D.complex_finite p)
  let : Fintype N.faces := hNfinite.fintype
  have hNK : N ≤ K := K.vertexSubcomplex_le _
  have hKD : K ≤ D.complex := fun _ ht => ht.1
  have hNstar : N.closedStar p ≤ K := fun _ ht => hNK ht.1
  have hNk := SimplicialComplex.space_subset_of_le hNK
  have hKk := SimplicialComplex.space_subset_of_le hKD
  have hp := D.axis.face_subset_vertices hs hps
  have hpK : p ∈ D.complex.vertices := D.axis_le hp
  have hsK : s ∈ K.faces := ⟨D.axis_le hs, by
    simpa only [Finset.insert_eq_of_mem hps] using D.axis_le hs⟩
  have hsN : s ∈ N.faces := by
    refine ⟨hsK, fun v hv => ?_⟩
    have hzero := (haxis v (K.subset_space hsK hv)).mp (D.axis.subset_space hs hv)
    refine ⟨hzero.1, ?_⟩
    fin_cases j
    · exact hzero.2.1
    · exact hzero.2.2
  have hpN : p ∈ N.vertices := N.face_subset_vertices hsN hps
  have hpstar := hNk (N.vertices_subset_space hpN)
  have hpzero := (haxis p hpstar).mp (D.axis.vertices_subset_space hp)
  have hpcore : (D.inverse p : X) ∈ interior D.core := by
    apply D.core_neighborhood
    obtain ⟨a, ha, hap⟩ := D.axis_space.subset (D.axis.vertices_subset_space hp)
    exact ⟨a, ha, (D.graph_separates _ (D.inverse p).property _
      ((D.graph_inverse p (D.complex.vertices_subset_space hpK)).trans hap.symm)).symm⟩
  obtain ⟨hchartinj, ⟨O, hOo, hpO, hOC, hOK⟩, _⟩ :=
    D.complex.exists_original_open_neighborhood_inside_closedStar D.complex_finite
      D.homeomorph D.inverse D.inverse_value hpK hpcore C.chart hC
  let r : V3 →ᴬ[ℝ] P2 := ((ContinuousLinearMap.proj j.rev.castSucc).prod
    (ContinuousLinearMap.proj (2 : Fin 3))).toContinuousAffineMap
  let a : P2 →ᴬ[ℝ] V3 := (ContinuousLinearMap.pi fun k : Fin 3 =>
    if k = j.castSucc then 0 else
      if k = j.rev.castSucc then ContinuousLinearMap.fst ℝ ℝ ℝ
      else ContinuousLinearMap.snd ℝ ℝ ℝ).toContinuousAffineMap
  let shift : V3 →ᴬ[ℝ] V3 := ContinuousAffineMap.id ℝ V3 -
    ContinuousAffineMap.const ℝ V3 (C.chart (D.inverse p))
  let ell : (D.sample → ℝ × V3) → P2 :=
    fun z => r (C.chart (D.inverse z) - C.chart (D.inverse p))
  have hra (w : P2) : r (a w) = w := by fin_cases j <;> simp [r, a]
  have ha0 : a 0 = 0 := by ext k; fin_cases j <;> fin_cases k <;> simp [a]
  have haz (w : P2) : a w j.castSucc = 0 := by fin_cases j <;> simp [a]
  have hpz : C.chart (D.inverse p) j.castSucc = 0 := by
    fin_cases j
    · exact hpzero.2.1
    · exact hpzero.2.2
  have hNz (z : D.sample → ℝ × V3) (hz : z ∈ (N.closedStar p).space) :
      C.chart (D.inverse z) j.castSucc = 0 :=
    (hsheet.subset (SimplicialComplex.space_subset_of_le
      (show N.closedStar p ≤ N from fun _ ht => ht.1) hz)).2.2
  have hell : (N.closedStar p).AffineOnFaces ell :=
    ((show (N.closedStar p).AffineOnFaces (fun z => C.chart (D.inverse z)) from
      fun t ht => hface t (hNstar ht)).postcomp shift).postcomp r
  have helli : InjOn ell (N.closedStar p).space := by
    intro z hz w hw he
    apply hchartinj (SimplicialComplex.space_subset_of_le hNstar hz)
      (SimplicialComplex.space_subset_of_le hNstar hw)
    have he0 := congrArg Prod.fst he
    have he1 := congrArg Prod.snd he
    change C.chart (D.inverse z) j.rev.castSucc - C.chart (D.inverse p) j.rev.castSucc =
      C.chart (D.inverse w) j.rev.castSucc - C.chart (D.inverse p) j.rev.castSucc at he0
    change C.chart (D.inverse z) 2 - C.chart (D.inverse p) 2 =
      C.chart (D.inverse w) 2 - C.chart (D.inverse p) 2 at he1
    have he0' := sub_left_inj.mp he0
    have he1' := sub_left_inj.mp he1
    ext k
    fin_cases j <;> fin_cases k
    · exact (hNz z hz).trans (hNz w hw).symm
    · exact he0'
    · exact he1'
    · exact he0'
    · exact (hNz z hz).trans (hNz w hw).symm
    · exact he1'
  obtain ⟨eta, heta, hsmall⟩ := N.exists_ball_inter_space_subset_closedStar hNfinite hpN
  let U := O ∩ interior R ∩ D.graph ⁻¹' ball p eta
  have hUo : IsOpen U := (hOo.inter isOpen_interior).inter
    (isOpen_ball.preimage D.graph_continuous)
  have hpU : (D.inverse p : X) ∈ U :=
    ⟨⟨hpO, hcore (D.inverse p).property⟩,
      by change D.graph (D.inverse p) ∈ ball p eta
         rw [D.graph_inverse p (D.complex.vertices_subset_space hpK)]
         exact mem_ball_self heta⟩
  let b : X → V3 := fun z => C.chart z - C.chart (D.inverse p)
  have hbU : IsOpen (b '' U) := by
    have heq : b '' U = (Homeomorph.subRight (C.chart (D.inverse p))) '' (C.chart '' U) := by
      rw [image_image]; rfl
    rw [heq]
    exact (Homeomorph.subRight _).isOpenMap _
      (C.chart.isOpen_image_of_subset_source hUo (fun _ hz => hOC hz.1.1))
  let W := a ⁻¹' (b '' U)
  have hWo : IsOpen W := hbU.preimage a.continuous
  have hW0 : (0 : P2) ∈ W := ⟨D.inverse p, hpU, by simp [b, ha0]⟩
  have hWimage : W ⊆ ell '' (N.closedStar p).space := by
    rintro w ⟨z, hz, hbz⟩
    obtain ⟨v, hvK, hvz⟩ := hOK hz.1.1
    change (D.inverse v : X) = z at hvz
    have hgv : D.graph z = v := by rw [← hvz, D.graph_inverse v (hKk hvK)]
    have hvR : (D.inverse v : X) ∈ R := hvz.symm ▸ interior_subset hz.1.2
    have hvzero : C.chart (D.inverse v) j.castSucc = 0 := by
      have he := congrArg (fun q : V3 => q j.castSucc) hbz
      simpa only [b, Pi.sub_apply, hpz, sub_zero, haz, hvz] using he
    have hvN : v ∈ N.space := hsheet.symm.subset ⟨hvK, hvR, hvzero⟩
    refine ⟨v, hsmall ⟨hvN, hgv ▸ hz.2⟩, ?_⟩
    change r (C.chart (D.inverse v) - C.chart (D.inverse p)) = w
    rw [hvz]
    change r (b z) = w
    rw [hbz, hra]
  have hellp : ell p = 0 := by simp [ell, r]
  have hint : ell p ∈ interior (ell '' (N.closedStar p).space) := by
    rw [hellp]
    exact interior_maximal hWimage hWo hW0
  obtain ⟨t, ht, u, hu, hst, hsu, htc, huc, htu, hco, hI, hmI, hbI⟩ :=
    N.exists_dual_interval_of_embedded_star hsN (by simpa using hcard) hps ell hell helli hint
  have hradii := N.dual_interval_eq_centroid_segments hsN ht hu hst hsu htu hI hmI
  let J := D.complex.barycentricDualBlock s
  have hND : N ≤ D.complex := le_trans hNK hKD
  have hJstar : J.space ⊆ K.space := by
    intro z hz
    have hzV := SimplicialComplex.space_subset_of_le
      (D.complex.barycentricDualBlock_antitone (Finset.singleton_subset_iff.mpr hps)) hz
    obtain ⟨v, hv, hzv⟩ := SimplicialComplex.mem_space_iff.mp hzV
    obtain ⟨w, hw, hvw⟩ := D.complex.exists_original_star_face_of_vertex_dual_face hpK hv
    exact K.convexHull_subset_space hw (hvw hzv)
  have hzero : (N.barycentricDualBlock s).space = J.space ∩
      {z | C.chart (D.inverse z) j.castSucc = 0} := by
    rw [← D.complex.barycentricDualBlock_space_inter_subcomplex N hND s]
    ext z
    constructor
    · rintro ⟨hz, hzN⟩
      exact ⟨hz, (hsheet.subset hzN).2.2⟩
    · rintro ⟨hz, hz0⟩
      exact ⟨hz, hsheet.symm.subset ⟨hJstar hz,
        interior_subset (hcore (D.inverse z).property), hz0⟩⟩
  have hboundary : (N.barycentricDualBlock s).space ∩
      (J.link (s.centroid ℝ id)).space = {t.centroid ℝ id, u.centroid ℝ id} := by
    rw [← J.link_space_eq_inter_of_closedStar_eq (N.barycentricDualBlock s)
      (D.complex.barycentricDualBlock_mono_of_subcomplex N hND s) (s.centroid ℝ id)
      (N.barycentricDualBlock_closedStar_faceCentroid hsN)]
    exact hbI
  have hsstar : s ∈ (N.closedStar p).faces :=
    ⟨hsN, by simpa only [Finset.insert_eq_of_mem hps] using hsN⟩
  have htstar : t ∈ (N.closedStar p).faces :=
    ⟨ht, by simpa only [Finset.insert_eq_of_mem (hst hps)] using ht⟩
  have hustar : u ∈ (N.closedStar p).faces :=
    ⟨hu, by simpa only [Finset.insert_eq_of_mem (hsu hps)] using hu⟩
  have hsign := hell.opposite_centroid_signs helli hsstar htstar hustar
    (by simpa using hcard) htc huc hst hsu htu (LinearMap.fst ℝ ℝ ℝ).toAffineMap
    (by intro hz; have h := congrArg (fun L : P2 →ₗ[ℝ] ℝ => L (1, 0)) hz; norm_num at h)
    (by
      intro z hzs
      change C.chart (D.inverse z) j.rev.castSucc - C.chart (D.inverse p) j.rev.castSucc = 0
      have hzaxis := (haxis z (K.subset_space hsK hzs)).mp (D.axis.subset_space hs hzs)
      fin_cases j <;> simp_all)
  have hprev : C.chart (D.inverse p) j.rev.castSucc = 0 := by
    fin_cases j
    · exact hpzero.2.2
    · exact hpzero.2.1
  change
    (C.chart (D.inverse (t.centroid ℝ id)) j.rev.castSucc - C.chart (D.inverse p) j.rev.castSucc < 0 ∧
      0 < C.chart (D.inverse (u.centroid ℝ id)) j.rev.castSucc - C.chart (D.inverse p) j.rev.castSucc) ∨
    (0 < C.chart (D.inverse (t.centroid ℝ id)) j.rev.castSucc - C.chart (D.inverse p) j.rev.castSucc ∧
      C.chart (D.inverse (u.centroid ℝ id)) j.rev.castSucc - C.chart (D.inverse p) j.rev.castSucc < 0) at hsign
  simp only [hprev, sub_zero] at hsign
  rcases hsign with hsign | hsign
  · refine ⟨t, ht, u, hu, hst, hsu, ?_, ?_, htu, ?_, hI, hmI, hbI, hzero, hboundary,
      hsign.1, hsign.2, hradii⟩
    · simpa using htc
    · simpa using huc
    · intro v hv hsv hvc
      exact hco v hv hsv (by simpa using hvc)
  · refine ⟨u, hu, t, ht, hsu, hst, ?_, ?_, htu.symm, ?_, ?_, ?_, ?_, hzero, ?_,
      hsign.2, hsign.1, ?_, ?_⟩
    · simpa using huc
    · simpa using htc
    · intro v hv hsv hvc
      exact (hco v hv hsv (by simpa using hvc)).symm
    · simpa only [pair_comm] using hI
    · simpa only [pair_comm] using hmI
    · simpa only [pair_comm] using hbI
    · simpa only [pair_comm] using hboundary
    · simpa only [union_comm] using hradii.1
    · simpa only [inter_comm] using hradii.2

open Classical in



theorem ComponentBranchModel.exists_raw_edge_joint_intervals
    {X ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {f : V2 → X} {R : Set X}
    {old : OrdinaryDoubleCurveModel e f R} {i : old.Index}
    (D : ComponentBranchModel old i) (hcore : D.core ⊆ interior R)
    (s : Finset (D.sample → ℝ × V3)) (hs : s ∈ D.axis.faces) (hcard : s.card = 2)
    (p : D.sample → ℝ × V3) (hps : p ∈ s) :
    letI : Fintype D.complex.faces := D.complex_finite.fintype
    ∃ (x y : V2) (C : RawCrossingChart e f R x y),
      MapsTo (fun z ↦ (D.inverse z : X)) (D.complex.closedStar p).space C.chart.source ∧
      (D.complex.closedStar p).AffineOnFaces (fun z ↦ C.chart (D.inverse z)) ∧
      (∀ z ∈ (D.complex.closedStar p).space,
        z ∈ D.axis.space ↔ (D.inverse z : X) ∈ R ∧
          C.chart (D.inverse z) 0 = 0 ∧ C.chart (D.inverse z) 1 = 0) ∧
      (∀ j : Fin 2,
        ((D.complex.closedStar p).vertexSubcomplex
          {z | (D.inverse z : X) ∈ R ∧ C.chart (D.inverse z) j.castSucc = 0}).space =
        (D.complex.closedStar p).space ∩
          {z | (D.inverse z : X) ∈ R ∧ C.chart (D.inverse z) j.castSucc = 0}) ∧
      IsFinitePLBallPair P2 (D.complex.barycentricDualBlock s).space
        ((D.complex.barycentricDualBlock s).link (s.centroid ℝ id)).space ∧
      (D.complex.barycentricDualBlock s).space ∩ D.axis.space = {s.centroid ℝ id} ∧
      ∀ j : Fin 2,
        let N := (D.complex.closedStar p).vertexSubcomplex
          {z | (D.inverse z : X) ∈ R ∧ C.chart (D.inverse z) j.castSucc = 0}
        letI : Fintype N.faces := ((D.complex.closedStar p).vertexSubcomplex_finite _
          (SimplicialComplex.finite_closedStar_faces D.complex_finite p)).fintype
        ∃ t ∈ N.faces, ∃ u ∈ N.faces,
          s ⊆ t ∧ s ⊆ u ∧ t.card = 3 ∧ u.card = 3 ∧ t ≠ u ∧
          (∀ v ∈ N.faces, s ⊆ v → v.card = 3 → v = t ∨ v = u) ∧
          IsFinitePLBallPair ℝ (N.barycentricDualBlock s).space
            {t.centroid ℝ id, u.centroid ℝ id} ∧
          s.centroid ℝ id ∈ (N.barycentricDualBlock s).space \
            {t.centroid ℝ id, u.centroid ℝ id} ∧
          ((N.barycentricDualBlock s).link (s.centroid ℝ id)).space =
            {t.centroid ℝ id, u.centroid ℝ id} ∧
          (N.barycentricDualBlock s).space = (D.complex.barycentricDualBlock s).space ∩
            {z | C.chart (D.inverse z) j.castSucc = 0} ∧
          (N.barycentricDualBlock s).space ∩
              ((D.complex.barycentricDualBlock s).link (s.centroid ℝ id)).space =
            {t.centroid ℝ id, u.centroid ℝ id} ∧
          C.chart (D.inverse (t.centroid ℝ id)) j.rev.castSucc < 0 ∧
          0 < C.chart (D.inverse (u.centroid ℝ id)) j.rev.castSucc ∧
          (N.barycentricDualBlock s).space =
            segment ℝ (s.centroid ℝ id) (t.centroid ℝ id) ∪
              segment ℝ (s.centroid ℝ id) (u.centroid ℝ id) ∧
          segment ℝ (s.centroid ℝ id) (t.centroid ℝ id) ∩
              segment ℝ (s.centroid ℝ id) (u.centroid ℝ id) = {s.centroid ℝ id} := by
  obtain ⟨x, y, C, hC, hface, haxis, hsheet, hJ, hJA⟩ := D.exists_raw_edge_joint s hs hcard p hps
  exact ⟨x, y, C, hC, hface, haxis, hsheet, hJ, hJA,
    fun j => D.exists_local_sheet_interval hcore s hs hcard p hps C hC hface haxis j (hsheet j)⟩

end PoincareConjecture.M76.Dehn
