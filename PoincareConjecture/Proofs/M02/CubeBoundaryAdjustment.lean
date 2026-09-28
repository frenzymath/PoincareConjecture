import PoincareConjecture.Proofs.M02.CubeHomotopyExtension
import Mathlib.AlgebraicTopology.FundamentalGroupoid.Basic








set_option autoImplicit false

open Set Metric Topology
open scoped unitInterval

namespace PoincareConjecture.Proofs.M02


theorem exists_cube_homotopy_of_boundary_homotopy
    {N Z : Type*} [Finite N] [TopologicalSpace Z]
    (f0 f1 : C(I^N, Z)) (H : f0.Homotopy f1)
    (K : C(unitInterval × (unitInterval × Cube.boundary N), Z))
    (hK0 : ∀ t (z : Cube.boundary N), K (0, (t, z)) = H (t, z))
    (hKL : ∀ s (z : Cube.boundary N), K (s, (0, z)) = f0 z)
    (hKR : ∀ s (z : Cube.boundary N), K (s, (1, z)) = f1 z) :
    ∃ H' : f0.Homotopy f1, ∀ t (z : Cube.boundary N), H' (t, z) = K (1, (t, z)) := by
  classical
  let A : Set (unitInterval × (I^N)) :=
    {z | z.1 = 0 ∨ z.1 = 1 ∨ z.2 ∈ Cube.boundary N}
  let bottom : Set (unitInterval × A) := {z | z.2.1.1 = 0}
  let top : Set (unitInterval × A) := {z | z.2.1.1 = 1}
  let side : Set (unitInterval × A) := {z | z.2.1.2 ∈ Cube.boundary N}
  let g : unitInterval × A → Z := fun z =>
    if h0 : z.2.1.1 = 0 then f0 z.2.1.2
    else if h1 : z.2.1.1 = 1 then f1 z.2.1.2
    else K (z.1, (z.2.1.1, ⟨z.2.1.2,
      (z.2.property.resolve_left h0).resolve_left h1⟩))
  have hg0 (z : unitInterval × A) (hz : z ∈ bottom) : g z = f0 z.2.1.2 := by
    change z.2.1.1 = 0 at hz
    dsimp [g]
    rw [dif_pos hz]
  have hg1 (z : unitInterval × A) (hz : z ∈ top) : g z = f1 z.2.1.2 := by
    change z.2.1.1 = 1 at hz
    have hn : z.2.1.1 ≠ 0 := by
      rw [hz]
      exact one_ne_zero
    dsimp [g]
    rw [dif_neg hn, dif_pos hz]
  have hgside (z : unitInterval × A) (hz : z ∈ side) :
      g z = K (z.1, (z.2.1.1, ⟨z.2.1.2, hz⟩)) := by
    dsimp [g]
    split_ifs with h0 h1
    · simpa only [h0] using (hKL z.1 ⟨z.2.1.2, hz⟩).symm
    · simpa only [h1] using (hKR z.1 ⟨z.2.1.2, hz⟩).symm
    · rfl
  have htime : Continuous (fun z : unitInterval × A => z.2.1.1) :=
    continuous_fst.comp (continuous_subtype_val.comp continuous_snd)
  have hspace : Continuous (fun z : unitInterval × A => z.2.1.2) :=
    continuous_snd.comp (continuous_subtype_val.comp continuous_snd)
  have hbottom : IsClosed bottom := isClosed_eq htime continuous_const
  have htop : IsClosed top := isClosed_eq htime continuous_const
  have hboundary : IsClosed (Cube.boundary N) := by
    simp only [Cube.boundary, ofPred_exists, ofPred_or]
    exact isClosed_iUnion_of_finite fun i =>
      (isClosed_eq (continuous_apply i) continuous_const).union
        (isClosed_eq (continuous_apply i) continuous_const)
  have hside : IsClosed side := hboundary.preimage hspace
  have hcover : (bottom ∪ top) ∪ side = univ := by
    ext z
    simp only [mem_union, mem_univ, iff_true]
    rcases z.2.property with hz | hz | hz
    · exact Or.inl (Or.inl hz)
    · exact Or.inl (Or.inr hz)
    · exact Or.inr hz
  have hcont0 : ContinuousOn g bottom :=
    (f0.continuous.comp hspace).continuousOn.congr hg0
  have hcont1 : ContinuousOn g top :=
    (f1.continuous.comp hspace).continuousOn.congr hg1
  have hcontside : ContinuousOn g side := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    let j : C(side, unitInterval × (unitInterval × Cube.boundary N)) :=
      ⟨fun z => (z.val.1, (z.val.2.val.1, ⟨z.val.2.val.2, z.property⟩)), by fun_prop⟩
    have hrestriction : side.domRestrict g = (K.comp j : side → Z) :=
      funext fun z => hgside z.val z.property
    rw [hrestriction]
    exact (K.comp j).continuous
  have hgcont : Continuous g := by
    apply continuousOn_univ.mp
    rw [← hcover]
    exact (hcont0.union_of_isClosed hcont1 hbottom htop).union_of_isClosed
      hcontside (hbottom.union htop) hside
  have hgstart (z : A) : g (0, z) = H z.val := by
    change g (0, z) = H (z.1.1, z.1.2)
    dsimp [g]
    split_ifs with h0 h1
    · simpa only [h0] using (H.apply_zero z.1.2).symm
    · simpa only [h1] using (H.apply_one z.1.2).symm
    · exact hK0 _ _
  obtain ⟨e, _, _, he⟩ := exists_cube_cylinder_homeomorph N
  let boundaryMap : C(Cube.boundary (Option N), A) :=
    ⟨fun z => ⟨e.symm z, (he (e.symm z)).mp (by
      rw [e.apply_symm_apply]
      exact z.property)⟩,
      (e.symm.continuous.comp continuous_subtype_val).subtype_mk _⟩
  let f : C(I^(Option N), Z) := H.toContinuousMap.comp ⟨e.symm, e.symm.continuous⟩
  let h : C(unitInterval × Cube.boundary (Option N), Z) :=
    (⟨g, hgcont⟩ : C(unitInterval × A, Z)).comp
      ⟨fun z => (z.1, boundaryMap z.2),
        continuous_fst.prodMk (boundaryMap.continuous.comp continuous_snd)⟩
  obtain ⟨F, _, hFB⟩ := exists_cube_homotopy_extension f h
    (fun z => hgstart (boundaryMap z))
  have hFe (s : unitInterval) (z : A) : F (s, e z.val) = g (s, z) := by
    let v : Cube.boundary (Option N) := ⟨e z.val, (he z.val).mpr z.property⟩
    have hbz : boundaryMap v = z := by
      apply Subtype.ext
      exact e.symm_apply_apply z.val
    have hv := hFB s v
    change F (s, e z.val) = g (s, boundaryMap v) at hv
    simpa only [hbz] using hv
  refine ⟨{
    toFun := fun z => F (1, e z)
    continuous_toFun := F.continuous.comp (continuous_const.prodMk e.continuous)
    map_zero_left := ?_
    map_one_left := ?_
  }, ?_⟩
  · intro z
    exact (hFe 1 ⟨(0, z), Or.inl rfl⟩).trans
      (hg0 (1, ⟨(0, z), Or.inl rfl⟩) rfl)
  · intro z
    exact (hFe 1 ⟨(1, z), Or.inr (Or.inl rfl)⟩).trans
      (hg1 (1, ⟨(1, z), Or.inr (Or.inl rfl)⟩) rfl)
  · intro t z
    exact (hFe 1 ⟨(t, z), Or.inr (Or.inr z.property)⟩).trans
      (hgside (1, ⟨(t, z), Or.inr (Or.inr z.property)⟩) z.property)


theorem cube_homotopicRel_of_homotopies_with_same_boundary
    {N Z : Type*} [Finite N] [TopologicalSpace Z]
    (u v w : C(I^N, Z)) (H : u.Homotopy v) (G : u.Homotopy w)
    (htrace : ∀ t (z : Cube.boundary N), H (t, z) = G (t, z)) :
    v.HomotopicRel w (Cube.boundary N) := by
  have hboundary : IsClosed (Cube.boundary N) := by
    simp only [Cube.boundary, ofPred_exists, ofPred_or]
    exact isClosed_iUnion_of_finite fun i =>
      (isClosed_eq (continuous_apply i) continuous_const).union
        (isClosed_eq (continuous_apply i) continuous_const)
  let : LocallyCompactSpace (Cube.boundary N) := hboundary.locallyCompactSpace
  let side : C(unitInterval × Cube.boundary N, Z) := H.toContinuousMap.comp
    ⟨fun z => (z.1, (z.2 : I^N)), continuous_fst.prodMk continuous_snd.subtype_val⟩
  let gamma : Path (u.restrict (Cube.boundary N)) (v.restrict (Cube.boundary N)) := {
    toContinuousMap := side.curry
    source' := by
      ext z
      exact H.apply_zero z
    target' := by
      ext z
      exact H.apply_one z
  }
  have hconcat (t : unitInterval) (z : Cube.boundary N) :
      (H.symm.trans G) (t, z) = (gamma.symm.trans gamma) t z := by
    rw [ContinuousMap.Homotopy.trans_apply, Path.trans_apply]
    split_ifs
    · rfl
    · exact (htrace _ z).symm
  have hvw (z : Cube.boundary N) : v z = w z :=
    (H.apply_one z).symm.trans ((htrace 1 z).trans (G.apply_one z))
  obtain ⟨P⟩ := Path.Homotopic.symm_trans gamma
  let K : C(unitInterval × (unitInterval × Cube.boundary N), Z) :=
    ⟨fun z => P (z.1, z.2.1) z.2.2,
      (P.continuous.comp (continuous_fst.prodMk
        (continuous_fst.comp continuous_snd))).eval (continuous_snd.comp continuous_snd)⟩
  have hK0 (t : unitInterval) (z : Cube.boundary N) :
      K (0, (t, z)) = (H.symm.trans G) (t, z) :=
    (congrArg (fun a : C(Cube.boundary N, Z) => a z) (P.apply_zero t)).trans
      (hconcat t z).symm
  have hKL (s : unitInterval) (z : Cube.boundary N) : K (s, (0, z)) = v z :=
    congrArg (fun a : C(Cube.boundary N, Z) => a z) (P.source s)
  have hKR (s : unitInterval) (z : Cube.boundary N) : K (s, (1, z)) = w z :=
    (congrArg (fun a : C(Cube.boundary N, Z) => a z) (P.target s)).trans (hvw z)
  obtain ⟨F, hF⟩ := exists_cube_homotopy_of_boundary_homotopy v w
    (H.symm.trans G) K hK0 hKL hKR
  refine ⟨{ toHomotopy := F, prop' := ?_ }⟩
  intro t z hz
  exact (hF t ⟨z, hz⟩).trans
    (congrArg (fun a : C(Cube.boundary N, Z) => a ⟨z, hz⟩) (P.apply_one t))

end PoincareConjecture.Proofs.M02
