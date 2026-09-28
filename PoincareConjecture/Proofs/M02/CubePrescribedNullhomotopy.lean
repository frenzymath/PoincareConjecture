import PoincareConjecture.Proofs.M02.CubeBoundaryAdjustment

set_option autoImplicit false

open Set Metric Topology
open scoped unitInterval

namespace PoincareConjecture.Proofs.M02

theorem exists_cube_nullhomotopy_with_prescribed_boundary
    (n : ℕ) {X : Type*} [TopologicalSpace X] (x : X)
    (hpi : Subsingleton (HomotopyGroup.Pi (n + 1) X x))
    (f : C(I^(Fin (n + 1)), X))
    (h : C(unitInterval × Cube.boundary (Fin (n + 1)), X))
    (h0 : ∀ z : Cube.boundary (Fin (n + 1)), h (0, z) = f z)
    (h1 : ∀ z : Cube.boundary (Fin (n + 1)), h (1, z) = x) :
    ∃ H : f.Homotopy (ContinuousMap.const _ x),
      ∀ (t : unitInterval) (z : Cube.boundary (Fin (n + 1))),
        H (t, z) = h (t, z) := by
  obtain ⟨F, hF0, hFB⟩ := exists_cube_homotopy_extension f h h0
  let r : GenLoop (Fin (n + 1)) X x :=
    ⟨⟨fun z => F (1, z), F.continuous.comp (continuous_const.prodMk continuous_id)⟩,
      fun z hz => (hFB 1 ⟨z, hz⟩).trans (h1 ⟨z, hz⟩)⟩
  let H : f.Homotopy r.val := {
    toContinuousMap := F
    map_zero_left := hF0
    map_one_left := fun _ => rfl
  }
  obtain ⟨L⟩ : GenLoop.Homotopic r (GenLoop.const : GenLoop (Fin (n + 1)) X x) :=
    Quotient.exact (hpi.elim (⟦r⟧ : HomotopyGroup.Pi (n + 1) X x) ⟦GenLoop.const⟧)
  let G : f.Homotopy (ContinuousMap.const _ x) := H.trans L.toHomotopy
  have hclosed : IsClosed (Cube.boundary (Fin (n + 1))) := by
    simp only [Cube.boundary, ofPred_exists, ofPred_or]
    exact isClosed_iUnion_of_finite fun i =>
      (isClosed_eq (continuous_apply i) continuous_const).union
        (isClosed_eq (continuous_apply i) continuous_const)
  let : LocallyCompactSpace (Cube.boundary (Fin (n + 1))) := hclosed.locallyCompactSpace
  let gamma : Path (f.restrict (Cube.boundary (Fin (n + 1))))
      (ContinuousMap.const (Cube.boundary (Fin (n + 1))) x) := {
    toContinuousMap := h.curry
    source' := by
      ext z
      exact h0 z
    target' := by
      ext z
      exact h1 z
  }
  have hconcat (t : unitInterval) (z : Cube.boundary (Fin (n + 1))) :
      G (t, z) = (gamma.trans (Path.refl _)) t z := by
    change (H.trans L.toHomotopy) (t, z) = (gamma.trans (Path.refl _)) t z
    rw [ContinuousMap.Homotopy.trans_apply, Path.trans_apply]
    split_ifs
    · exact hFB _ z
    · exact (L.eq_fst _ z.property).trans (GenLoop.boundary r z z.property)
  let P := Path.Homotopy.transRefl gamma
  let K : C(unitInterval × (unitInterval × Cube.boundary (Fin (n + 1))), X) :=
    ⟨fun z => P (z.1, z.2.1) z.2.2,
      (P.continuous.comp (continuous_fst.prodMk
        (continuous_fst.comp continuous_snd))).eval (continuous_snd.comp continuous_snd)⟩
  have hK0 (t : unitInterval) (z : Cube.boundary (Fin (n + 1))) :
      K (0, (t, z)) = G (t, z) :=
    (congrArg (fun a : C(Cube.boundary (Fin (n + 1)), X) => a z)
      (P.apply_zero t)).trans (hconcat t z).symm
  have hKL (s : unitInterval) (z : Cube.boundary (Fin (n + 1))) :
      K (s, (0, z)) = f z :=
    congrArg (fun a : C(Cube.boundary (Fin (n + 1)), X) => a z) (P.source s)
  have hKR (s : unitInterval) (z : Cube.boundary (Fin (n + 1))) :
      K (s, (1, z)) = (ContinuousMap.const _ x) z :=
    congrArg (fun a : C(Cube.boundary (Fin (n + 1)), X) => a z) (P.target s)
  obtain ⟨H', hH'⟩ := exists_cube_homotopy_of_boundary_homotopy f
    (ContinuousMap.const _ x) G K hK0 hKL hKR
  refine ⟨H', fun t z => (hH' t z).trans ?_⟩
  exact congrArg (fun a : C(Cube.boundary (Fin (n + 1)), X) => a z) (P.apply_one t)

end PoincareConjecture.Proofs.M02
