import PoincareConjecture.Proofs.Horizon.Topology.Homotopy.Hurewicz.HurewiczMap

set_option autoImplicit false

open CategoryTheory Set Topology
open scoped Simplicial unitInterval

universe w

namespace Poincare.Topology

theorem stdSimplex_face_map_range (n : ℕ) (i : Fin (n + 2)) :
    range (stdSimplex.map (S := ℝ) i.succAbove) =
      Set.ofPred (fun y : stdSimplex ℝ (Fin (n + 2)) => y i = 0) := by
  classical
  have hzero (z : stdSimplex ℝ (Fin (n + 1))) :
      stdSimplex.map i.succAbove z i = 0 := by
    change FunOnFinite.linearMap ℝ ℝ i.succAbove z i = 0
    simp [FunOnFinite.linearMap_apply_apply, Fin.succAbove_ne]
  ext y
  constructor
  · rintro ⟨z, rfl⟩
    exact hzero z
  · intro hy
    change y i = 0 at hy
    have hsum : ∑ j : Fin (n + 1), y (i.succAbove j) = 1 := by
      have hs := Fin.sum_univ_succAbove (fun j => y j) i
      simpa only [stdSimplex.sum_eq_one, hy, zero_add] using hs.symm
    let z : stdSimplex ℝ (Fin (n + 1)) :=
      ⟨fun j => y (i.succAbove j), fun j => y.property.1 _, hsum⟩
    refine ⟨z, ?_⟩
    apply stdSimplex.ext
    funext j
    rcases Fin.eq_self_or_eq_succAbove i j with rfl | ⟨k, rfl⟩
    · exact (hzero z).trans hy.symm
    · change FunOnFinite.linearMap ℝ ℝ i.succAbove z (i.succAbove k) = y _
      rw [FunOnFinite.linearMap_apply_apply]
      have hfilter : Finset.univ.filter (fun j => i.succAbove j = i.succAbove k) = {k} := by
        ext j
        simp
      rw [hfilter, Finset.sum_singleton]
      rfl

theorem singularSimplex_constant_faces_iff_boundary (X : TopCat.{w}) (n : ℕ)
    (s : (TopCat.toSSet.obj X) _⦋n + 1⦌) (x : X) :
    (∀ i : Fin (n + 2), (TopCat.toSSet.obj X).δ i s = singularConstantSimplex X n x) ↔
      ∀ y : stdSimplex ℝ (Fin (n + 2)), (∃ i, y i = 0) → X.toSSetObjEquiv _ s y = x := by
  constructor
  · intro hface y hy
    obtain ⟨i, hi⟩ := hy
    have hy' : y ∈ range (stdSimplex.map (S := ℝ) i.succAbove) := by
      rw [stdSimplex_face_map_range]
      exact hi
    obtain ⟨z, rfl⟩ := hy'
    have h := congrArg (fun u => X.toSSetObjEquiv (Opposite.op ⦋n⦌) u z) (hface i)
    simpa only [TopCat.toSSetObjEquiv_δ_apply, singularConstantSimplex,
      Equiv.apply_symm_apply, ContinuousMap.const_apply] using h
  · intro hboundary i
    apply (X.toSSetObjEquiv _).injective
    ext z
    simp only [TopCat.toSSetObjEquiv_δ_apply, singularConstantSimplex,
      Equiv.apply_symm_apply, ContinuousMap.const_apply]
    apply hboundary _
    refine ⟨i, ?_⟩
    have hz : stdSimplex.map i.succAbove z ∈ range (stdSimplex.map (S := ℝ) i.succAbove) :=
      mem_range_self z
    rw [stdSimplex_face_map_range] at hz
    exact hz

theorem exists_genLoop_of_singularSimplex_constant_faces (X : TopCat.{w}) (n : ℕ)
    (s : (TopCat.toSSet.obj X) _⦋n + 1⦌) (x : X)
    (hface : ∀ i : Fin (n + 2), (TopCat.toSSet.obj X).δ i s = singularConstantSimplex X n x) :
    ∃ p : GenLoop (Fin (n + 1)) X x, genLoopSingularSimplex X p = s := by
  let e := Classical.choose (exists_stdSimplex_cube_pair_homeomorph (n + 1))
  have he (z : stdSimplex ℝ (Fin (n + 2))) :
      (∃ i, z i = 0) ↔ e z ∈ Cube.boundary (Fin (n + 1)) :=
    Classical.choose_spec (exists_stdSimplex_cube_pair_homeomorph (n + 1)) z
  let p : GenLoop (Fin (n + 1)) X x :=
    ⟨(X.toSSetObjEquiv _ s).comp ⟨e.symm, e.symm.continuous⟩, fun z hz => by
      apply (singularSimplex_constant_faces_iff_boundary X n s x).mp hface
      apply (he (e.symm z)).mpr
      simpa only [e.apply_symm_apply] using hz⟩
  refine ⟨p, ?_⟩
  apply (X.toSSetObjEquiv _).injective
  ext z
  simp only [genLoopSingularSimplex, Equiv.apply_symm_apply,
    ContinuousMap.comp_apply, ContinuousMap.coe_mk]
  change X.toSSetObjEquiv _ s (e.symm (e z)) = X.toSSetObjEquiv _ s z
  exact congrArg (X.toSSetObjEquiv _ s) (e.symm_apply_apply z)

theorem exists_genLoop_quotient_map (n : ℕ) {Q X : Type*}
    [TopologicalSpace Q] [TopologicalSpace X]
    (q : C(I^(Fin (n + 1)), Q)) (hq : IsQuotientMap q)
    (hfib : ∀ z w, q z = q w ↔ z = w ∨
      (z ∈ Cube.boundary (Fin (n + 1)) ∧ w ∈ Cube.boundary (Fin (n + 1))))
    {x : X} (p : GenLoop (Fin (n + 1)) X x) :
    ∃ f : C(Q, X), f.comp q = p.val ∧ f (q (fun _ => 0)) = x := by
  have hp : Function.FactorsThrough p.val q := by
    intro z w hzw
    rcases (hfib z w).mp hzw with hzw | ⟨hz, hw⟩
    · exact congrArg p hzw
    · exact (GenLoop.boundary p z hz).trans (GenLoop.boundary p w hw).symm
  let f := hq.lift p.val hp
  have hcomp : f.comp q = p.val := hq.lift_comp p.val hp
  refine ⟨f, hcomp, ?_⟩
  exact (ContinuousMap.congr_fun hcomp (fun _ => 0)).trans
    (GenLoop.boundary p (fun _ => 0) ⟨0, Or.inl rfl⟩)

end Poincare.Topology
