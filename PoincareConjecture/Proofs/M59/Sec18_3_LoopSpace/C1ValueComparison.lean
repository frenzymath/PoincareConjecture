import PoincareConjecture.Proofs.M59.Sec18_3_LoopSpace.C1HomotopyLifting
import PoincareConjecture.Proofs.M59.Mathlib.CubicalPostcomposition









set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology unitInterval

universe u

namespace PoincareConjecture

open Proofs.M02 Proofs.M59

variable {M : Type u} [MetricSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]



theorem m59_continuous_loop_cube_has_c1_representative
    (hcompact : IsCompact (univ : Set M)) (n : Nat) (x : M)
    (F : GenLoop (Fin n) C(LoopCircle, M) (ContinuousMap.const LoopCircle x)) :
    ∃ G : GenLoop (Fin n) (C1FreeLoopSpace (M := M)) (constantC1Loop x),
      GenLoop.Homotopic F (mapGenLoop Proofs.M58.loopValues rfl G) := by
  let : CompactSpace M := isCompact_univ_iff.mp hcompact
  obtain ⟨C, U, hU, hdiag, h0, h1, hfix, hC⟩ :=
    Proofs.M58.exists_local_contraction (𝓡 3) hcompact 1
  obtain ⟨epsilon, he, hnear⟩ := isCompact_diagonal.exists_thickening_subset_open hU hdiag
  obtain ⟨G, hG, hGc⟩ := m59_cube_loop_approximation n F.val.uncurry x he
  have hGF (v : Fin n → I) (z : LoopCircle) : (G v z, F v z) ∈ U := by
    apply hnear
    apply Metric.mem_thickening_iff.mpr
    refine ⟨(F v z, F v z), rfl, ?_⟩
    have hh : dist (G v z) (F v z) < epsilon := hG v z
    simpa only [Prod.dist_eq, dist_self, max_eq_left (dist_nonneg)] using hh
  have hGb (v : Fin n → I) (hv : v ∈ Cube.boundary (Fin n)) :
      G v = constantC1Loop x := by
    apply hGc
    intro z
    change F v z = x
    rw [GenLoop.boundary F v hv]
    rfl
  let G' : GenLoop (Fin n) (C1FreeLoopSpace (M := M)) (constantC1Loop x) := ⟨G, hGb⟩
  let D : C((I × (Fin n → I)) × LoopCircle, ℝ × (M × M)) :=
    ⟨fun v => (v.1.1, G v.1.2 v.2, F v.1.2 v.2),
      (continuous_subtype_val.comp (continuous_fst.comp continuous_fst)).prodMk
        ((Proofs.M58.continuous_loop_eval.comp
          ((G.continuous.comp (continuous_snd.comp continuous_fst)).prodMk continuous_snd)).prodMk
          (by fun_prop))⟩
  have hCD : Continuous (fun v => C (D v)) := continuous_iff_continuousAt.mpr fun v =>
    (hC (D v) ⟨v.1.1.property, hGF v.1.2 v.2⟩).continuousAt.comp D.continuous.continuousAt
  let J : C(I × (Fin n → I), C(LoopCircle, M)) := (⟨fun v => C (D v), hCD⟩ : C(_, M)).curry
  refine ⟨G', ⟨{ toContinuousMap := J, map_zero_left := ?_, map_one_left := ?_, prop' := ?_ }⟩⟩
  · intro v
    ext z
    exact h0 _ _
  · intro v
    ext z
    exact h1 _ (hGF v z)
  · intro t v hv
    ext z
    change C (t, G v z, F v z) = F v z
    rw [hGb v hv, GenLoop.boundary F v hv]
    exact hfix t x



theorem m59_loopValues_homotopyGroupMap_injective
    (hcompact : IsCompact (univ : Set M)) (n : Nat) (x : M) :
    Function.Injective (homotopyGroupMap (Fin n) Proofs.M58.loopValues
      (rfl : Proofs.M58.loopValues (constantC1Loop x) = ContinuousMap.const LoopCircle x)) := by
  intro a b
  refine Quotient.inductionOn₂ a b ?_
  intro F G h
  have hFG : GenLoop.Homotopic (mapGenLoop Proofs.M58.loopValues rfl F)
      (mapGenLoop Proofs.M58.loopValues rfl G) := Quotient.exact h
  obtain ⟨H⟩ := hFG
  let J : C(I × ((Fin n → I) × LoopCircle), M) :=
    ⟨fun v => H (v.1, v.2.1) v.2.2, by fun_prop⟩
  apply Quotient.sound
  exact m59_genLoop_homotopic_of_value_homotopy hcompact n x F G J
    (fun v z => congrArg (fun f : C(LoopCircle, M) => f z) (H.apply_zero v))
    (fun v z => congrArg (fun f : C(LoopCircle, M) => f z) (H.apply_one v))
    (fun t v hv z =>
      (congrArg (fun f : C(LoopCircle, M) => f z) (H.eq_fst t hv)).trans
        (congrArg (fun gamma : C1FreeLoopSpace (M := M) => gamma z) (GenLoop.boundary F v hv)))



theorem m59_loopValues_homotopyGroupMap_surjective
    (hcompact : IsCompact (univ : Set M)) (n : Nat) (x : M) :
    Function.Surjective (homotopyGroupMap (Fin n) Proofs.M58.loopValues
      (rfl : Proofs.M58.loopValues (constantC1Loop x) = ContinuousMap.const LoopCircle x)) := by
  intro a
  refine Quotient.inductionOn a ?_
  intro F
  obtain ⟨G, h⟩ := m59_continuous_loop_cube_has_c1_representative hcompact n x F
  exact ⟨⟦G⟧, Quotient.sound h.symm⟩



noncomputable def m59C1ValueEquiv
    (hcompact : IsCompact (univ : Set M)) (n : Nat) [Nonempty (Fin n)] (x : M) :
    HomotopyGroup.Pi n (C1FreeLoopSpace (M := M)) (constantC1Loop x) ≃*
      HomotopyGroup.Pi n C(LoopCircle, M) (ContinuousMap.const LoopCircle x) :=
  MulEquiv.ofBijective (homotopyGroupMapHom (N := Fin n) Proofs.M58.loopValues rfl)
    ⟨m59_loopValues_homotopyGroupMap_injective hcompact n x,
      m59_loopValues_homotopyGroupMap_surjective hcompact n x⟩

end PoincareConjecture
