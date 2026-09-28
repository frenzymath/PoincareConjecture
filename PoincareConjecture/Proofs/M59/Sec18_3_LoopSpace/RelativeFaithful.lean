import PoincareConjecture.Proofs.M59.Sec18_3_LoopSpace.RelativeSurjective
import PoincareConjecture.Proofs.M02.CubeBoundaryAdjustment










set_option autoImplicit false

open scoped Manifold ContDiff Topology unitInterval

noncomputable section

universe u

namespace PoincareConjecture



def m59SquareRightEdge : C(I, Fin 2 → I) :=
  ⟨fun t i => if i = 0 then 1 else t, by
    apply continuous_pi
    intro i
    by_cases hi : i = 0 <;> simp only [hi, if_true, if_false]
    · exact continuous_const
    · exact continuous_id⟩



theorem m59RelativeLoopCubeAt_of_genLoop
    {M : Type u} [TopologicalSpace M] [ChartedSpace LoopAmbient M]
    [IsManifold (𝓡 3) ∞ M] {x : M}
    (gamma : GenLoop (Fin 2) (C1FreeLoopSpace (M := M)) (constantC1Loop x)) :
    M59RelativeLoopCubeAt x gamma.val := by
  constructor
  · intro z hz
    apply GenLoop.boundary gamma z
    rcases hz with h | h | h
    · exact ⟨0, Or.inl h⟩
    · exact ⟨1, Or.inl h⟩
    · exact ⟨1, Or.inr h⟩
  · intro z hz
    exact ⟨x, GenLoop.boundary gamma z ⟨0, Or.inr hz⟩⟩

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]



theorem m59_relative_homotopy_of_based {x : M}
    {gamma delta : GenLoop (Fin 2) (C1FreeLoopSpace (M := M)) (constantC1Loop x)}
    (h : GenLoop.Homotopic gamma delta) :
    ContinuousMap.HomotopicWith gamma.val delta.val (M59RelativeLoopCubeAt x) := by
  obtain ⟨H⟩ := h
  refine ⟨{ toHomotopy := H.toHomotopy, prop' := ?_ }⟩
  intro t
  exact m59RelativeLoopCubeAt_of_genLoop
    ⟨H.toHomotopy.curry t, fun z hz => (H.eq_fst t hz).trans (GenLoop.boundary gamma z hz)⟩




theorem m59_relative_faithful (z0 : LoopCircle) (x : M)
    (hpi : Subsingleton (HomotopyGroup.Pi 2 M x))
    (gamma delta : GenLoop (Fin 2) (C1FreeLoopSpace (M := M)) (constantC1Loop x)) :
    ContinuousMap.HomotopicWith gamma.val delta.val (M59RelativeLoopCubeAt x) ↔
      GenLoop.Homotopic gamma delta := by
  refine ⟨?_, m59_relative_homotopy_of_based⟩
  rintro ⟨H⟩
  let B : C((Fin 2 → I), M) := (Proofs.M58.loopEvaluation z0).comp
    (H.toContinuousMap.comp
      ⟨fun z => (z 0, m59SquareRightEdge (z 1)), by fun_prop⟩)
  have hB (z : Fin 2 → I) (hz : z ∈ Cube.boundary (Fin 2)) : B z = x := by
    change H (z 0, m59SquareRightEdge (z 1)) z0 = x
    rcases (m59_square_boundary_iff z).mp hz with h | h | h | h
    · rw [h, H.apply_zero]
      exact congrArg (fun g : C1FreeLoopSpace (M := M) => g z0)
        (GenLoop.boundary gamma (m59SquareRightEdge (z 1)) ⟨0, Or.inr rfl⟩)
    · rw [h, H.apply_one]
      exact congrArg (fun g : C1FreeLoopSpace (M := M) => g z0)
        (GenLoop.boundary delta (m59SquareRightEdge (z 1)) ⟨0, Or.inr rfl⟩)
    · have he := (H.prop (z 0)).1 (m59SquareRightEdge (z 1))
        (Or.inr (Or.inl (by simpa [m59SquareRightEdge] using h)))
      change H (z 0, m59SquareRightEdge (z 1)) = _ at he
      rw [he]
      rfl
    · have he := (H.prop (z 0)).1 (m59SquareRightEdge (z 1))
        (Or.inr (Or.inr (by simpa [m59SquareRightEdge] using h)))
      change H (z 0, m59SquareRightEdge (z 1)) = _ at he
      rw [he]
      rfl
  let b : GenLoop (Fin 2) M x := ⟨B, hB⟩
  obtain ⟨J⟩ : GenLoop.Homotopic b GenLoop.const :=
    Quotient.exact (hpi.elim (⟦b⟧ : HomotopyGroup.Pi 2 M x) ⟦GenLoop.const⟧)
  let pair : C(I × I, Fin 2 → I) :=
    ⟨fun p i => if i = 0 then p.1 else p.2, by
      apply continuous_pi
      intro i
      by_cases hi : i = 0 <;> simp only [hi, if_true, if_false]
      · exact continuous_fst
      · exact continuous_snd⟩
  have hJboundary (s : I) (v : Fin 2 → I) (hv : v ∈ Cube.boundary (Fin 2)) :
      J (s, v) = x := (J.eq_fst s hv).trans (GenLoop.boundary b v hv)
  let K : C(I × (I × Cube.boundary (Fin 2)), C1FreeLoopSpace (M := M)) :=
    Proofs.M58.constantLoopMap.comp (J.toContinuousMap.comp
      ⟨fun p => (unitInterval.symm (p.2.2.val 0 * unitInterval.symm p.1),
        pair (p.2.1, p.2.2.val 1)), by
        exact (unitInterval.continuous_symm.comp
          (((continuous_apply 0).comp
            (continuous_subtype_val.comp (continuous_snd.comp continuous_snd))).mul
            (unitInterval.continuous_symm.comp continuous_fst))).prodMk
          (pair.continuous.comp ((continuous_fst.comp continuous_snd).prodMk
            ((continuous_apply 1).comp
              (continuous_subtype_val.comp (continuous_snd.comp continuous_snd)))))⟩)
  have hK0 (t : I) (z : Cube.boundary (Fin 2)) : K (0, (t, z)) = H (t, z) := by
    change constantC1Loop (J (unitInterval.symm (z.val 0 * unitInterval.symm 0),
      pair (t, z.val 1))) = H (t, z)
    rcases (m59_square_boundary_iff z).mp z.property with h | h | h | h
    · simp only [h, zero_mul, unitInterval.symm_zero, J.apply_one]
      exact ((H.prop t).1 z (Or.inl h)).symm
    · simp only [h, one_mul, unitInterval.symm_symm, J.apply_zero]
      change constantC1Loop (H (t, m59SquareRightEdge (z.val 1)) z0) = H (t, z)
      have hz : m59SquareRightEdge (z.val 1) = z.val := by
        funext i
        fin_cases i
        · exact h.symm
        · rfl
      rw [hz]
      obtain ⟨p, hp⟩ := (H.prop t).2 z h
      change H (t, z) = constantC1Loop p at hp
      rw [hp]
      rfl
    · rw [hJboundary _ _ ⟨1, Or.inl (by simpa [pair] using h)⟩]
      exact ((H.prop t).1 z (Or.inr (Or.inl h))).symm
    · rw [hJboundary _ _ ⟨1, Or.inr (by simpa [pair] using h)⟩]
      exact ((H.prop t).1 z (Or.inr (Or.inr h))).symm
  have hKL (s : I) (z : Cube.boundary (Fin 2)) : K (s, (0, z)) = gamma.val z := by
    change constantC1Loop (J (_, pair (0, z.val 1))) = gamma.val z
    rw [hJboundary _ _ ⟨0, Or.inl (by simp [pair])⟩]
    exact (GenLoop.boundary gamma z z.property).symm
  have hKR (s : I) (z : Cube.boundary (Fin 2)) : K (s, (1, z)) = delta.val z := by
    change constantC1Loop (J (_, pair (1, z.val 1))) = delta.val z
    rw [hJboundary _ _ ⟨0, Or.inr (by simp [pair])⟩]
    exact (GenLoop.boundary delta z z.property).symm
  have hK1 (t : I) (z : Cube.boundary (Fin 2)) : K (1, (t, z)) = constantC1Loop x := by
    change constantC1Loop (J (unitInterval.symm (z.val 0 * unitInterval.symm 1), _)) = _
    simp only [unitInterval.symm_one, mul_zero, unitInterval.symm_zero, J.apply_one]
    rfl
  obtain ⟨H', hH'⟩ := Proofs.M02.exists_cube_homotopy_of_boundary_homotopy
    gamma.val delta.val H.toHomotopy K hK0 hKL hKR
  exact ⟨{ toHomotopy := H', prop' := fun t z hz =>
    (hH' t ⟨z, hz⟩).trans ((hK1 t ⟨z, hz⟩).trans (GenLoop.boundary gamma z hz).symm) }⟩

end PoincareConjecture
