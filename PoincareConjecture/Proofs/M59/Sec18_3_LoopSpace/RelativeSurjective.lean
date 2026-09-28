import PoincareConjecture.Definitions.M59LoopIdentification
import PoincareConjecture.Proofs.M58.Sec18_4_LoopTopology
import PoincareConjecture.Proofs.M02.CubeHomotopyExtension










set_option autoImplicit false

open scoped Manifold ContDiff Topology unitInterval

noncomputable section

universe u

namespace PoincareConjecture



theorem m59_square_boundary_iff (z : Fin 2 → I) :
    z ∈ Cube.boundary (Fin 2) ↔
      z 0 = 0 ∨ z 0 = 1 ∨ z 1 = 0 ∨ z 1 = 1 := by
  constructor
  · rintro ⟨i, hi⟩
    fin_cases i
    · rcases hi with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr hi)
  · rintro (h | h | h | h)
    · exact ⟨0, Or.inl h⟩
    · exact ⟨0, Or.inr h⟩
    · exact ⟨1, Or.inl h⟩
    · exact ⟨1, Or.inr h⟩



def m59RelativeSquareShrink : C(I × (Fin 2 → I), Fin 2 → I) :=
  ⟨fun p i => if i = 0 then unitInterval.symm p.1 * p.2 0 else p.2 i, by
    apply continuous_pi
    intro i
    by_cases hi : i = 0
    · simp only [hi]
      exact (unitInterval.continuous_symm.comp continuous_fst).mul
        ((continuous_apply 0).comp continuous_snd)
    · simp only [hi, if_false]
      exact (continuous_apply i).comp continuous_snd⟩



theorem m59RelativeSquareShrink_zero (z : Fin 2 → I) :
    m59RelativeSquareShrink (0, z) = z := by
  ext i
  by_cases hi : i = 0 <;> simp [m59RelativeSquareShrink, hi]

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]



theorem m59RelativeLoopCubeAt_boundary {x : M}
    {F : C((Fin 2 → I), C1FreeLoopSpace (M := M))}
    (hF : M59RelativeLoopCubeAt x F) (z : Cube.boundary (Fin 2)) :
    ∃ p : M, F z = constantC1Loop p := by
  rcases (m59_square_boundary_iff z).mp z.property with h | h | h | h
  · exact ⟨x, hF.1 z (Or.inl h)⟩
  · exact hF.2 z h
  · exact ⟨x, hF.1 z (Or.inr (Or.inl h))⟩
  · exact ⟨x, hF.1 z (Or.inr (Or.inr h))⟩




theorem m59_relative_surjective (z0 : LoopCircle) (x : M)
    (F : C((Fin 2 → I), C1FreeLoopSpace (M := M)))
    (hF : M59RelativeLoopCubeAt x F) :
    ∃ gamma : GenLoop (Fin 2) (C1FreeLoopSpace (M := M)) (constantC1Loop x),
      ContinuousMap.HomotopicWith F gamma.val (M59RelativeLoopCubeAt x) := by
  let K : C(I × Cube.boundary (Fin 2), C1FreeLoopSpace (M := M)) :=
    (Proofs.M58.constantLoopMap.comp ((Proofs.M58.loopEvaluation z0).comp
      (F.comp m59RelativeSquareShrink))).comp
      ⟨fun p => (p.1, p.2.val), continuous_fst.prodMk continuous_snd.subtype_val⟩
  have hK0 (z : Cube.boundary (Fin 2)) : K (0, z) = F z := by
    change constantC1Loop (F (m59RelativeSquareShrink (0, z.val)) z0) = F z
    rw [m59RelativeSquareShrink_zero]
    obtain ⟨p, hp⟩ := m59RelativeLoopCubeAt_boundary hF z
    rw [hp]
    rfl
  have hKfixed (t : I) (z : Cube.boundary (Fin 2))
      (hz : z.val 0 = 0 ∨ z.val 1 = 0 ∨ z.val 1 = 1) :
      K (t, z) = constantC1Loop x := by
    change constantC1Loop (F (m59RelativeSquareShrink (t, z.val)) z0) = _
    have hshrink : (m59RelativeSquareShrink (t, z.val)) 0 = 0 ∨
        (m59RelativeSquareShrink (t, z.val)) 1 = 0 ∨
        (m59RelativeSquareShrink (t, z.val)) 1 = 1 := by
      rcases hz with hz | hz | hz
      · exact Or.inl (by simp [m59RelativeSquareShrink, hz])
      · exact Or.inr (Or.inl (by simpa [m59RelativeSquareShrink] using hz))
      · exact Or.inr (Or.inr (by simpa [m59RelativeSquareShrink] using hz))
    rw [hF.1 _ hshrink]
    rfl
  have hK1 (z : Cube.boundary (Fin 2)) : K (1, z) = constantC1Loop x := by
    change constantC1Loop (F (m59RelativeSquareShrink (1, z.val)) z0) = _
    rw [hF.1 _ (Or.inl (by simp [m59RelativeSquareShrink]))]
    rfl
  obtain ⟨G, hG0, hGB⟩ := Proofs.M02.exists_cube_homotopy_extension F K hK0
  let gamma : GenLoop (Fin 2) (C1FreeLoopSpace (M := M)) (constantC1Loop x) :=
    ⟨⟨fun z => G (1, z), G.continuous.comp (continuous_const.prodMk continuous_id)⟩,
      fun z hz => (hGB 1 ⟨z, hz⟩).trans (hK1 ⟨z, hz⟩)⟩
  refine ⟨gamma, ⟨{
    toContinuousMap := G
    map_zero_left := hG0
    map_one_left := fun _ => rfl
    prop' := ?_ }⟩⟩
  intro t
  constructor
  · intro z hz
    have hzB : z ∈ Cube.boundary (Fin 2) := by
      rcases hz with h | h | h
      · exact ⟨0, Or.inl h⟩
      · exact ⟨1, Or.inl h⟩
      · exact ⟨1, Or.inr h⟩
    exact (hGB t ⟨z, hzB⟩).trans (hKfixed t ⟨z, hzB⟩ hz)
  · intro z hz
    refine ⟨F (m59RelativeSquareShrink (t, z)) z0, ?_⟩
    exact hGB t ⟨z, ⟨0, Or.inr hz⟩⟩

end PoincareConjecture
