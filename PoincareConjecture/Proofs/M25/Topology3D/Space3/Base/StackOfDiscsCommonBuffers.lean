import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.LowerEndTubePrimitives
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Tactic.FinCases











set_option autoImplicit false

open Set Metric

namespace PoincareConjecture.M25.Topology3D



theorem exists_stackCommonDiscBuffers
    (U V : Fin 2 -> OpenPartialHomeomorph (E2 × ℝ) E3)
    (s tau : ℝ) (htau : 0 < tau)
    (hUs : ∀ i, closedBall (0 : E2) 1 ×ˢ ({s} : Set ℝ) ⊆ (U i).source)
    (hVs : ∀ i, closedBall (0 : E2) 1 ×ˢ ({s} : Set ℝ) ⊆ (V i).source)
    (hsame : ∀ i,
      U i '' (closedBall (0 : E2) 1 ×ˢ ({s} : Set ℝ)) =
        V i '' (closedBall (0 : E2) 1 ×ˢ ({s} : Set ℝ)))
    (hdis : Disjoint
      (U 0 '' (closedBall (0 : E2) 1 ×ˢ ({s} : Set ℝ)))
      (U 1 '' (closedBall (0 : E2) 1 ×ˢ ({s} : Set ℝ))))
    (W : Fin 2 -> Set E3) (hW : ∀ i, IsOpen (W i))
    (hUW : ∀ i, U i '' (closedBall (0 : E2) 1 ×ˢ ({s} : Set ℝ)) ⊆ W i) :
    ∃ (r delta : ℝ) (O : Fin 2 -> Set E3),
      1 < r ∧ 0 < delta ∧ delta < tau ∧
      (∀ i, IsOpen (O i) ∧ O i ⊆ W i) ∧ Disjoint (O 0) (O 1) ∧
      ∀ i,
        closedBall (0 : E2) r ×ˢ Icc (s - delta) (s + delta) ⊆ (U i).source ∧
        closedBall (0 : E2) r ×ˢ Icc (s - delta) (s + delta) ⊆ (V i).source ∧
        U i '' (closedBall (0 : E2) r ×ˢ Icc (s - delta) (s + delta)) ⊆ O i ∧
        V i '' (closedBall (0 : E2) r ×ˢ Icc (s - delta) (s + delta)) ⊆ O i := by
  let C : Set (E2 × ℝ) := closedBall (0 : E2) 1 ×ˢ ({s} : Set ℝ)
  have hC : IsCompact C := (isCompact_closedBall (0 : E2) 1).prod isCompact_singleton
  have hUC (i : Fin 2) : IsCompact (U i '' C) :=
    hC.image_of_continuousOn ((U i).continuousOn.mono (hUs i))
  obtain ⟨O0, O1, hO0, hO1, hU0, hU1, hOdis⟩ :=
    SeparatedNhds.of_isCompact_isCompact (hUC 0) (hUC 1) hdis
  let A : Fin 2 -> Set E3 := ![O0, O1]
  let O : Fin 2 -> Set E3 := fun i => A i ∩ W i
  have hA (i : Fin 2) : IsOpen (A i) := by fin_cases i <;> assumption
  have hUA (i : Fin 2) : U i '' C ⊆ A i := by fin_cases i <;> assumption
  have hO (i : Fin 2) : IsOpen (O i) := (hA i).inter (hW i)
  have hUO (i : Fin 2) : U i '' C ⊆ O i := fun _ hy => ⟨hUA i hy, hUW i hy⟩
  have hVO (i : Fin 2) : V i '' C ⊆ O i := by
    change V i '' (closedBall (0 : E2) 1 ×ˢ ({s} : Set ℝ)) ⊆ O i
    rw [← hsame i]
    exact hUO i
  let Z : Fin 2 -> Set (E2 × ℝ) := fun i =>
    ((U i).source ∩ (U i) ⁻¹' O i) ∩ ((V i).source ∩ (V i) ⁻¹' O i)
  have hZ (i : Fin 2) : IsOpen (Z i) :=
    ((U i).isOpen_inter_preimage (hO i)).inter ((V i).isOpen_inter_preimage (hO i))
  have hCZ (i : Fin 2) : C ⊆ Z i := fun p hp =>
    ⟨⟨hUs i hp, hUO i ⟨p, hp, rfl⟩⟩, ⟨hVs i hp, hVO i ⟨p, hp, rfl⟩⟩⟩
  let Zall := Z 0 ∩ Z 1
  have hZall : IsOpen Zall := (hZ 0).inter (hZ 1)
  have hCZall : C ⊆ Zall := fun _ hp => ⟨hCZ 0 hp, hCZ 1 hp⟩
  obtain ⟨X, J, _hX, hJ, hDX, hsJ, hXJ⟩ :=
    generalized_tube_lemma (isCompact_closedBall (0 : E2) 1)
      isCompact_singleton hZall hCZall
  obtain ⟨d, hd, hdJ⟩ := Metric.isOpen_iff.mp hJ s (hsJ (mem_singleton s))
  let delta := min tau d / 2
  have hdelta : 0 < delta := div_pos (lt_min htau hd) (by norm_num)
  have hdeltaTau : delta < tau := by
    dsimp only [delta]
    linarith only [min_le_left tau d, htau]
  have hdeltaD : delta < d := by
    dsimp only [delta]
    linarith only [min_le_right tau d, hd]
  have hband : closedBall (0 : E2) 1 ×ˢ Icc (s - delta) (s + delta) ⊆ Zall := by
    intro p hp
    apply hXJ
    refine ⟨hDX hp.1, hdJ ?_⟩
    rw [mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith only [hp.2.1, hp.2.2, hdeltaD]
  obtain ⟨r0, hr0, hrZ⟩ := exists_saddle_end_disc_buffer
    (Icc (s - delta) (s + delta)) isCompact_Icc Zall hZall hband
  let r := (1 + r0) / 2
  have hr : 1 < r := by dsimp only [r]; linarith only [hr0]
  have hrr0 : r < r0 := by dsimp only [r]; linarith only [hr0]
  have hclosed : closedBall (0 : E2) r ×ˢ Icc (s - delta) (s + delta) ⊆ Zall :=
    (prod_mono (closedBall_subset_ball hrr0) subset_rfl).trans hrZ
  have hZi (i : Fin 2) : Zall ⊆ Z i := by
    fin_cases i
    · exact inter_subset_left
    · exact inter_subset_right
  refine ⟨r, delta, O, hr, hdelta, hdeltaTau,
    (fun i => ⟨hO i, inter_subset_right⟩), ?_, ?_⟩
  · exact hOdis.mono inter_subset_left inter_subset_left
  · intro i
    have hmem := hclosed.trans (hZi i)
    refine ⟨(fun _ hp => (hmem hp).1.1), (fun _ hp => (hmem hp).2.1), ?_, ?_⟩
    · rintro _ ⟨p, hp, rfl⟩
      exact (hmem hp).1.2
    · rintro _ ⟨p, hp, rfl⟩
      exact (hmem hp).2.2

end PoincareConjecture.M25.Topology3D
