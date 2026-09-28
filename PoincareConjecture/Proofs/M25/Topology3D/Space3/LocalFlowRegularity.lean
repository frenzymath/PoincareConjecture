import PoincareConjecture.Proofs.M25.Topology3D.Space3.FlowAlgebra
import PoincareConjecture.Proofs.M09.LocalSmoothFlow

set_option autoImplicit false

open Set Filter Metric
open scoped ContDiff NNReal Topology

namespace PoincareConjecture.M25.Topology3D

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [FiniteDimensional ℝ E]
variable (f : E → E) {K L : ℝ≥0}
variable (hK : LipschitzWith K f) (hL : ∀ x, ‖f x‖ ≤ L)

theorem boundedFlow_local_smooth (hf : ContDiff ℝ ∞ f) (x : E) :
    ∃ (U : Set E) (d : ℝ), IsOpen U ∧ x ∈ U ∧ 0 < d ∧
      ContDiffOn ℝ ∞ (fun p : E × ℝ => boundedFlow f hK hL p.1 p.2)
        (U ×ˢ Ioo (-d) d) := by
  let fc : C(E, E) := ⟨f, hf.continuous⟩
  obtain ⟨α, U, d, hU, hx, hd, hα, hα0, hαode⟩ :=
    PoincareConjecture.Proofs.M09.exists_local_smooth_flow fc hf x
  have hzero : (0 : ℝ) ∈ Ioo (-d) d := by constructor <;> linarith
  have heq (y : E) (hy : y ∈ U) :
      EqOn (boundedFlow f hK hL y) (fun t => α (y, t)) (Ioo (-d) d) := by
    apply ODE_solution_unique_of_mem_Ioo
      (v := fun _ : ℝ => f) (s := fun _ => univ)
      (fun _ _ => hK.lipschitzOnWith) hzero
    · exact fun t _ => ⟨boundedFlow_hasDerivAt f hK hL y t, mem_univ _⟩
    · exact fun t ht => ⟨hαode y hy t ht, mem_univ _⟩
    · rw [boundedFlow_zero, hα0 y hy]
  exact ⟨U, d, hU, hx, hd, hα.congr (fun p hp => heq p.1 hp.1 hp.2)⟩

theorem boundedFlow_smooth_strip (hf : ContDiff ℝ ∞ f) (hs : HasCompactSupport f) :
    ∃ d > (0 : ℝ),
      ContDiffOn ℝ ∞ (fun p : E × ℝ => boundedFlow f hK hL p.1 p.2)
        (univ ×ˢ Ioo (-d) d) := by
  classical
  choose U d hU hx hd hF using boundedFlow_local_smooth f hK hL hf
  let W : Set (E × ℝ) := ⋃ x : E, U x ×ˢ Ioo (-d x) (d x)
  have hWo : IsOpen W := isOpen_iUnion fun x => (hU x).prod isOpen_Ioo
  have hWF : ContDiffOn ℝ ∞
      (fun p : E × ℝ => boundedFlow f hK hL p.1 p.2) W := by
    intro p hp
    obtain ⟨x, hpx⟩ := mem_iUnion.mp hp
    exact ((hF x).contDiffAt (((hU x).prod isOpen_Ioo).mem_nhds hpx)).contDiffWithinAt
  have hcover : tsupport f ×ˢ ({0} : Set ℝ) ⊆ W := by
    rintro ⟨x, t⟩ ⟨_, ht⟩
    have ht0 : t = 0 := mem_singleton_iff.mp ht
    subst t
    exact mem_iUnion.mpr ⟨x, hx x, by constructor <;> linarith [hd x]⟩
  obtain ⟨A, B, _, hB, hA, hzero, hAB⟩ :=
    generalized_tube_lemma hs.isCompact isCompact_singleton hWo hcover
  obtain ⟨r, hr, hrB⟩ :=
    Metric.mem_nhds_iff.mp (hB.mem_nhds (hzero (mem_singleton 0)))
  have hIB : Ioo (-r) r ⊆ B := by
    intro t ht
    apply hrB
    change dist t 0 < r
    rw [Real.dist_eq, sub_zero]
    exact abs_lt.mpr ht
  refine ⟨r, hr, fun p hp => ?_⟩
  by_cases hpk : p.1 ∈ tsupport f
  · have hpW : p ∈ W := hAB ⟨hA hpk, hIB hp.2⟩
    exact (hWF.contDiffAt (hWo.mem_nhds hpW)).contDiffWithinAt
  · have ho : IsOpen ((tsupport f)ᶜ ×ˢ (univ : Set ℝ)) :=
      (isClosed_tsupport f).isOpen_compl.prod isOpen_univ
    have heq : (fun q : E × ℝ => boundedFlow f hK hL q.1 q.2) =ᶠ[𝓝 p] Prod.fst :=
      Filter.eventuallyEq_of_mem (ho.mem_nhds ⟨hpk, mem_univ _⟩) fun q hq =>
        boundedFlow_eq_self f hK hL q.1 (image_eq_zero_of_notMem_tsupport hq.1) q.2
    exact (contDiffAt_fst.congr_of_eventuallyEq heq).contDiffWithinAt

end PoincareConjecture.M25.Topology3D
