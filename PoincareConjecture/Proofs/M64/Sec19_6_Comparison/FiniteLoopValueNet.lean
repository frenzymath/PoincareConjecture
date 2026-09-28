import PoincareConjecture.Proofs.M60.Def18_17_FillingArea.LoopNeighborhoods
import PoincareConjecture.Proofs.M58.Cor18_28_PeriodicSpeed










set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture




theorem m64_finite_loop_value_net
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
    (g : RiemannianMetric 3 M)
    {Z : Type*} [TopologicalSpace Z] [CompactSpace Z]
    (Gamma : Z → C1FreeLoopSpace (M := M)) (hGamma : Continuous Gamma)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ k : ℕ, ∃ nodes : Fin k → Z, ∀ z : Z, ∃ i : Fin k,
      ∀ x : ℝ, g.edist (periodicFreeLoop (Gamma z) x)
        (periodicFreeLoop (Gamma (nodes i)) x) < ENNReal.ofReal epsilon := by
  classical
  have hnear (w : Z) := m60_exists_loop_close_neighborhood g (Gamma w) hepsilon
  choose U hU hself hclose using hnear
  let V : Z → Set Z := fun w => Gamma ⁻¹' U w
  have hV (w : Z) : IsOpen (V w) := (hU w).preimage hGamma
  obtain ⟨S, hS⟩ := isCompact_univ.elim_finite_subcover V hV
    (fun z _ => mem_iUnion.mpr ⟨z, hself z⟩)
  let e : Fin (Fintype.card S) ≃ S := (Fintype.equivFin S).symm
  refine ⟨Fintype.card S, fun i => (e i).val, ?_⟩
  intro z
  obtain ⟨w, hwS, hzw⟩ := mem_iUnion₂.mp (hS (mem_univ z))
  refine ⟨e.symm ⟨w, hwS⟩, ?_⟩
  intro x
  simp only [e.apply_symm_apply]
  let q : LoopCircle :=
    ⟨Proofs.M58.angularPoint x, Proofs.M58.norm_angularPoint x⟩
  have h := hclose w (Gamma z) hzw q
  rw [← (Gamma z).boundary q, ← (Gamma w).boundary q] at h
  exact h

end PoincareConjecture
