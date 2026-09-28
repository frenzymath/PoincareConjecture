import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Isotopy.Compact
import Mathlib.Geometry.Manifold.PartitionOfUnity



noncomputable section
set_option autoImplicit false

open Set Metric Filter
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies



theorem exists_velocity_agreeing_on_finite_disjoint_compacts
    {ι E F : Type*} [Finite ι] [NormedAddCommGroup E] [NormedSpace Real E]
    [FiniteDimensional Real E] [NormedAddCommGroup F] [NormedSpace Real F]
    (K : ι → Set E) (hK : ∀ i, IsCompact (K i))
    (hpair : Pairwise (fun i j => Disjoint (K i) (K j)))
    (V : ι → E → F) (hV : ∀ i, ContDiff Real ∞ (V i))
    (hVc : ∀ i, HasCompactSupport (V i)) :
    ∃ W : E → F, ContDiff Real ∞ W ∧ HasCompactSupport W ∧
      ∀ i x, x ∈ K i → W x = V i x := by
  classical
  let := Fintype.ofFinite ι
  have hcutoff (i : ι) : ∃ χ : E → Real, ContDiff Real ∞ χ ∧
      (∀ x ∈ K i, χ x = 1) ∧ ∀ j, j ≠ i → ∀ x ∈ K j, χ x = 0 := by
    let J := Finset.univ.erase i
    let O := ⋃ j ∈ J, K j
    have hO : IsClosed O := J.finite_toSet.isClosed_biUnion (fun j _ => (hK j).isClosed)
    have hdis : Disjoint O (K i) := by
      apply Set.disjoint_left.mpr
      intro x hx hxi
      obtain ⟨j, hj, hxj⟩ := mem_iUnion₂.mp hx
      exact Set.disjoint_left.mp (hpair (Finset.mem_erase.mp hj).1) hxj hxi
    obtain ⟨χ, hzero, hone, _⟩ := exists_contMDiffMap_zero_one_nhds_of_isClosed
      𝓘(Real, E) hO (hK i).isClosed hdis (n := ⊤)
    refine ⟨χ, χ.contMDiff.contDiff, fun x hx => hone.self_of_nhdsSet x hx, ?_⟩
    intro j hji x hx
    apply hzero.self_of_nhdsSet
    exact mem_iUnion_of_mem j (mem_iUnion_of_mem (Finset.mem_erase.mpr ⟨hji, Finset.mem_univ j⟩) hx)
  choose χ hχ hone hzero using hcutoff
  let W : E → F := fun x => ∑ i, χ i x • V i x
  refine ⟨W, ContDiff.sum (fun i _ => (hχ i).smul (hV i)), ?_, ?_⟩
  · have hfun : W = ∑ i, χ i • V i := by
      funext x
      simp only [W, Finset.sum_apply, Pi.smul_apply']
    rw [hfun]
    exact HasCompactSupport.finset_sum (fun i _ => (hVc i).smul_left)
  · intro j x hx
    dsimp only [W]
    rw [Finset.sum_eq_single j]
    · rw [hone j x hx, one_smul]
    · intro i _ hij
      rw [hzero i j hij.symm x hx, zero_smul]
    · simp

end Poincare.Manifold.Schoenflies
