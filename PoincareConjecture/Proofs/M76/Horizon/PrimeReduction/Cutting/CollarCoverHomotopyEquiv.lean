import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.ClosedCutCollarRetraction
import Mathlib.Topology.Homotopy.Equiv



set_option autoImplicit false
open Set
open scoped Topology

namespace PoincareConjecture.M76

theorem exists_collarCoverOuter_homotopyEquiv
    {X κ : Type*} [TopologicalSpace X] [Finite κ]
    {A : κ → Type*} [∀ i, TopologicalSpace (A i)]
    (R Q : Set X) (O : κ → Set X)
    (W : ∀ i, (A i × unitInterval) ≃ₜ closure (O i))
    (hQ : Q = R \ ⋃ i, O i) (hcQ : IsClosed Q)
    (hCR : ∀ i, closure (O i) ⊆ R)
    (hdis : Pairwise fun i j => Disjoint (closure (O i)) (closure (O j)))
    (hO : ∀ i z, (W i z : X) ∈ O i ↔ (0 : ℝ) < z.2 ∧ (z.2 : ℝ) < 1) :
    ∃ e : ContinuousMap.HomotopyEquiv (collarCoverOuter R W) Q,
      ∀ x : Q, ((e.invFun x).val : X) = x := by
  obtain ⟨F, hF0, hF1, hfix⟩ :=
    exists_collarCoverOuter_contraction R Q O W hQ hcQ hCR hdis hO
  have hQR : Q ⊆ R := hQ ▸ sdiff_subset
  let inc : C(Q, collarCoverOuter R W) :=
    ⟨fun x => ⟨⟨x, hQR x.property⟩,
      cut_subset_collarCoverOuter R O W hO ⟨x, hQR x.property⟩
        ((show (x : X) ∈ R \ ⋃ i, O i from hQ ▸ x.property).2)⟩,
      (continuous_subtype_val.subtype_mk _).subtype_mk _⟩
  let r : C(collarCoverOuter R W, Q) :=
    ⟨fun x => ⟨(F (1, x)).val, hF1 x⟩,
      (continuous_subtype_val.comp (continuous_subtype_val.comp
        (F.continuous.comp (continuous_const.prodMk continuous_id)))).subtype_mk _⟩
  have Hr : (ContinuousMap.id (collarCoverOuter R W)).Homotopy (inc.comp r) :=
    { toFun := F
      continuous_toFun := F.continuous
      map_zero_left := hF0
      map_one_left := fun x => rfl }
  have he : r.comp inc = ContinuousMap.id Q := by
    apply ContinuousMap.ext
    intro x
    apply Subtype.ext
    exact congrArg (fun y : collarCoverOuter R W => (y.val : X))
      (hfix 1 (inc x) x.property)
  refine ⟨{ toFun := r
            invFun := inc
            left_inv := ⟨Hr.symm⟩
            right_inv := ?_ }, fun _ => rfl⟩
  rw [he]

end PoincareConjecture.M76
