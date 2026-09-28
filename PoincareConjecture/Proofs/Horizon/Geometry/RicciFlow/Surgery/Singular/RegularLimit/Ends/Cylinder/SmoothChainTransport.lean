import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Ends.Cylinder.SmoothSliceTransport
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.DeepHorn.Limit.Separation.ChainTransport

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.BalancedNeckChain

theorem exists_central_sphere_smooth_transport_threshold :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        {g : RiemannianMetric 3 M} {ε : ℝ} (C : BalancedNeckChain g ε),
        ε ≤ ε₀ → ∀ i ∈ C.shape.active, ∀ j ∈ C.shape.active,
          ∃ (D : Diffeomorph (𝓡 3) (𝓡 3) M M ∞) (K : Set M),
            IsCompact K ∧ K ⊆ C.unionOpen ∧
            (∀ x, x ∉ K → D x = x) ∧
            D '' (C.unionOpen : Set M) = C.unionOpen ∧
            D '' (C.neck i).central_sphere = (C.neck j).central_sphere := by
  obtain ⟨ε₀, hε₀, hsmall, hslice⟩ := EpsilonNeck.exists_contained_slice_smooth_transport.{u}
  refine ⟨ε₀, hε₀, hsmall, ?_⟩
  intro M _ _ _ _ _ _ _ g ε C hε
  let R (i j : ℤ) : Prop :=
    ∃ (D : Diffeomorph (𝓡 3) (𝓡 3) M M ∞) (K : Set M),
      IsCompact K ∧ K ⊆ C.unionOpen ∧
      (∀ x, x ∉ K → D x = x) ∧
      D '' (C.neck i).central_sphere = (C.neck j).central_sphere
  have hrefl (i : ℤ) : R i i :=
    ⟨Diffeomorph.refl (𝓡 3) M ∞, ∅, isCompact_empty, empty_subset _, fun _ _ => rfl, by simp⟩
  have hsymm {i j : ℤ} (h : R i j) : R j i := by
    obtain ⟨D, K, hK, hKU, hfix, hs⟩ := h
    refine ⟨D.symm, K, hK, hKU, ?_, ?_⟩
    · intro x hx
      exact (congrArg D.symm (hfix x hx)).symm.trans (D.symm_apply_apply x)
    · rw [← hs]
      exact D.toEquiv.symm_image_image _
  have htrans {i j k : ℤ} (hij : R i j) (hjk : R j k) : R i k := by
    obtain ⟨D, K, hK, hKU, hDfix, hD⟩ := hij
    obtain ⟨F, L, hL, hLU, hFfix, hF⟩ := hjk
    refine ⟨D.trans F, K ∪ L, hK.union hL, union_subset hKU hLU, ?_, ?_⟩
    · intro x hx
      change F (D x) = x
      rw [hDfix x (fun h => hx (Or.inl h)), hFfix x (fun h => hx (Or.inr h))]
    · change (F ∘ D) '' (C.neck i).central_sphere = (C.neck k).central_sphere
      rw [image_comp, hD, hF]
  have hsub (i : ℤ) (hi : i ∈ C.shape.active) :
      (C.neck i).carrier ⊆ (C.unionOpen : Set M) :=
    fun x hx => mem_iUnion.mpr ⟨⟨i, hi⟩, hx⟩
  have hadj (i : ℤ) (hi : i ∈ C.shape.active) (hi' : i + 1 ∈ C.shape.active) :
      R i (i + 1) := by
    have he := C.epsilon_eq i hi
    have he' := C.epsilon_eq (i + 1) hi'
    have hiPos : 0 < ε⁻¹ := inv_pos.mpr (he ▸ (C.neck i).epsilon_pos)
    let a : ℝ := (3 / 4 : ℝ) * ε⁻¹
    have ha : a ∈ Ioo (-(C.neck i).epsilon⁻¹) (C.neck i).epsilon⁻¹ := by
      rw [he]
      dsimp [a]
      constructor <;> linarith
    have hmem (q : UnitTwoSphere) : (C.neck i).coordinate_map (q, a) ∈
        (C.neck (i + 1)).carrier := by
      apply (C.overlap_contains_quarters i hi hi').1
      refine ⟨(C.neck i).coordinate_map_mem ⟨mem_univ _, ha⟩, ?_⟩
      rw [(C.neck i).coordinate_inverse_coordinate_map ⟨mem_univ _, ha⟩]
      change a ∈ Ioo (ε⁻¹ / 2) ε⁻¹
      dsimp [a]
      constructor <;> linarith
    obtain ⟨D, K, hK, hKU, hfix, hs⟩ := hslice
      (C.neck (i + 1)) (C.neck i) (he'.symm ▸ hε) (he.symm ▸ hε) ha hmem
    exact ⟨D, K, hK, hKU.trans (union_subset (hsub _ hi') (hsub _ hi)), hfix, hs⟩
  have hle (i j : ℤ) (hi : i ∈ C.shape.active) (hj : j ∈ C.shape.active)
      (hij : i ≤ j) : R i j := by
    have hn : ∀ n : ℕ, i + (n : ℤ) ∈ C.shape.active → R i (i + (n : ℤ)) := by
      intro n
      induction n with
      | zero => simpa using fun _ => hrefl i
      | succ n ih =>
        intro hn
        have hmid : i + (n : ℤ) ∈ C.shape.active :=
          C.shape.ordConnected_active.out hi hn ⟨by omega, by omega⟩
        have hnext : i + (n : ℤ) + 1 ∈ C.shape.active := by simpa [add_assoc] using hn
        simpa only [Nat.cast_add, Nat.cast_one, add_assoc] using
          htrans (ih hmid) (hadj (i + (n : ℤ)) hmid hnext)
    have heq : i + ((j - i).toNat : ℤ) = j := by omega
    simpa only [heq] using hn (j - i).toNat (heq.symm ▸ hj)
  intro i hi j hj
  have hR : R i j := by
    obtain hij | hji := le_total i j
    · exact hle i j hi hj hij
    · exact hsymm (hle j i hj hi hji)
  obtain ⟨D, K, hK, hKU, hfix, hs⟩ := hR
  exact ⟨D, K, hK, hKU, hfix,
    DeepHorn.image_eq_self_of_fixed_compl D.toHomeomorph
      (fun x hx => hfix x (fun h => hx (hKU h))), hs⟩

end PoincareConjecture.BalancedNeckChain
