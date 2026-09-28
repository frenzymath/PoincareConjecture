import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Overlap.SliceAgreement
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Chain.Restriction








set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.DeepHorn


theorem image_eq_self_of_fixed_compl {M : Type*} [TopologicalSpace M]
    (e : M ≃ₜ M) {U : Set M} (hfix : ∀ x, x ∉ U → e x = x) : e '' U = U := by
  apply Subset.antisymm
  · rintro y ⟨x, hx, rfl⟩
    by_contra hn
    have he : e x = x := e.injective (hfix (e x) hn)
    exact hn (he.symm ▸ hx)
  · intro x hx
    refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
    by_contra hn
    have he := hfix (e.symm x) hn
    rw [e.apply_symm_apply] at he
    exact hn (he ▸ hx)

end PoincareConjecture.DeepHorn

namespace PoincareConjecture.BalancedNeckChain



theorem exists_central_sphere_transport_threshold :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        {g : RiemannianMetric 3 M} {ε : ℝ} (C : BalancedNeckChain g ε),
        ε ≤ ε₀ → ∀ i ∈ C.shape.active, ∀ j ∈ C.shape.active,
          ∃ (e : M ≃ₜ M) (K : Set M), IsCompact K ∧ K ⊆ C.unionOpen ∧
            (∀ x, x ∉ K → e x = x) ∧
            e '' (C.unionOpen : Set M) = C.unionOpen ∧
            e '' (C.neck i).central_sphere = (C.neck j).central_sphere := by
  obtain ⟨ε₀, hε₀, hsmall, hslice⟩ := EpsilonNeck.exists_contained_slice_compact_transport.{u}
  refine ⟨ε₀, hε₀, hsmall, ?_⟩
  intro M _ _ _ _ _ _ _ g ε C hε
  let R (i j : ℤ) : Prop :=
    ∃ (e : M ≃ₜ M) (K : Set M), IsCompact K ∧ K ⊆ C.unionOpen ∧
      (∀ x, x ∉ K → e x = x) ∧
      e '' (C.neck i).central_sphere = (C.neck j).central_sphere
  have hrefl (i : ℤ) : R i i :=
    ⟨Homeomorph.refl M, ∅, isCompact_empty, empty_subset _, fun _ _ => rfl, by simp⟩
  have hsymm {i j : ℤ} (h : R i j) : R j i := by
    obtain ⟨e, K, hK, hKU, hfix, hs⟩ := h
    refine ⟨e.symm, K, hK, hKU, ?_, ?_⟩
    · intro x hx
      exact (congrArg e.symm (hfix x hx)).symm.trans (e.symm_apply_apply x)
    · rw [← hs]
      exact e.symm_image_image _
  have htrans {i j k : ℤ} (hij : R i j) (hjk : R j k) : R i k := by
    obtain ⟨e, K, hK, hKU, hefix, he⟩ := hij
    obtain ⟨f, L, hL, hLU, hffix, hf⟩ := hjk
    refine ⟨e.trans f, K ∪ L, hK.union hL, union_subset hKU hLU, ?_, ?_⟩
    · intro x hx
      change f (e x) = x
      rw [hefix x (fun h => hx (Or.inl h)), hffix x (fun h => hx (Or.inr h))]
    · change (f ∘ e) '' (C.neck i).central_sphere = (C.neck k).central_sphere
      exact (Set.image_image (⇑f) (⇑e) _).symm.trans (by rw [he, hf])
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
    obtain ⟨e, K, hK, hKU, hfix, _, hs⟩ := hslice
      (C.neck (i + 1)) (C.neck i) (he'.symm ▸ hε) (he.symm ▸ hε) ha hmem
    exact ⟨e, K, hK, hKU.trans (union_subset (hsub _ hi') (hsub _ hi)), hfix, hs⟩
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
  obtain ⟨e, K, hK, hKU, hfix, hs⟩ := hR
  exact ⟨e, K, hK, hKU, hfix,
    DeepHorn.image_eq_self_of_fixed_compl e (fun x hx => hfix x (fun h => hx (hKU h))), hs⟩

end PoincareConjecture.BalancedNeckChain
