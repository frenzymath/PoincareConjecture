import PoincareConjecture.Proofs.M32.Neck.SliceTransport
import PoincareConjecture.Proofs.M32.Claim11_34.Isotopy.AmbientFlow


















set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M32




theorem exists_tube_prescribed_sphere_compact_transport :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ 1 / 200 ∧
      epsilon₀ ≤ 1 / (64 * Real.pi) ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        {g : RiemannianMetric 3 M} {X : Set M}
        (C : EpsilonTubeCertificate g X) (N : EpsilonNeck g),
        C.epsilon ≤ epsilon₀ → N.epsilon ≤ epsilon₀ → N.center ∈ C.carrier →
        N.closedCollar (32 * Real.pi) ⊆ C.carrier →
        ∃ (e : M ≃ₜ M) (K : Set M), IsCompact K ∧ K ⊆ C.carrier ∧
          (∀ x, x ∉ K → e x = x) ∧
          e '' N.central_sphere = C.cylinder.middleSphere ∧ e '' C.carrier = C.carrier := by
  obtain ⟨epsilon₀, hpos, hsmall, hfixed, htransport⟩ :=
    exists_center_in_carrier_compact_transport.{u}
  refine ⟨epsilon₀, hpos, hsmall, hfixed, ?_⟩
  intro M _ _ _ _ _ _ _ g X C N hC hN hcenter hcollar
  have hcover := hcenter
  rw [C.carrier_eq_chain_union, mem_iUnion] at hcover
  obtain ⟨i, hi⟩ := hcover
  let P := C.chain.neck i.1
  have hP : P.epsilon ≤ epsilon₀ := by
    change (C.chain.neck i.1).epsilon ≤ epsilon₀
    rw [C.chain.epsilon_eq i.1 i.2]
    exact hC
  have hPU : P.carrier ⊆ C.carrier := by
    rw [C.carrier_eq_chain_union]
    exact subset_iUnion (fun j : {j // j ∈ C.chain.shape.active} =>
      (C.chain.neck j.1).carrier) i
  obtain ⟨e, K, hK, hKsubset, hfix, hsphere⟩ := htransport N P hN hP hi
  have hKU : K ⊆ C.carrier :=
    hKsubset.trans (union_subset hcollar hPU)
  have heU : e '' C.carrier = C.carrier := by
    apply subset_antisymm
    · rintro y ⟨x, hx, rfl⟩
      by_contra hn
      have hyK : e x ∉ K := fun h => hn (hKU h)
      have he : e x = x := e.injective (hfix (e x) hyK)
      apply hn
      rw [he]
      exact hx
    · intro y hy
      refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
      by_contra hn
      have hxK : e.symm y ∉ K := fun h => hn (hKU h)
      have he : y = e.symm y := (e.apply_symm_apply y).symm.trans (hfix (e.symm y) hxK)
      exact hn (he ▸ hy)
  obtain ⟨f, L, hL, hLU, hfixf, hspheref, hfU⟩ :=
    exists_compactly_supported_homeomorph_of_sphere_isotopic C.carrier_open
      (C.central_sphere_isotopy i.1 i.2)
  refine ⟨e.trans f, K ∪ L, hK.union hL, union_subset hKU hLU, ?_, ?_, ?_⟩
  · intro x hx
    change f (e x) = x
    rw [hfix x (fun h => hx (Or.inl h))]
    exact hfixf x (fun h => hx (Or.inr h))
  · change (f ∘ e) '' N.central_sphere = C.cylinder.middleSphere
    rw [image_comp, hsphere]
    exact hspheref
  · change (f ∘ e) '' C.carrier = C.carrier
    rw [image_comp, heU, hfU]

end PoincareConjecture.M32
