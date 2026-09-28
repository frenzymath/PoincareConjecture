import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Overlap.Nearby
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Separation
import Mathlib.Topology.Connected.Clopen

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.EpsilonNeck

theorem exists_connected_center_compact_transport :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        {g : RiemannianMetric 3 M} {ε : ℝ},
        0 < ε → ε ≤ ε₀ → ∀ (X : Set M), IsPreconnected X →
        (∀ x ∈ X, ∃ N : EpsilonNeck g, N.epsilon = ε ∧ N.center = x) →
        ∀ N₀ N₁ : EpsilonNeck g, N₀.epsilon = ε → N₁.epsilon = ε →
        N₀.center ∈ X → N₁.center ∈ X →
        ∃ (e : M ≃ₜ M) (K : Set M), IsCompact K ∧
          (∀ x, x ∉ K → e x = x) ∧ e '' N₀.central_sphere = N₁.central_sphere := by
  obtain ⟨ε₀, hε₀, hε₀small, hnear⟩ := exists_nearby_compact_transport.{u}
  refine ⟨ε₀, hε₀, hε₀small, ?_⟩
  intro M _ _ _ _ _ _ _ g ε hεpos hε X hX hcover N₀ N₁ hN₀ hN₁ hx₀ hx₁
  let R (N P : EpsilonNeck g) : Prop :=
    ∃ (e : M ≃ₜ M) (K : Set M), IsCompact K ∧
      (∀ x, x ∉ K → e x = x) ∧ e '' N.central_sphere = P.central_sphere
  have hrefl (N : EpsilonNeck g) : R N N :=
    ⟨Homeomorph.refl M, ∅, isCompact_empty, fun _ _ => rfl, by simp⟩
  have hsymm {N P : EpsilonNeck g} (h : R N P) : R P N := by
    obtain ⟨e, K, hK, hfix, hs⟩ := h
    refine ⟨e.symm, K, hK, ?_, ?_⟩
    · intro x hx
      exact (congrArg e.symm (hfix x hx)).symm.trans (e.symm_apply_apply x)
    · rw [← hs]
      exact e.symm_image_image _
  have htrans {N P Q : EpsilonNeck g} (hNP : R N P) (hPQ : R P Q) : R N Q := by
    obtain ⟨e, K, hK, hefix, he⟩ := hNP
    obtain ⟨f, L, hL, hffix, hf⟩ := hPQ
    refine ⟨e.trans f, K ∪ L, hK.union hL, ?_, ?_⟩
    · intro x hx
      change f (e x) = x
      rw [hefix x (fun h => hx (Or.inl h)), hffix x (fun h => hx (Or.inr h))]
    · change (f ∘ e) '' N.central_sphere = Q.central_sphere
      exact (Set.image_image (⇑f) (⇑e) _).symm.trans (by rw [he, hf])
  have hlocal (N P : EpsilonNeck g) (hN : N.epsilon = ε) (hP : P.epsilon = ε)
      (hcenter : P.center ∈ N.region (-ε⁻¹ / 2) (ε⁻¹ / 2)) : R N P := by
    obtain ⟨e, K, hK, _, hfix, _, hs⟩ := hnear hεpos hε N P hN hP hcenter
    exact ⟨e, K, hK, hfix, hs⟩
  have hmiddle (N : EpsilonNeck g) : N.center ∈ N.region (-ε⁻¹ / 2) (ε⁻¹ / 2) := by
    have hc := (N.mem_central_sphere_iff N.center).mp N.center_on_central_sphere
    have hi : 0 < ε⁻¹ := inv_pos.mpr hεpos
    refine ⟨hc.1, ?_, ?_⟩ <;> rw [hc.2]
    · linarith
    · linarith
  let good : Set X := {x | ∃ N : EpsilonNeck g, N.epsilon = ε ∧ N.center = x ∧ R N₀ N}
  have hgood : IsOpen good := by
    apply isOpen_iff_mem_nhds.mpr
    rintro x ⟨N, hN, hNx, hRN⟩
    have hxV : (x : M) ∈ N.region (-ε⁻¹ / 2) (ε⁻¹ / 2) := hNx ▸ hmiddle N
    apply mem_of_superset (((N.isOpen_region _ _).preimage continuous_subtype_val).mem_nhds hxV)
    intro y hy
    obtain ⟨P, hP, hPy⟩ := hcover y y.property
    exact ⟨P, hP, hPy, htrans hRN (hlocal N P hN hP (hPy.symm ▸ hy))⟩
  have hbad : IsOpen goodᶜ := by
    apply isOpen_iff_mem_nhds.mpr
    intro x hx
    obtain ⟨N, hN, hNx⟩ := hcover x x.property
    have hnot : ¬ R N₀ N := fun h => hx ⟨N, hN, hNx, h⟩
    have hxV : (x : M) ∈ N.region (-ε⁻¹ / 2) (ε⁻¹ / 2) := hNx ▸ hmiddle N
    apply mem_of_superset (((N.isOpen_region _ _).preimage continuous_subtype_val).mem_nhds hxV)
    intro y hy hgy
    obtain ⟨P, hP, hPy, hRP⟩ := hgy
    exact hnot (htrans hRP (hsymm (hlocal N P hN hP (hPy.symm ▸ hy))))
  let : PreconnectedSpace X := isPreconnected_iff_preconnectedSpace.mp hX
  have hall : good = univ := IsClopen.eq_univ ⟨isOpen_compl_iff.mp hbad, hgood⟩
    ⟨⟨N₀.center, hx₀⟩, N₀, hN₀, rfl, hrefl N₀⟩
  have hxgood : (⟨N₁.center, hx₁⟩ : X) ∈ good := hall ▸ mem_univ _
  obtain ⟨N, hN, hNx, hRN⟩ := hxgood
  have hNx' : N.center = N₁.center := hNx
  exact htrans hRN (hlocal N N₁ hN hN₁ (hNx' ▸ hmiddle N))

end PoincareConjecture.EpsilonNeck
