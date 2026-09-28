import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Ends.CalibratedHorn.RicciComparison.SphereTransport
import Mathlib.Topology.Connected.Clopen

noncomputable section
set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.EpsilonNeck

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  {g : RiemannianMetric 3 M}

theorem connected_center_smooth_transport_of_epsilon_le
    (X : Set M) (hX : IsPreconnected X)
    (hcover : ∀ x ∈ X, ∃ N : EpsilonNeck g, N.epsilon ≤ 1 / 200 ∧ N.center = x)
    (N₀ N₁ : EpsilonNeck g) (hN₀ : N₀.epsilon ≤ 1 / 200) (hN₁ : N₁.epsilon ≤ 1 / 200)
    (hx₀ : N₀.center ∈ X) (hx₁ : N₁.center ∈ X) :
    ∃ (D : Diffeomorph (𝓡 3) (𝓡 3) M M ∞) (K : Set M), IsCompact K ∧
      (∀ x, x ∉ K → D x = x) ∧ D '' N₀.central_sphere = N₁.central_sphere := by
  let R (N P : EpsilonNeck g) : Prop :=
    ∃ (D : Diffeomorph (𝓡 3) (𝓡 3) M M ∞) (K : Set M), IsCompact K ∧
      (∀ x, x ∉ K → D x = x) ∧ D '' N.central_sphere = P.central_sphere
  have hrefl (N : EpsilonNeck g) : R N N :=
    ⟨Diffeomorph.refl (𝓡 3) M ∞, ∅, isCompact_empty, fun _ _ => rfl, by simp⟩
  have hsymm {N P : EpsilonNeck g} (h : R N P) : R P N := by
    obtain ⟨D, K, hK, hfix, hs⟩ := h
    refine ⟨D.symm, K, hK, ?_, ?_⟩
    · intro x hx
      exact (congrArg D.symm (hfix x hx)).symm.trans (D.symm_apply_apply x)
    · rw [← hs]
      exact D.toEquiv.symm_image_image _
  have htrans {N P Q : EpsilonNeck g} (hNP : R N P) (hPQ : R P Q) : R N Q := by
    obtain ⟨D, K, hK, hDfix, hD⟩ := hNP
    obtain ⟨E, L, hL, hEfix, hE⟩ := hPQ
    refine ⟨D.trans E, K ∪ L, hK.union hL, ?_, ?_⟩
    · intro x hx
      change E (D x) = x
      rw [hDfix x (fun h => hx (Or.inl h)), hEfix x (fun h => hx (Or.inr h))]
    · change (E ∘ D) '' N.central_sphere = Q.central_sphere
      rw [image_comp, hD, hE]
  have hlocal (N P : EpsilonNeck g) (hN : N.epsilon ≤ 1 / 200)
      (hP : P.epsilon ≤ 1 / 200) (hcenter : P.center ∈ N.carrier) : R N P := by
    obtain ⟨D, K, hK, _, hfix, hs⟩ :=
      P.central_sphere_smooth_transport_of_center_mem N hP hN hcenter
    exact ⟨D, K, hK, hfix, hs⟩
  have hmiddle (N : EpsilonNeck g) : N.center ∈ N.carrier :=
    N.central_sphere_subset N.center_on_central_sphere
  let good : Set X := {x | ∃ N : EpsilonNeck g,
    N.epsilon ≤ 1 / 200 ∧ N.center = x ∧ R N₀ N}
  have hgood : IsOpen good := by
    apply isOpen_iff_mem_nhds.mpr
    rintro x ⟨N, hN, hNx, hRN⟩
    have hxV : (x : M) ∈ N.carrier := hNx ▸ hmiddle N
    apply mem_of_superset ((N.carrier_open.preimage continuous_subtype_val).mem_nhds hxV)
    intro y hy
    obtain ⟨P, hP, hPy⟩ := hcover y y.property
    exact ⟨P, hP, hPy, htrans hRN (hlocal N P hN hP (hPy.symm ▸ hy))⟩
  have hbad : IsOpen goodᶜ := by
    apply isOpen_iff_mem_nhds.mpr
    intro x hx
    obtain ⟨N, hN, hNx⟩ := hcover x x.property
    have hnot : ¬ R N₀ N := fun h => hx ⟨N, hN, hNx, h⟩
    have hxV : (x : M) ∈ N.carrier := hNx ▸ hmiddle N
    apply mem_of_superset ((N.carrier_open.preimage continuous_subtype_val).mem_nhds hxV)
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
