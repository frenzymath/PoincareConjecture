import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Ends.Cylinder.GraphShift
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Overlap.GraphTransport
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Tube.Gluing.Coordinates.Chart
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Diffeomorph.CompactSupport
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Diffeomorph.Restriction







set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace
open scoped ContDiff Manifold Topology

namespace PoincareConjecture.EpsilonNeck

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [T2Space M] {g : RiemannianMetric 3 M} (N : EpsilonNeck g)



theorem exists_smooth_graph_transport (h : UnitTwoSphere → ℝ)
    (hh : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ h)
    (hdom : ∀ q, h q ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) :
    ∃ (D : Diffeomorph (𝓡 3) (𝓡 3) M M ∞) (K : Set M),
      IsCompact K ∧ K ⊆ N.carrier ∧
      (∀ x : M, x ∉ K → D x = x) ∧
      (∀ q : UnitTwoSphere,
        D (N.coordinate_map (q, 0)) = N.coordinate_map (q, h q)) ∧
      D '' N.central_sphere = range (fun q => N.coordinate_map (q, h q)) := by
  obtain ⟨r₀, hr₀, hr₀N, hbound⟩ := N.exists_graph_collar h hh.continuous hdom
  let r := (r₀ + N.epsilon⁻¹) / 2
  have hr₀r : r₀ < r := by dsimp [r]; linarith
  have hrN : r < N.epsilon⁻¹ := by dsimp [r]; linarith
  have hr : 0 < r := hr₀.trans hr₀r
  obtain ⟨D₀, _, hD₀fixed, hD₀slice⟩ := CylinderGluing.exists_supported_graph_shift
    (l := -r) (b := -r₀) (r := r) (neg_lt_neg hr₀r)
    (fun _ : UnitTwoSphere => (0 : ℝ)) contMDiff_const
    (fun _ => neg_neg_of_pos hr₀) (fun _ => hr)
  obtain ⟨Dh, _, hDhfixed, hDhslice⟩ := CylinderGluing.exists_supported_graph_shift
    (l := -r) (b := -r₀) (r := r) (neg_lt_neg hr₀r) h hh
    (fun q => (abs_lt.mp (hbound q)).1)
    (fun q => ((abs_lt.mp (hbound q)).2).trans hr₀r)
  let J := D₀.symm.trans Dh
  have hJfixed (p : RoundCylinderSpace) (hp : p.2 ≤ -r ∨ r ≤ p.2) : J p = p := by
    have hD₀inv : D₀.symm p = p := by
      apply D₀.injective
      change D₀ (D₀.symm p) = D₀ p
      rw [D₀.apply_symm_apply, hD₀fixed p hp]
    change Dh (D₀.symm p) = p
    rw [hD₀inv, hDhfixed p hp]
  have hJslice (q : UnitTwoSphere) : J (q, 0) = (q, h q) := by
    have hD₀inv : D₀.symm (q, 0) = (q, -r₀) := by
      apply D₀.injective
      change D₀ (D₀.symm (q, 0)) = D₀ (q, -r₀)
      rw [D₀.apply_symm_apply, hD₀slice]
    change Dh (D₀.symm (q, 0)) = _
    rw [hD₀inv, hDhslice]
  have hJoutside (p : RoundCylinderSpace) (hp : p ∉ N.cylinderDomain) : J p = p := by
    apply hJfixed
    by_cases hlow : p.2 ≤ -r
    · exact Or.inl hlow
    · right
      apply le_of_not_gt
      intro hhigh
      exact hp ⟨mem_univ _, by constructor <;> linarith⟩
  let J₀ := J.restrictOpensOfFixedCompl N.cylinderDomainOpen subset_rfl hJoutside
  let F := (N.coordinateDiffeomorph.symm.trans J₀).trans N.coordinateDiffeomorph
  let K := N.closedCollar r
  have hK : IsCompact K := N.isCompact_closedCollar hrN
  have hKN : K ⊆ N.carrier := N.closedCollar_subset_carrier hrN
  have hF (x : N.carrierOpen) : (F x : M) = N.coordinate_map (J (N.coordinate_inverse x)) := rfl
  have hFfixed (x : N.carrierOpen) (hx : (x : M) ∉ K) : F x = x := by
    apply Subtype.ext
    rw [hF]
    have hout : (N.coordinate_inverse x).2 ≤ -r ∨ r ≤ (N.coordinate_inverse x).2 := by
      by_cases hlow : (N.coordinate_inverse x).2 ≤ -r
      · exact Or.inl hlow
      · right
        apply le_of_not_gt
        intro hhigh
        exact hx ⟨N.coordinate_inverse x,
          ⟨mem_univ _, (lt_of_not_ge hlow).le, hhigh.le⟩,
          N.coordinate_map_coordinate_inverse x.property⟩
    rw [hJfixed _ hout]
    exact N.coordinate_map_coordinate_inverse x.property
  obtain ⟨D, hD, hDfixed⟩ := Diffeomorph.exists_extension_of_isCompact
    N.carrierOpen F hK hKN hFfixed
  have hDslice (q : UnitTwoSphere) :
      D (N.coordinate_map (q, 0)) = N.coordinate_map (q, h q) := by
    have hz : (q, (0 : ℝ)) ∈ N.cylinderDomain :=
      ⟨mem_univ _, neg_neg_of_pos (inv_pos.mpr N.epsilon_pos), inv_pos.mpr N.epsilon_pos⟩
    rw [hD (⟨N.coordinate_map (q, 0), N.coordinate_map_mem hz⟩ : N.carrierOpen), hF,
      N.coordinate_inverse_coordinate_map hz, hJslice]
  refine ⟨D, K, hK, hKN, hDfixed, hDslice, ?_⟩
  rw [← N.centralSphere_range, ← range_comp]
  congr 1
  funext q
  exact hDslice q

end PoincareConjecture.EpsilonNeck
