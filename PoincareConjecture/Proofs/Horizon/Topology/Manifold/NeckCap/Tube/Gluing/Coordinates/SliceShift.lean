import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Tube.Gluing.Coordinates.AxialShift
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Tube.Gluing.Coordinates.Chart
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Tube.Gluing.Band.GraphSlab
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

theorem exists_smooth_slice_shift {b c : ℝ}
    (hb : b ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹)
    (hc : c ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) (hbc : b < c) :
    ∃ (ρ : ℝ) (D : Diffeomorph (𝓡 3) (𝓡 3) M M ∞),
      0 < ρ ∧
      (∀ x : M, x ∉ N.carrier → D x = x) ∧
      (∀ p : RoundCylinderSpace, p ∈ N.cylinderDomain → |p.2 - b| < ρ →
        D (N.coordinate_map p) = N.coordinate_map (p.1, p.2 + (c - b))) ∧
      D '' {x : M | x ∈ N.carrier ∧ (N.coordinate_inverse x).2 ≤ b} =
        {x : M | x ∈ N.carrier ∧ (N.coordinate_inverse x).2 ≤ c} := by
  let l := (-N.epsilon⁻¹ + b) / 2
  let r := (c + N.epsilon⁻¹) / 2
  have hl : -N.epsilon⁻¹ < l := by dsimp [l]; linarith [hb.1]
  have hlb : l < b := by dsimp [l]; linarith [hb.1]
  have hcr : c < r := by dsimp [r]; linarith [hc.2]
  have hr : r < N.epsilon⁻¹ := by dsimp [r]; linarith [hc.2]
  obtain ⟨ρ, J, hρ, hJfst, hJmono, hJfixed, hJlocal⟩ :=
    CylinderGluing.exists_supported_axial_shift hlb hbc hcr
  have hJdomain (p : RoundCylinderSpace) : J p ∈ N.cylinderDomain ↔ p ∈ N.cylinderDomain := by
    rcases p with ⟨q, t⟩
    have hlo : (J (q, -N.epsilon⁻¹)).2 = -N.epsilon⁻¹ :=
      congrArg Prod.snd (hJfixed _ (Or.inl hl.le))
    have hhi : (J (q, N.epsilon⁻¹)).2 = N.epsilon⁻¹ :=
      congrArg Prod.snd (hJfixed _ (Or.inr hr.le))
    change (_ ∧ -N.epsilon⁻¹ < (J (q, t)).2 ∧ (J (q, t)).2 < N.epsilon⁻¹) ↔
      (_ ∧ -N.epsilon⁻¹ < t ∧ t < N.epsilon⁻¹)
    constructor
    · rintro ⟨_, hlow, hhigh⟩
      exact ⟨mem_univ _, (hJmono q).lt_iff_lt.mp (hlo.symm ▸ hlow),
        (hJmono q).lt_iff_lt.mp (hhi.symm ▸ hhigh)⟩
    · rintro ⟨_, hlow, hhigh⟩
      exact ⟨mem_univ _, hlo ▸ hJmono q hlow, hhi ▸ hJmono q hhigh⟩
  let J₀ := J.restrictOpens N.cylinderDomainOpen N.cylinderDomainOpen hJdomain
  let F := (N.coordinateDiffeomorph.symm.trans J₀).trans N.coordinateDiffeomorph
  let K := N.closedGraphSlab (fun _ => l) (fun _ => r)
  have hK : IsCompact K := N.isCompact_closedGraphSlab (fun _ => l) (fun _ => r)
    continuous_const continuous_const
    (fun _ => ⟨hl, (hlb.trans hbc).trans hc.2⟩)
    (fun _ => ⟨hb.1.trans (hbc.trans hcr), hr⟩) (fun _ => (hlb.trans hbc).trans hcr)
  have hKN : K ⊆ N.carrier := fun _ hx => hx.1
  have hF (x : N.carrierOpen) : (F x : M) = N.coordinate_map (J (N.coordinate_inverse x)) := rfl
  have hFfixed (x : N.carrierOpen) (hx : (x : M) ∉ K) : F x = x := by
    apply Subtype.ext
    rw [hF]
    have hout : (N.coordinate_inverse x).2 ≤ l ∨ r ≤ (N.coordinate_inverse x).2 := by
      by_cases hlow : (N.coordinate_inverse x).2 ≤ l
      · exact Or.inl hlow
      · right
        apply le_of_not_gt
        intro hhigh
        exact hx ⟨x.property, (lt_of_not_ge hlow).le, hhigh.le⟩
    rw [hJfixed _ hout]
    exact N.coordinate_map_coordinate_inverse x.property
  obtain ⟨D, hD, hDfixed⟩ := Diffeomorph.exists_extension_of_isCompact
    N.carrierOpen F hK hKN hFfixed
  have hDoutside (x : M) (hx : x ∉ N.carrier) : D x = x :=
    hDfixed x (fun h => hx (hKN h))
  have hDmem (x : M) : D x ∈ N.carrier ↔ x ∈ N.carrier :=
    D.mem_iff_of_fixed_compl subset_rfl hDoutside x
  have hDcoord (p : RoundCylinderSpace) (hp : p ∈ N.cylinderDomain) :
      D (N.coordinate_map p) = N.coordinate_map (J p) := by
    rw [hD (⟨N.coordinate_map p, N.coordinate_map_mem hp⟩ : N.carrierOpen), hF]
    rw [N.coordinate_inverse_coordinate_map hp]
  have hDinv (x : M) (hx : x ∈ N.carrier) :
      N.coordinate_inverse (D x) = J (N.coordinate_inverse x) := by
    have hz := N.coordinate_inverse_mem x hx
    have hcoord := hDcoord (N.coordinate_inverse x) hz
    rw [N.coordinate_map_coordinate_inverse hx] at hcoord
    rw [hcoord, N.coordinate_inverse_coordinate_map ((hJdomain _).mpr hz)]
  have hJb (q : UnitTwoSphere) : J (q, b) = (q, c) := by
    simpa only [sub_self, abs_zero, add_sub_cancel] using hJlocal (q, b) (by simpa using hρ)
  have hDside (x : M) (hx : x ∈ N.carrier) :
      (N.coordinate_inverse (D x)).2 ≤ c ↔ (N.coordinate_inverse x).2 ≤ b := by
    rw [hDinv x hx, ← show (J ((N.coordinate_inverse x).1, b)).2 = c from
      congrArg Prod.snd (hJb _)]
    exact (hJmono (N.coordinate_inverse x).1).le_iff_le
  refine ⟨ρ, D, hρ, hDoutside, ?_, ?_⟩
  · intro p hp hnear
    rw [hDcoord p hp, hJlocal p hnear]
  · ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨(hDmem y).mpr hy.1, (hDside y hy.1).mpr hy.2⟩
    · intro hx
      have hy : D.symm x ∈ N.carrier := (hDmem _).mp (by simpa using hx.1)
      refine ⟨D.symm x, ⟨hy, (hDside _ hy).mp ?_⟩, D.apply_symm_apply x⟩
      simpa only [D.apply_symm_apply] using hx.2

end PoincareConjecture.EpsilonNeck
