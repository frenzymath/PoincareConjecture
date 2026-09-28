import PoincareConjecture.Proofs.M45.Ch12_Standard.CapNeckTopology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M45

local notation "IC" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M}

theorem neck_axial_derivative (N : EpsilonNeck g) {x : M} (hx : x ∈ N.carrier) :
    ∃ d : TangentSpace (𝓡 3) x,
      mvfderiv (𝓡 3) (fun y => (N.coordinate_inverse y).2) x d = 1 := by
  let z := N.coordinate_inverse x
  have hz := N.coordinate_inverse_mem x hx
  have hk := (M36.neck_coordinate_contMDiffAt N hz).mdifferentiableAt (by simp)
  have hf := (M36.neck_inverse_contMDiffAt N hx).snd.mdifferentiableAt (by simp)
  have hright := M36.neck_coordinate_inverse N hx
  have heq : (fun y => (N.coordinate_inverse y).2) ∘ N.coordinate_map =ᶠ[𝓝 z]
      Prod.snd := by
    filter_upwards [(isOpen_univ.prod isOpen_Ioo).mem_nhds hz] with w hw
    exact congrArg Prod.snd (M36.neck_inverse_coordinate N w hw)
  have hd : mvfderiv IC
      ((fun y => (N.coordinate_inverse y).2) ∘ N.coordinate_map) z (0, 1) = 1 := by
    change mfderiv IC 𝓘(ℝ, ℝ) _ z (0, 1) = 1
    rw [heq.mfderiv_eq, mfderiv_snd]
    rfl
  rw [mvfderiv_comp_apply_of_eq z hf hk hright] at hd
  exact ⟨_, hd⟩

theorem neck_core_iff_nonpos (N : EpsilonNeck g) {K : Set M} (hK : IsClosed K)
    (hB : frontier K = N.central_sphere)
    (hleft : N.region (-N.epsilon⁻¹) 0 ⊆ interior K)
    (hright : N.region 0 N.epsilon⁻¹ ⊆ Kᶜ) {x : M} (hx : x ∈ N.carrier) :
    x ∈ K ↔ (N.coordinate_inverse x).2 ≤ 0 := by
  have hz := (N.coordinate_inverse_mem x hx).2
  constructor
  · intro hxin
    by_contra h
    exact hright ⟨hx, lt_of_not_ge h, hz.2⟩ hxin
  · intro h
    rcases lt_or_eq_of_le h with h | h
    · exact interior_subset (hleft ⟨hx, hz.1, h⟩)
    · have hxB := (M36.neck_central_iff N).mpr ⟨hx, h⟩
      rw [← hB] at hxB
      exact hK.closure_eq ▸ frontier_subset_closure hxB

theorem neck_boundary_defining_function [PreconnectedSpace M]
    (N : EpsilonNeck g) {K C : Set M} (hK : IsClosed K)
    (hinterior : (interior K).Nonempty) (hproper : K ≠ univ)
    (hB : frontier K = N.central_sphere) (hNC : N.carrier ⊆ C)
    {x : M} (hx : x ∈ frontier K) :
    ∃ U : Set M, ∃ f : M → ℝ, IsOpen U ∧ x ∈ U ∧ U ⊆ C ∧
      (∀ y ∈ U, y ∈ K ↔ f y ≤ 0) ∧ f x = 0 ∧
      ContMDiffOn (𝓡 3) 𝓘(ℝ, ℝ) ∞ f U ∧
      ∃ d : TangentSpace (𝓡 3) x, d ≠ 0 ∧ mvfderiv (𝓡 3) f x d ≠ 0 := by
  have hxN := N.central_sphere_subset (hB ▸ hx)
  have hx0 := ((M36.neck_central_iff N).mp (hB ▸ hx)).2
  obtain ⟨d, hd⟩ := neck_axial_derivative N hxN
  have hdne : d ≠ 0 := by intro h; simp only [h, map_zero, zero_ne_one] at hd
  rcases neck_opposite_sides N hK hinterior hproper hB with hside | hside
  · refine ⟨N.carrier, fun y => (N.coordinate_inverse y).2, N.carrier_open,
      hxN, hNC, fun y hy => neck_core_iff_nonpos N hK hB hside.1 hside.2 hy,
      hx0, (fun y hy => (N.coordinate_inverse_smooth y hy).snd), d, hdne, ?_⟩
    rw [hd]
    norm_num
  · refine ⟨N.carrier, fun y => -(N.coordinate_inverse y).2, N.carrier_open,
      hxN, hNC, ?_, by simp only [hx0, neg_zero],
      (fun y hy => (N.coordinate_inverse_smooth y hy).snd.neg), d, hdne, ?_⟩
    · intro y hy
      have hz := (N.coordinate_inverse_mem y hy).2
      constructor
      · intro hyK
        by_contra h
        have hneg : (N.coordinate_inverse y).2 < 0 := by linarith
        exact hside.1 ⟨hy, hz.1, hneg⟩ hyK
      · intro h
        have hnonneg : 0 ≤ (N.coordinate_inverse y).2 := by linarith
        rcases lt_or_eq_of_le hnonneg with hpos | hzero
        · exact interior_subset (hside.2 ⟨hy, hpos, hz.2⟩)
        · have hyB := (M36.neck_central_iff N).mpr ⟨hy, hzero.symm⟩
          rw [← hB] at hyB
          exact hK.closure_eq ▸ frontier_subset_closure hyB
    · change (mvfderiv (𝓡 3) (-(fun y => (N.coordinate_inverse y).2)) x) d ≠ 0
      rw [mvfderiv_neg]
      simpa only [neg_apply, hd] using (by norm_num : -(1 : ℝ) ≠ 0)

end PoincareConjecture.M45
