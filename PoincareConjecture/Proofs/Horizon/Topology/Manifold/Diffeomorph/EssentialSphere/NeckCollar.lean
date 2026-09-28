import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Separation
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Geometry.Transport.Charts
import Mathlib.Topology.OpenPartialHomeomorph.Composition

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

namespace PoincareConjecture.EpsilonNeck

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M}

theorem exists_slice_collar (N : EpsilonNeck g) {s δ : ℝ}
    (hlo : -N.epsilon⁻¹ < s - δ) (hhi : s + δ < N.epsilon⁻¹) :
    ∃ c : OpenPartialHomeomorph RoundCylinderSpace M,
      c.source = univ ×ˢ Ioo (-δ) δ ∧ c.target = N.region (s - δ) (s + δ) ∧
      ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ c c.source ∧
      ContMDiffOn (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞ c.symm c.target ∧
      ∀ p : RoundCylinderSpace, c p = N.coordinate_map (p.1, s + p.2) := by
  let shift : RoundCylinderSpace ≃ₜ RoundCylinderSpace :=
    (Homeomorph.refl UnitTwoSphere).prodCongr (Homeomorph.addLeft s)
  let e := shift.toOpenPartialHomeomorph.trans N.coordinatePartialHomeomorph
  let W : Set RoundCylinderSpace := univ ×ˢ Ioo (-δ) δ
  let c := e.restrOpen W (isOpen_univ.prod isOpen_Ioo)
  have hW : W ⊆ e.source := by
    rintro ⟨q, t⟩ ⟨_, ht⟩
    refine ⟨mem_univ _, mem_univ _, ?_⟩
    change s + t ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹
    constructor <;> linarith [ht.1, ht.2]
  have hsource : c.source = W := inter_eq_right.mpr hW
  have hinv (x : M) : c.symm x =
      ((N.coordinate_inverse x).1, (N.coordinate_inverse x).2 - s) := by
    change ((N.coordinate_inverse x).1, -s + (N.coordinate_inverse x).2) = _
    congr 1
    ring
  have htarget : c.target = N.region (s - δ) (s + δ) := by
    ext x
    change ((x ∈ N.carrier ∧ N.coordinate_inverse x ∈ univ) ∧
      e.symm x ∈ W) ↔ _
    simp only [mem_univ, and_true]
    change (x ∈ N.carrier ∧ c.symm x ∈ W) ↔ _
    rw [hinv]
    change (x ∈ N.carrier ∧ True ∧ -δ < (N.coordinate_inverse x).2 - s ∧
      (N.coordinate_inverse x).2 - s < δ) ↔
      x ∈ N.carrier ∧ s - δ < (N.coordinate_inverse x).2 ∧
        (N.coordinate_inverse x).2 < s + δ
    constructor
    · rintro ⟨hx, _, hl, hu⟩
      exact ⟨hx, by linarith, by linarith⟩
    · rintro ⟨hx, hl, hu⟩
      exact ⟨hx, trivial, by linarith, by linarith⟩
  refine ⟨c, hsource, htarget, ?_, ?_, fun _ => rfl⟩
  · apply N.coordinate_map_smooth.comp
      (contMDiff_fst.prodMk (contMDiff_const.add contMDiff_snd)).contMDiffOn
    intro p hp
    exact (hW (hsource ▸ hp)).2
  · have hsub : c.target ⊆ N.carrier := by
      rw [htarget]
      exact fun _ hx => hx.1
    have hsm := N.coordinate_inverse_smooth.mono hsub
    have h : ContMDiffOn (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞
        (fun x => ((N.coordinate_inverse x).1, (N.coordinate_inverse x).2 - s))
        c.target := (contMDiff_fst.comp_contMDiffOn hsm).prodMk
      ((contMDiff_snd.comp_contMDiffOn hsm).sub contMDiffOn_const)
    exact h.congr (fun x _ => hinv x)

end PoincareConjecture.EpsilonNeck
