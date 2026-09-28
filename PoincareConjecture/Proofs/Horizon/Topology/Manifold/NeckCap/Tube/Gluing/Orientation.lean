import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Tube.Gluing.Scalar
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Topology.Order.IntermediateValue













set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.CylinderGluing



theorem exists_scalar_collar_extension_of_nonzero (h : RoundCylinderSpace → ℝ)
    (hh : ContMDiff ((𝓡 2).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ h)
    (hne : ∀ q : UnitTwoSphere, deriv (fun t : ℝ => h (q, t)) 0 ≠ 0) :
    ∃ (r : ℝ) (F : Diffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ))
        ((𝓡 2).prod 𝓘(ℝ, ℝ)) RoundCylinderSpace RoundCylinderSpace ∞),
      0 < r ∧ (∀ p : RoundCylinderSpace, (F p).1 = p.1) ∧
      ∀ (q : UnitTwoSphere) (t : ℝ), |t| < r → F (q, t) = (q, h (q, t)) := by
  let α : UnitTwoSphere → ℝ := fun q => deriv (fun t : ℝ => h (q, t)) 0
  have hα : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ α := by
    intro q
    have hd := hh.contMDiffAt.mfderiv (fun q t => h (q, t)) (fun _ => (0 : ℝ))
      (contMDiffAt_const (x := q)) (by simp : (∞ : ℕ∞ω) + 1 ≤ ∞)
    rw [inTangentCoordinates_model_space] at hd
    have hv := hd.clm_apply (contMDiffAt_const (c := (1 : ℝ)))
    simpa only [mfderiv_eq_fderiv, fderiv_eq_deriv_mul, mul_one, α] using hv
  have hrank : 1 < Module.rank ℝ (EuclideanSpace ℝ (Fin 3)) := by
    rw [← Module.finrank_eq_rank]
    norm_num
  let : ConnectedSpace UnitTwoSphere := isConnected_iff_connectedSpace.mp
    (isConnected_sphere hrank (0 : EuclideanSpace ℝ (Fin 3)) zero_le_one)
  by_cases hp : ∀ q, 0 < α q
  · exact exists_scalar_collar_extension h hh hp
  push Not at hp
  obtain ⟨p, hp⟩ := hp
  have hn (q : UnitTwoSphere) : α q < 0 := by
    by_contra hq
    obtain ⟨w, hw⟩ := intermediate_value_univ p q hα.continuous
      (show (0 : ℝ) ∈ Icc (α p) (α q) from ⟨hp, le_of_not_gt hq⟩)
    exact hne w hw
  have hhneg : ContMDiff ((𝓡 2).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ (fun p => -h p) :=
    hh.neg
  have hpneg (q : UnitTwoSphere) : 0 < deriv (fun t : ℝ => -h (q, t)) 0 := by
    have hd := (((hh.comp ((contMDiff_const (c := q)).prodMk contMDiff_id)).contDiff.differentiable
      (by simp)) 0).hasDerivAt.neg.deriv
    change deriv (fun t : ℝ => -h (q, t)) 0 = -α q at hd
    rw [hd]
    exact neg_pos.mpr (hn q)
  obtain ⟨r, K, hr, hKfst, hK⟩ := exists_scalar_collar_extension _ hhneg hpneg
  let R : Diffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, ℝ))
      RoundCylinderSpace RoundCylinderSpace ∞ :=
    { toEquiv :=
        { toFun := fun p => (p.1, -p.2)
          invFun := fun p => (p.1, -p.2)
          left_inv := by intro p; simp
          right_inv := by intro p; simp }
      contMDiff_toFun := contMDiff_fst.prodMk contMDiff_snd.neg
      contMDiff_invFun := contMDiff_fst.prodMk contMDiff_snd.neg }
  refine ⟨r, K.trans R, hr, hKfst, ?_⟩
  intro q t ht
  change R (K (q, t)) = (q, h (q, t))
  rw [hK q t ht]
  change (q, -(-h (q, t))) = (q, h (q, t))
  rw [neg_neg]

end PoincareConjecture.CylinderGluing
