import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Tube.Gluing.Coordinates.Chart
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Geometry.Manifold.Algebra.Structures












noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace
open scoped Manifold ContDiff

namespace PoincareConjecture.EpsilonNeck

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M} (N : EpsilonNeck g)



theorem exists_centered_neck_coordinates
    (f : UnitTwoSphere → ℝ) (hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ f)
    (hdom : ∀ q, f q ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) :
    ∃ D : Diffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3)
        RoundCylinderSpace N.carrierOpen ∞,
      (∀ p, (N.coordinate_inverse (D p)).1 = p.1) ∧
      (∀ q, (D (q, 0) : M) = N.coordinate_map (q, f q)) ∧
      (∀ p : RoundCylinderSpace, ∃ a : ℝ, 0 < a ∧
        HasDerivAt (fun t => (N.coordinate_inverse (D (p.1, t))).2) a p.2) ∧
      ∀ (q : UnitTwoSphere) (t : ℝ),
        (N.coordinate_inverse (D (q, t))).2 ≤ f q ↔ t ≤ 0 := by
  let c : ℝ := N.epsilon⁻¹ / (Real.pi / 2)
  have hc : 0 < c := div_pos (inv_pos.mpr N.epsilon_pos) (by positivity)
  have hcr : c * (Real.pi / 2) = N.epsilon⁻¹ :=
    div_mul_cancel₀ _ (by positivity)
  have hscaled {s : ℝ} (hs : s ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) :
      s / c ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor
    · apply (lt_div_iff₀ hc).2
      nlinarith [hs.1]
    · apply (div_lt_iff₀ hc).2
      nlinarith [hs.2]
  have hatan (t : ℝ) : c * Real.arctan t ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ := by
    constructor
    · nlinarith [mul_lt_mul_of_pos_left (Real.neg_pi_div_two_lt_arctan t) hc]
    · nlinarith [mul_lt_mul_of_pos_left (Real.arctan_lt_pi_div_two t) hc]
  let shift : UnitTwoSphere → ℝ := fun q => Real.tan (f q / c)
  have hshift : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ shift := by
    intro q
    apply ContMDiffAt.comp (I' := 𝓘(ℝ, ℝ)) (f := fun q => f q / c) (g := Real.tan) q
    · exact (Real.contDiffAt_tan.mpr
        (Real.cos_pos_of_mem_Ioo (hscaled (hdom q))).ne').contMDiffAt
    · exact (hf.div_const c).contMDiffAt
  let P : RoundCylinderSpace → N.cylinderDomainOpen := fun p =>
    ⟨(p.1, c * Real.arctan (p.2 + shift p.1)), mem_univ _, hatan _⟩
  let Q : N.cylinderDomainOpen → RoundCylinderSpace := fun z =>
    (z.1.1, Real.tan (z.1.2 / c) - shift z.1.1)
  have hP : ContMDiff ((𝓡 2).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞ P := by
    rw [← ContMDiff.subtypeVal_comp_iff N.cylinderDomainOpen]
    exact contMDiff_fst.prodMk (contMDiff_const.mul
      (Real.contDiff_arctan.contMDiff.comp (contMDiff_snd.add
        (hshift.comp contMDiff_fst))))
  have hQ : ContMDiff ((𝓡 2).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞ Q := by
    have hsnd : ContMDiff ((𝓡 2).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
        (fun z : N.cylinderDomainOpen => Real.tan (z.1.2 / c)) := by
      intro z
      apply ContMDiffAt.comp (I' := 𝓘(ℝ, ℝ)) (f := fun z : N.cylinderDomainOpen => z.1.2 / c)
        (g := Real.tan) z
      · exact (Real.contDiffAt_tan.mpr
          (Real.cos_pos_of_mem_Ioo (hscaled z.property.2)).ne').contMDiffAt
      · exact ((contMDiff_snd.comp contMDiff_subtype_val).div_const c).contMDiffAt
    exact (contMDiff_fst.comp contMDiff_subtype_val).prodMk
      (hsnd.sub (hshift.comp (contMDiff_fst.comp contMDiff_subtype_val)))
  have hleft : Function.LeftInverse Q P := by
    rintro ⟨q, t⟩
    refine Prod.ext ?_ ?_
    · rfl
    dsimp [Q, P]
    rw [mul_div_cancel_left₀ _ hc.ne', Real.tan_arctan]
    exact add_sub_cancel_right _ _
  have hright : Function.RightInverse Q P := by
    intro z
    apply Subtype.ext
    refine Prod.ext ?_ ?_
    · rfl
    dsimp [P, Q]
    rw [sub_add_cancel, Real.arctan_tan (hscaled z.property.2).1 (hscaled z.property.2).2]
    field_simp
  let K : Diffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, ℝ))
      RoundCylinderSpace N.cylinderDomainOpen ∞ :=
    { toFun := P
      invFun := Q
      left_inv := hleft
      right_inv := hright
      contMDiff_toFun := hP
      contMDiff_invFun := hQ }
  have hKzero (q : UnitTwoSphere) : (K (q, 0)).1 = (q, f q) := by
    refine Prod.ext ?_ ?_
    · rfl
    change c * Real.arctan (0 + Real.tan (f q / c)) = f q
    rw [zero_add, Real.arctan_tan (hscaled (hdom q)).1 (hscaled (hdom q)).2]
    field_simp
  have hKderiv (p : RoundCylinderSpace) : ∃ a : ℝ, 0 < a ∧
      HasDerivAt (fun t => (K (p.1, t)).1.2) a p.2 := by
    refine ⟨c * (1 / (1 + (p.2 + shift p.1) ^ 2)), by positivity, ?_⟩
    change HasDerivAt (fun t => c * Real.arctan (t + shift p.1)) _ p.2
    simpa only [id_eq, mul_one] using
      (((hasDerivAt_id p.2).add_const (shift p.1)).arctan.const_mul c)
  let D := K.trans N.coordinateDiffeomorph
  have hcoords (p : RoundCylinderSpace) : N.coordinate_inverse (D p) = (K p).1 :=
    N.coordinate_inverse_coordinate_map (K p).property
  refine ⟨D, ?_, ?_, ?_, ?_⟩
  · intro p
    rw [hcoords]
    rfl
  · intro q
    change N.coordinate_map (K (q, 0)).1 = N.coordinate_map (q, f q)
    rw [hKzero]
  · intro p
    simpa only [hcoords] using hKderiv p
  · intro q t
    have hm : StrictMono (fun t : ℝ => (K (q, t)).1.2) := by
      apply strictMono_of_deriv_pos
      intro t
      obtain ⟨a, ha, hd⟩ := hKderiv (q, t)
      rwa [hd.deriv]
    rw [hcoords]
    have h := hm.le_iff_le (a := t) (b := 0)
    rw [hKzero] at h
    exact h

end PoincareConjecture.EpsilonNeck
