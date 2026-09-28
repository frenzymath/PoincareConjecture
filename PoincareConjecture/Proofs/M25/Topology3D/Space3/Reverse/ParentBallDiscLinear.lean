import PoincareConjecture.Proofs.M25.Topology3D.Space3.ChartIsotopyExtension
import PoincareConjecture.Proofs.M25.Topology3D.Space3.RadialIsotopyTransport
import PoincareConjecture.Proofs.M25.Topology3D.Space3.SourceCircleDisc
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Analysis.SpecialFunctions.SmoothTransition











set_option autoImplicit false

open Set Metric Filter InnerProductSpace
open scoped ContDiff Manifold Topology InnerProductSpace

namespace PoincareConjecture.M25.Topology3D

attribute [local instance] sourceCircle_stereographic_dimension


theorem exists_boundary_linear_realization
    (v : UnitTwoSphere)
    (L : (ℝ ∙ (v : E3))ᗮ ≃L[ℝ] (ℝ ∙ (v : E3))ᗮ)
    {K : Set ((ℝ ∙ (v : E3))ᗮ)} (hK : IsCompact K) :
    ∃ F : Diffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) E3 E3 ∞,
      (∀ y : E3, ‖F y‖ = ‖y‖) ∧
      ∀ x ∈ K,
        F (stereoInvFun (norm_eq_of_mem_sphere v) x : E3) =
          (stereoInvFun (norm_eq_of_mem_sphere v) (L x) : E3) := by
  classical
  let V := (ℝ ∙ (v : E3))ᗮ
  let b : OrthonormalBasis (Fin 2) ℝ V :=
    OrthonormalBasis.fromOrthogonalSpanSingleton 2 (ne_zero_of_mem_unit_sphere v)
  let c : Module.Basis (Fin 2) ℝ V := b.toBasis.map L.toLinearEquiv
  have hc (i : Fin 2) : c i = L (b i) := by simp [c]
  have hdim : Module.finrank ℝ V = Fintype.card (Fin 2) :=
    Module.finrank_eq_card_basis b.toBasis
  let q := gramSchmidtOrthonormalBasis hdim c
  have hq (i : Fin 2) : q i = ‖gramSchmidt ℝ c i‖⁻¹ • gramSchmidt ℝ c i := by
    rw [gramSchmidtOrthonormalBasis_apply hdim]
    · rfl
    · intro hz
      have hn := gramSchmidtNormed_unit_length i c.linearIndependent
      rw [hz, norm_zero] at hn
      exact zero_ne_one hn
  have hdiag (i : Fin 2) : 0 < q.repr (L (b i)) i := by
    have hn : 0 < ‖gramSchmidt ℝ c i‖ :=
      norm_pos_iff.mpr (gramSchmidt_ne_zero i c.linearIndependent)
    have hsum : ⟪gramSchmidt ℝ c i,
        ∑ j ∈ Finset.Iio i,
          (⟪gramSchmidt ℝ c j, c i⟫_ℝ / ‖gramSchmidt ℝ c j‖ ^ 2) •
            gramSchmidt ℝ c j⟫_ℝ = 0 := by
      rw [inner_sum]
      apply Finset.sum_eq_zero
      intro j hj
      rw [real_inner_smul_right,
        gramSchmidt_orthogonal ℝ c (ne_of_gt (Finset.mem_Iio.mp hj)), mul_zero]
    have hinner : ⟪gramSchmidt ℝ c i, c i⟫_ℝ = ‖gramSchmidt ℝ c i‖ ^ 2 := by
      have hh := congrArg (fun z : V => ⟪gramSchmidt ℝ c i, z⟫_ℝ)
        (gramSchmidt_def'' ℝ c i)
      change ⟪gramSchmidt ℝ c i, c i⟫_ℝ =
        ⟪gramSchmidt ℝ c i, gramSchmidt ℝ c i +
          ∑ j ∈ Finset.Iio i,
            (⟪gramSchmidt ℝ c j, c i⟫_ℝ / ‖gramSchmidt ℝ c j‖ ^ 2) •
              gramSchmidt ℝ c j⟫_ℝ at hh
      rw [inner_add_right, hsum, add_zero, real_inner_self_eq_norm_sq] at hh
      exact hh
    rw [q.repr_apply_apply, hq, ← hc, real_inner_smul_left, hinner]
    exact mul_pos (inv_pos.mpr hn) (sq_pos_of_pos hn)
  have htriangle : q.repr (L (b 0)) 1 = 0 := by
    simpa only [hc] using
      gramSchmidtOrthonormalBasis_inv_triangular' hdim c (show (0 : Fin 2) < 1 by decide)
  let α := q.repr (L (b 0)) 0
  let β := q.repr (L (b 1)) 0
  let γ := q.repr (L (b 1)) 1
  have hα : 0 < α := hdiag 0
  have hγ : 0 < γ := hdiag 1
  let O : V ≃ₗᵢ[ℝ] V := b.repr.trans q.repr.symm
  have hdecomp (x : V) : b.repr x 0 • b 0 + b.repr x 1 • b 1 = x := by
    simpa only [Fin.sum_univ_two] using b.sum_repr x
  have hcoord0 (s t : ℝ) : b.repr (s • b 0 + t • b 1) 0 = s := by simp
  have hcoord1 (s t : ℝ) : b.repr (s • b 0 + t • b 1) 1 = t := by simp
  have hL0 (x : V) : q.repr (L x) 0 = α * b.repr x 0 + β * b.repr x 1 := by
    have hh := congrArg (fun y : V => q.repr (L y) 0) (hdecomp x)
    simp only [map_add, map_smul, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] at hh
    change b.repr x 0 * α + b.repr x 1 * β = q.repr (L x) 0 at hh
    rw [mul_comm (b.repr x 0) α, mul_comm (b.repr x 1) β] at hh
    exact hh.symm
  have hL1 (x : V) : q.repr (L x) 1 = γ * b.repr x 1 := by
    have hh := congrArg (fun y : V => q.repr (L y) 1) (hdecomp x)
    simp only [map_add, map_smul, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
      htriangle, mul_zero, zero_add] at hh
    change b.repr x 1 * γ = q.repr (L x) 1 at hh
    rw [mul_comm (b.repr x 1) γ] at hh
    exact hh.symm
  let d0 : ℝ → ℝ := fun t => 1 + Real.smoothTransition t * (α - 1)
  let d1 : ℝ → ℝ := fun t => 1 + Real.smoothTransition t * (γ - 1)
  have hconv (a : ℝ) (ha : 0 < a) (t : ℝ) :
      0 < 1 + Real.smoothTransition t * (a - 1) := by
    have ht0 := Real.smoothTransition.nonneg t
    have ht1 := Real.smoothTransition.le_one t
    by_cases ht : Real.smoothTransition t = 1
    · rw [ht, one_mul]
      linarith only [ha]
    · have hlt : Real.smoothTransition t < 1 := lt_of_le_of_ne ht1 ht
      have hp := mul_nonneg ht0 ha.le
      nlinarith only [hlt, hp]
  have hd0 (t : ℝ) : 0 < d0 t := hconv α hα t
  have hd1 (t : ℝ) : 0 < d1 t := hconv γ hγ t
  have hd0sm : ContDiff ℝ ∞ d0 :=
    contDiff_const.add (Real.smoothTransition.contDiff.mul contDiff_const)
  have hd1sm : ContDiff ℝ ∞ d1 :=
    contDiff_const.add (Real.smoothTransition.contDiff.mul contDiff_const)
  let R : ℝ → V → V := fun t x =>
    (d0 t * b.repr x 0 + Real.smoothTransition t * β * b.repr x 1) • b 0 +
      (d1 t * b.repr x 1) • b 1
  let Ri : ℝ → V → V := fun t x =>
    (b.repr x 0 / d0 t -
      Real.smoothTransition t * β * b.repr x 1 / (d0 t * d1 t)) • b 0 +
        (b.repr x 1 / d1 t) • b 1
  have hleft (t : ℝ) (x : V) : Ri t (R t x) = x := by
    rw [← hdecomp x]
    simp only [Ri, R, hcoord0, hcoord1]
    congr 2
    · field_simp [(hd0 t).ne', (hd1 t).ne']
      ring
    · field_simp [(hd0 t).ne', (hd1 t).ne']
  have hright (t : ℝ) (x : V) : R t (Ri t x) = x := by
    rw [← hdecomp x]
    simp only [Ri, R, hcoord0, hcoord1]
    congr 2
    · field_simp [(hd0 t).ne', (hd1 t).ne']
      ring
    · field_simp [(hd0 t).ne', (hd1 t).ne']
  have hRzero (x : V) : R 0 x = x := by
    simpa only [R, d0, d1, Real.smoothTransition.zero_of_nonpos le_rfl,
      zero_mul, add_zero, one_mul] using hdecomp x
  have hRone (x : V) : O (R 1 x) = L x := by
    apply q.repr.injective
    change q.repr (q.repr.symm (b.repr (R 1 x))) = q.repr (L x)
    rw [q.repr.apply_symm_apply]
    ext i
    fin_cases i
    · change b.repr (R 1 x) 0 = q.repr (L x) 0
      dsimp only [R]
      rw [hcoord0, hL0]
      dsimp only [d0]
      rw [Real.smoothTransition.one_of_one_le le_rfl]
      ring
    · change b.repr (R 1 x) 1 = q.repr (L x) 1
      dsimp only [R]
      rw [hcoord1, hL1]
      dsimp only [d1]
      rw [Real.smoothTransition.one_of_one_le le_rfl]
      ring
  have hcoordSm (i : Fin 2) :
      ContDiff ℝ ∞ (fun p : ℝ × (V × ℝ) => b.repr p.2.1 i) :=
    (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp
      (b.repr.toContinuousLinearEquiv.contDiff.comp contDiff_snd.fst)
  have hRsm : ContDiff ℝ ∞ (fun p : ℝ × (V × ℝ) => R p.1 p.2.1) :=
    (((hd0sm.comp contDiff_fst).mul (hcoordSm 0)).add
      (((Real.smoothTransition.contDiff.comp contDiff_fst).mul contDiff_const).mul
        (hcoordSm 1))).smul contDiff_const |>.add
          (((hd1sm.comp contDiff_fst).mul (hcoordSm 1)).smul contDiff_const)
  have hRism : ContDiff ℝ ∞ (fun p : ℝ × (V × ℝ) => Ri p.1 p.2.1) :=
    (((hcoordSm 0).div (hd0sm.comp contDiff_fst) (fun p => (hd0 p.1).ne')).sub
      ((((Real.smoothTransition.contDiff.comp contDiff_fst).mul contDiff_const).mul
        (hcoordSm 1)).div
          ((hd0sm.comp contDiff_fst).mul (hd1sm.comp contDiff_fst))
          (fun p => mul_ne_zero (hd0 p.1).ne' (hd1 p.1).ne'))).smul contDiff_const |>.add
            (((hcoordSm 1).div (hd1sm.comp contDiff_fst)
              (fun p => (hd1 p.1).ne')).smul contDiff_const)
  let e : OpenPartialHomeomorph (ℝ × (V × ℝ)) (ℝ × (V × ℝ)) := {
    toFun := fun p => (p.1, (R p.1 p.2.1, p.2.2))
    invFun := fun p => (p.1, (Ri p.1 p.2.1, p.2.2))
    source := univ ×ˢ (univ ×ˢ Ioi 0)
    target := univ ×ˢ (univ ×ˢ Ioi 0)
    map_source' := fun _ hp => hp
    map_target' := fun _ hp => hp
    left_inv' := fun p _ => by simp only [hleft]
    right_inv' := fun p _ => by simp only [hright]
    open_source := isOpen_univ.prod (isOpen_univ.prod isOpen_Ioi)
    open_target := isOpen_univ.prod (isOpen_univ.prod isOpen_Ioi)
    continuousOn_toFun :=
      (contDiff_fst.prodMk (hRsm.prodMk contDiff_snd.snd)).continuous.continuousOn
    continuousOn_invFun :=
      (contDiff_fst.prodMk (hRism.prodMk contDiff_snd.snd)).continuous.continuousOn }
  have he : ContDiffOn ℝ ∞ e e.source :=
    (contDiff_fst.prodMk (hRsm.prodMk contDiff_snd.snd)).contDiffOn
  have hei : ContDiffOn ℝ ∞ e.symm e.target :=
    (contDiff_fst.prodMk (hRism.prodMk contDiff_snd.snd)).contDiffOn
  have hsource : Icc (-1 : ℝ) 2 ×ˢ (K ×ˢ ({1} : Set ℝ)) ⊆ e.source := by
    rintro ⟨t, x, r⟩ ⟨_ht, _hx, hr⟩
    have hr1 : r = 1 := hr
    subst r
    exact ⟨mem_univ _, mem_univ _, show (0 : ℝ) < 1 from zero_lt_one⟩
  obtain ⟨Φ, hΦ, hΦzero, hΦtrack, ⟨C, hC, hCs, hfix⟩, hlinear⟩ :=
    exists_ambient_isotopy_of_chart e he hei (fun _ _ => rfl)
      (ContinuousLinearMap.snd ℝ V ℝ) (fun _ _ => rfl)
      (hK.prod isCompact_singleton) (show (0 : ℝ) ∈ Ioo (-1) 2 by norm_num) hsource
  have hCpos : C ⊆ univ ×ˢ Ioi (0 : ℝ) := by
    rintro p hp
    obtain ⟨q, hq, rfl⟩ := hCs hp
    exact hq.2
  obtain ⟨Ψ, _hΨ, _hΨzero, hnorm, htrack, _hsupport⟩ :=
    exists_radialStereo_transport_isotopy (v : E3) (norm_eq_of_mem_sphere v)
      Φ hΦ hΦzero hlinear hC hCpos hfix
  have hΦone (x : V) (hx : x ∈ K) : (Φ 1 (x, 1)).1 = R 1 x := by
    have hh := hΦtrack (x, 1) ⟨hx, rfl⟩ 1 (by norm_num)
    change Φ 1 (R 0 x, 1) = (R 1 x, 1) at hh
    rw [hRzero] at hh
    exact congrArg Prod.fst hh
  let n : E3 →L[ℝ] ℝ := innerSL ℝ (v : E3)
  have hv : ⟪(v : E3), v⟫_ℝ = 1 := by
    rw [real_inner_self_eq_norm_sq, norm_eq_of_mem_sphere v, one_pow]
  have hnV (x : V) : n (x : E3) = 0 :=
    Submodule.mem_orthogonal_singleton_iff_inner_right.mp x.property
  let P0 : E3 →L[ℝ] E3 := ContinuousLinearMap.id ℝ E3 - n.smulRight (v : E3)
  have hP0 (y : E3) : P0 y ∈ V := by
    apply Submodule.mem_orthogonal_singleton_iff_inner_right.mpr
    change ⟪(v : E3), y - n y • (v : E3)⟫_ℝ = 0
    rw [inner_sub_right, real_inner_smul_right, hv, mul_one]
    exact sub_self _
  let P : E3 →L[ℝ] V := P0.codRestrict V hP0
  have hPV (x : V) : P (x : E3) = x := by
    apply Subtype.ext
    change (x : E3) - n (x : E3) • (v : E3) = x
    rw [hnV, zero_smul, sub_zero]
  have hPv : P (v : E3) = 0 := by
    apply Subtype.ext
    change (v : E3) - n (v : E3) • (v : E3) = 0
    rw [show n (v : E3) = 1 from hv, one_smul, sub_self]
  have hsplit (y : E3) : (P y : E3) + n y • (v : E3) = y := by
    change (y - n y • (v : E3)) + n y • (v : E3) = y
    exact sub_add_cancel _ _
  let extend (J : V ≃ₗᵢ[ℝ] V) : E3 →L[ℝ] E3 :=
    V.subtypeL.comp (J.toContinuousLinearEquiv.toContinuousLinearMap.comp P) +
      n.smulRight (v : E3)
  have hextV (J : V ≃ₗᵢ[ℝ] V) (x : V) : extend J (x : E3) = (J x : E3) := by
    change (J (P (x : E3)) : E3) + n (x : E3) • (v : E3) = J x
    rw [hPV, hnV, zero_smul, add_zero]
  have hextv (J : V ≃ₗᵢ[ℝ] V) : extend J (v : E3) = v := by
    change (J (P (v : E3)) : E3) + n (v : E3) • (v : E3) = v
    rw [hPv, map_zero, Submodule.coe_zero, show n (v : E3) = 1 from hv,
      one_smul, zero_add]
  have hextright (J : V ≃ₗᵢ[ℝ] V) (y : E3) : extend J (extend J.symm y) = y := by
    change extend J ((J.symm (P y) : E3) + n y • (v : E3)) = y
    rw [map_add, map_smul, hextV, hextv, J.apply_symm_apply]
    exact hsplit y
  have hextnorm (J : V ≃ₗᵢ[ℝ] V) (y : E3) : ‖extend J y‖ = ‖y‖ := by
    have horth (x : V) : ⟪(x : E3), n y • (v : E3)⟫_ℝ = 0 := by
      rw [real_inner_smul_right, real_inner_comm]
      change n y * n (x : E3) = 0
      rw [hnV, mul_zero]
    have hnormJ : ‖(J (P y) : E3)‖ = ‖(P y : E3)‖ := J.norm_map (P y)
    have h1 := norm_add_sq_real (J (P y) : E3) (n y • (v : E3))
    have h2 := norm_add_sq_real (P y : E3) (n y • (v : E3))
    rw [horth, mul_zero, add_zero, hnormJ] at h1
    rw [horth, mul_zero, add_zero, hsplit] at h2
    change ‖(J (P y) : E3) + n y • (v : E3)‖ = ‖y‖
    nlinarith only [h1, h2, norm_nonneg ((J (P y) : E3) + n y • (v : E3)),
      norm_nonneg y]
  let J : E3 ≃L[ℝ] E3 := ContinuousLinearEquiv.equivOfInverse
    (extend O) (extend O.symm) (hextright O.symm) (hextright O)
  have hJplane (x : V) : J (x : E3) = (O x : E3) := hextV O x
  have hJpole : J (v : E3) = v := hextv O
  have hJstereo (x : V) : J (stereoInvFun (norm_eq_of_mem_sphere v) x : E3) =
      (stereoInvFun (norm_eq_of_mem_sphere v) (O x) : E3) := by
    rw [stereoInvFun_apply, stereoInvFun_apply, map_smul, map_add, map_smul, map_smul,
      hJplane, hJpole, O.norm_map]
  refine ⟨(Ψ 1).trans J.toDiffeomorph, ?_, ?_⟩
  · intro y
    change ‖extend O (Ψ 1 y)‖ = ‖y‖
    rw [hextnorm, hnorm]
  · intro x hx
    change J (Ψ 1 (stereoInvFun (norm_eq_of_mem_sphere v) x : E3)) = _
    rw [htrack, hΦone x hx, hJstereo, hRone]

end PoincareConjecture.M25.Topology3D
