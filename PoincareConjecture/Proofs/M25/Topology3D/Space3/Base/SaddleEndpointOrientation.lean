import PoincareConjecture.Proofs.M25.Topology3D.Space3.Base.SaddleArcOrientation
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Base.SaddleChartOrientation










set_option autoImplicit false

open Set Filter Function
open scoped ContDiff Manifold InnerProductSpace Matrix Topology

namespace PoincareConjecture.M25.Topology3D.SaddleOrientation

private theorem height_columns_from_quadratic
    (A : (ℝ × ℝ) → E3) (H : E3 →L[ℝ] ℝ) (c : ℝ) (s : ℝ × ℝ)
    (hA : DifferentiableAt ℝ A s)
    (hform : (fun p => H (A p)) =ᶠ[𝓝 s]
      (fun p => c + p.1 ^ 2 - p.2 ^ 2)) :
    H (fderiv ℝ A s (1, 0)) = 2 * s.1 ∧
      H (fderiv ℝ A s (0, 1)) = -(2 * s.2) := by
  have hd1 : HasFDerivAt (fun p : ℝ × ℝ => p.1)
      (ContinuousLinearMap.fst ℝ ℝ ℝ) s :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt
  have hd2 : HasFDerivAt (fun p : ℝ × ℝ => p.2)
      (ContinuousLinearMap.snd ℝ ℝ ℝ) s :=
    (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt
  have hQ := ((hd1.pow 2).const_add c).sub (hd2.pow 2)
  have hHA := H.hasFDerivAt.comp s hA.hasFDerivAt
  have heq := hHA.fderiv.symm.trans (hform.fderiv_eq.trans hQ.fderiv)
  constructor
  · have h := congrArg (fun T : (ℝ × ℝ) →L[ℝ] ℝ => T (1, 0)) heq
    simpa [nsmul_eq_mul, smul_eq_mul] using h
  · have h := congrArg (fun T : (ℝ × ℝ) →L[ℝ] ℝ => T (0, 1)) heq
    simpa [nsmul_eq_mul, smul_eq_mul] using h

private theorem hyperbola_tangent_scalar
    (s v : ℝ × ℝ) (hy : s.2 ≠ 0) (hv : v ≠ 0)
    (htan : s.1 * v.1 - s.2 * v.2 = 0) :
    ∃ lambda : ℝ, lambda ≠ 0 ∧ v = lambda • (s.2, s.1) := by
  let lambda := v.1 / s.2
  have h1 : lambda * s.2 = v.1 := div_mul_cancel₀ _ hy
  have h2 : lambda * s.1 = v.2 := by
    apply mul_right_cancel₀ hy
    calc
      (lambda * s.1) * s.2 = s.1 * (lambda * s.2) := by ring
      _ = s.1 * v.1 := by rw [h1]
      _ = s.2 * v.2 := sub_eq_zero.mp htan
      _ = v.2 * s.2 := mul_comm _ _
  have heq : v = lambda • (s.2, s.1) := Prod.ext h1.symm h2.symm
  refine ⟨lambda, ?_, heq⟩
  intro hz
  apply hv
  rw [heq, hz, zero_smul]

private theorem height_constraint_of_coordinate_derivative
    (xi : ℝ → ℝ × ℝ) (v : ℝ × ℝ) (t0 c z : ℝ)
    (hxi : HasDerivAt xi v t0)
    (hheight : (fun t => c + (xi t).1 ^ 2 - (xi t).2 ^ 2) =ᶠ[𝓝 t0]
      (fun _ => z)) :
    (xi t0).1 * v.1 - (xi t0).2 * v.2 = 0 := by
  have hx : HasDerivAt (fun t => (xi t).1) v.1 t0 :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt t0 hxi
  have hy : HasDerivAt (fun t => (xi t).2) v.2 t0 :=
    (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt t0 hxi
  have hd := ((hx.pow 2).const_add c).sub (hy.pow 2)
  have hzder := hheight.deriv_eq
  rw [deriv_const] at hzder
  have heq := hd.deriv.symm.trans hzder
  norm_num at heq
  linarith

private theorem radius_derivative_of_tangent_scalar
    (xi : ℝ → ℝ × ℝ) (v : ℝ × ℝ) (t0 lambda : ℝ)
    (hxi : HasDerivAt xi v t0)
    (hv : v = lambda • ((xi t0).2, (xi t0).1)) :
    HasDerivAt (fun t => (xi t).1 ^ 2 + (xi t).2 ^ 2)
      (4 * lambda * (xi t0).1 * (xi t0).2) t0 := by
  have hx : HasDerivAt (fun t => (xi t).1) v.1 t0 :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt t0 hxi
  have hy : HasDerivAt (fun t => (xi t).2) v.2 t0 :=
    (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt t0 hxi
  have hd : HasDerivAt (fun t => (xi t).1 ^ 2 + (xi t).2 ^ 2)
      (2 * (xi t0).1 * v.1 + 2 * (xi t0).2 * v.2) t0 := by
    convert (hx.pow 2).add (hy.pow 2) using 1 <;> first | rfl | norm_num
  refine hd.congr_deriv ?_
  rw [hv]
  change 2 * (xi t0).1 * (lambda * (xi t0).2) +
    2 * (xi t0).2 * (lambda * (xi t0).1) =
      4 * lambda * (xi t0).1 * (xi t0).2
  ring

private theorem morse_disc_membership
    {X : Type*} [TopologicalSpace X]
    (e : OpenPartialHomeomorph X (ℝ × ℝ)) (r : ℝ)
    (hdisc : {s : ℝ × ℝ | s.1 ^ 2 + s.2 ^ 2 ≤ r ^ 2} ⊆ e.target)
    (p : X) (hp : p ∈ e.source) :
    (p ∈ e.symm '' {s : ℝ × ℝ | s.1 ^ 2 + s.2 ^ 2 < r ^ 2} ↔
      (e p).1 ^ 2 + (e p).2 ^ 2 < r ^ 2) ∧
    (p ∈ e.symm '' {s : ℝ × ℝ | s.1 ^ 2 + s.2 ^ 2 ≤ r ^ 2} ↔
      (e p).1 ^ 2 + (e p).2 ^ 2 ≤ r ^ 2) := by
  constructor
  · constructor
    · rintro ⟨s, hs, rfl⟩
      rw [e.right_inv (hdisc (show s.1 ^ 2 + s.2 ^ 2 ≤ r ^ 2 from le_of_lt hs))]
      exact hs
    · intro hs
      exact ⟨e p, hs, e.left_inv hp⟩
  · constructor
    · rintro ⟨s, hs, rfl⟩
      rw [e.right_inv (hdisc hs)]
      exact hs
    · intro hs
      exact ⟨e p, hs, e.left_inv hp⟩



theorem saddle_arc_opposite_port_products
    (psi : UnitTwoSphere × ℝ → E3) (hpsi : IsCollarEmbedding psi)
    (rho : E3 → ℝ)
    (hrho : ContDiffOn ℝ ∞ rho (psi '' (univ ×ˢ Ioo (-1) 1)))
    (hrhopsi : ∀ p ∈ (univ ×ˢ Ioo (-1) 1 : Set (UnitTwoSphere × ℝ)),
      rho (psi p) = p.2)
    (hrhonz : ∀ y ∈ psi '' (univ ×ˢ Ioo (-1) 1), fderiv ℝ rho y ≠ 0)
    (u : E3) (c z : ℝ)
    (M : OpenPartialHomeomorph (ℝ × ℝ) UnitTwoSphere)
    (hMs : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 2) ∞ M M.source)
    (hMi : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ × ℝ) ∞ M.symm M.target)
    (hheight : ∀ s ∈ M.source,
      ⟪u, psi (M s, 0)⟫_ℝ = c + s.1 ^ 2 - s.2 ^ 2)
    (W : Set (ℝ × ℝ)) (hW : IsPreconnected W) (hWsource : W ⊆ M.source)
    (alpha : ℝ → UnitTwoSphere)
    (ha : ContMDiff 𝓘(ℝ, ℝ) (𝓡 2) ∞ alpha)
    (hai : ∀ t, Function.Injective (mfderiv 𝓘(ℝ, ℝ) (𝓡 2) alpha t))
    (hlevel : ∀ t, ⟪u, psi (alpha t, 0)⟫_ℝ = z)
    (hreg : ∀ t, mfderiv (𝓡 2) 𝓘(ℝ, ℝ)
      (fun p : UnitTwoSphere => ⟪u, psi (p, 0)⟫_ℝ) (alpha t) ≠ 0)
    (r eta : ℝ) (heta : 0 < eta)
    (hdisc : {s : ℝ × ℝ | s.1 ^ 2 + s.2 ^ 2 ≤ r ^ 2} ⊆ M.source)
    (hend : ∀ t ∈ ({0, 1} : Set ℝ), alpha t ∈ M.target)
    (hWend : ∀ t ∈ ({0, 1} : Set ℝ), M.symm (alpha t) ∈ W)
    (hwall : ∀ t ∈ ({0, 1} : Set ℝ),
      (M.symm (alpha t)).1 ^ 2 + (M.symm (alpha t)).2 ^ 2 = r ^ 2)
    (hport : ∀ t ∈ ({0, 1} : Set ℝ),
      (M.symm (alpha t)).1 ≠ 0 ∧ (M.symm (alpha t)).2 ≠ 0)
    (houtside : Disjoint (alpha '' Ioo (0 : ℝ) 1)
      (M '' {s : ℝ × ℝ | s.1 ^ 2 + s.2 ^ 2 ≤ r ^ 2}))
    (hafter : ∀ t ∈ Ioo (1 : ℝ) (1 + eta),
      alpha t ∈ M '' {s : ℝ × ℝ | s.1 ^ 2 + s.2 ^ 2 < r ^ 2}) :
    ((M.symm (alpha 0)).1 * (M.symm (alpha 0)).2) *
      ((M.symm (alpha 1)).1 * (M.symm (alpha 1)).2) < 0 := by
  let A : (ℝ × ℝ) → E3 := fun s => psi (M s, 0)
  let Gamma : ℝ → E3 := fun t => psi (alpha t, 0)
  let xi : ℝ → ℝ × ℝ := M.symm ∘ alpha
  let g : ℝ → ℝ := fun t => (xi t).1 ^ 2 + (xi t).2 ^ 2
  let J : ℝ → ℝ := fun t =>
    ⟪heightCrossMap u (gradient rho (Gamma t)), deriv Gamma t⟫_ℝ
  let Csign : (ℝ × ℝ) → ℝ := fun s =>
    WithLp.ofLp (gradient rho (A s)) ⬝ᵥ
      (WithLp.ofLp (fderiv ℝ A s (1, 0)) ⨯₃
        WithLp.ofLp (fderiv ℝ A s (0, 1)))
  obtain ⟨_hJcont, hJne, hJprod⟩ :=
    collar_arc_orientation psi hpsi rho hrho hrhopsi hrhonz u z alpha ha hai hlevel hreg
  obtain ⟨hA, _hAi, hCcont, hCne, horth⟩ :=
    collar_chart_orientation psi hpsi rho hrho hrhopsi hrhonz M hMs hMi
  have hvelocity (t : ℝ) : deriv Gamma t ≠ 0 := by
    intro hz
    apply hJne t
    change J t = 0
    simp only [J, hz, inner_zero_right]
  have hlocal (t : ℝ) (ht : t ∈ ({0, 1} : Set ℝ)) :
      ∀ᶠ s in 𝓝 t, alpha s ∈ M.target :=
    ha.continuous.continuousAt.eventually (M.open_target.mem_nhds (hend t ht))
  have hsource (t : ℝ) (ht : t ∈ ({0, 1} : Set ℝ)) : xi t ∈ M.source :=
    M.map_target (hend t ht)
  have hfactor (t : ℝ) (ht : t ∈ ({0, 1} : Set ℝ)) :
      ∃ lambda : ℝ, lambda ≠ 0 ∧
        deriv Gamma t = lambda •
          ((xi t).2 • fderiv ℝ A (xi t) (1, 0) +
            (xi t).1 • fderiv ℝ A (xi t) (0, 1)) ∧
        HasDerivAt g (4 * lambda * (xi t).1 * (xi t).2) t := by
    have hxi : ContDiffAt ℝ ∞ xi t :=
      ((hMi.contMDiffAt (M.open_target.mem_nhds (hend t ht))).comp t
        ha.contMDiffAt).contDiffAt
    have hrec : Gamma =ᶠ[𝓝 t] A ∘ xi := by
      filter_upwards [hlocal t ht] with s hs
      change psi (alpha s, 0) = psi (M (M.symm (alpha s)), 0)
      rw [M.right_inv hs]
    have hxiD := (hxi.differentiableAt (by simp)).hasDerivAt
    have hAd : DifferentiableAt ℝ A (xi t) :=
      (hA.contDiffAt (M.open_source.mem_nhds (hsource t ht))).differentiableAt (by simp)
    have hchain := hAd.hasFDerivAt.comp_hasDerivAt t hxiD
    have hvel : deriv Gamma t = fderiv ℝ A (xi t) (deriv xi t) :=
      hrec.deriv_eq.trans hchain.deriv
    have hxi_ne : deriv xi t ≠ 0 := by
      intro hz
      apply hvelocity t
      rw [hvel, hz, map_zero]
    have hheightNear : (fun s => c + (xi s).1 ^ 2 - (xi s).2 ^ 2) =ᶠ[𝓝 t]
        (fun _ => z) := by
      filter_upwards [hlocal t ht] with s hs
      rw [← hheight (xi s) (M.map_target hs)]
      change ⟪u, psi (M (M.symm (alpha s)), 0)⟫_ℝ = z
      rw [M.right_inv hs]
      exact hlevel s
    have htan := height_constraint_of_coordinate_derivative xi (deriv xi t) t c z
      hxiD hheightNear
    obtain ⟨lambda, hlambda, heq⟩ := hyperbola_tangent_scalar
      (xi t) (deriv xi t) (hport t ht).2 hxi_ne htan
    refine ⟨lambda, hlambda, ?_,
      radius_derivative_of_tangent_scalar xi (deriv xi t) t lambda hxiD heq⟩
    rw [hvel, heq, map_smul]
    apply congrArg (fun v : E3 => lambda • v)
    have hp : ((xi t).2, (xi t).1) =
        (xi t).2 • ((1 : ℝ), 0) + (xi t).1 • ((0 : ℝ), 1) := by
      ext <;> simp
    rw [hp, map_add, map_smul, map_smul]
  have hgram (t : ℝ) (ht : t ∈ ({0, 1} : Set ℝ)) (lambda : ℝ)
      (hvel : deriv Gamma t = lambda •
        ((xi t).2 • fderiv ℝ A (xi t) (1, 0) +
          (xi t).1 • fderiv ℝ A (xi t) (0, 1))) :
      ∃ L B : ℝ, 0 < L ∧ 0 < B ∧
        L * J t = 2 * lambda * Csign (xi t) * B := by
    let coord := EuclideanSpace.equiv (Fin 3) ℝ
    let n := coord (gradient rho (A (xi t)))
    let w := coord u
    let e1 := coord (fderiv ℝ A (xi t) (1, 0))
    let e2 := coord (fderiv ℝ A (xi t) (0, 1))
    let L := e1 ⨯₃ e2
    let B := (xi t).2 • e1 + (xi t).1 • e2
    have hBform : coord (deriv Gamma t) = lambda • B := by
      rw [hvel, map_smul, map_add, map_smul, map_smul]
    have hBne : B ≠ 0 := by
      intro hz
      apply hvelocity t
      apply coord.injective
      rw [hBform, hz, smul_zero, map_zero]
    have hLne : L ≠ 0 := by
      intro hz
      apply hCne (xi t) (hsource t ht)
      change n ⬝ᵥ L = 0
      rw [hz, dotProduct_zero]
    have hn1 : n ⬝ᵥ e1 = 0 := by
      have hh := (horth (xi t) (hsource t ht)).1
      rw [EuclideanSpace.inner_eq_star_dotProduct, star_trivial] at hh
      exact (dotProduct_comm n e1).trans hh
    have hn2 : n ⬝ᵥ e2 = 0 := by
      have hh := (horth (xi t) (hsource t ht)).2
      rw [EuclideanSpace.inner_eq_star_dotProduct, star_trivial] at hh
      exact (dotProduct_comm n e2).trans hh
    have hheightNear : (fun s => ⟪u, A s⟫_ℝ) =ᶠ[𝓝 (xi t)]
        (fun s => c + s.1 ^ 2 - s.2 ^ 2) := by
      filter_upwards [M.open_source.mem_nhds (hsource t ht)] with s hs
      exact hheight s hs
    have hAd : DifferentiableAt ℝ A (xi t) :=
      (hA.contDiffAt (M.open_source.mem_nhds (hsource t ht))).differentiableAt (by simp)
    have hcols := height_columns_from_quadratic A (InnerProductSpace.toDual ℝ E3 u)
      c (xi t) hAd hheightNear
    have hu1 : w ⬝ᵥ e1 = 2 * (xi t).1 := by
      have hh := hcols.1
      change ⟪u, fderiv ℝ A (xi t) (1, 0)⟫_ℝ = _ at hh
      rw [EuclideanSpace.inner_eq_star_dotProduct, star_trivial] at hh
      exact (dotProduct_comm w e1).trans hh
    have hu2 : w ⬝ᵥ e2 = -(2 * (xi t).2) := by
      have hh := hcols.2
      change ⟪u, fderiv ℝ A (xi t) (0, 1)⟫_ℝ = _ at hh
      rw [EuclideanSpace.inner_eq_star_dotProduct, star_trivial] at hh
      exact (dotProduct_comm w e2).trans hh
    have hnormal : gradient rho (Gamma t) = gradient rho (A (xi t)) := by
      change gradient rho (psi (alpha t, 0)) =
        gradient rho (psi (M (M.symm (alpha t)), 0))
      rw [M.right_inv (hend t ht)]
    have hJform : J t = n ⬝ᵥ (w ⨯₃ (lambda • B)) := by
      dsimp only [J]
      rw [hnormal, heightCrossMap_apply, EuclideanSpace.inner_eq_star_dotProduct,
        star_trivial]
      change coord (deriv Gamma t) ⬝ᵥ (n ⨯₃ w) = _
      rw [triple_product_permutation, hBform]
    refine ⟨L ⬝ᵥ L, B ⬝ᵥ B, dot_self_pos_of_ne_zero L hLne,
      dot_self_pos_of_ne_zero B hBne, ?_⟩
    rw [hJform]
    exact saddle_endpoint_gram_identity n w e1 e2 (xi t).1 (xi t).2 lambda
      hn1 hn2 hu1 hu2
  have h0 : (0 : ℝ) ∈ ({0, 1} : Set ℝ) := by simp
  have h1 : (1 : ℝ) ∈ ({0, 1} : Set ℝ) := by simp
  obtain ⟨lambda0, hlambda0, hvel0, hd0⟩ := hfactor 0 h0
  obtain ⟨lambda1, hlambda1, hvel1, hd1⟩ := hfactor 1 h1
  obtain ⟨L0, B0, hL0, hB0, heq0⟩ := hgram 0 h0 lambda0 hvel0
  obtain ⟨L1, B1, hL1, hB1, heq1⟩ := hgram 1 h1 lambda1 hvel1
  have hCprod : 0 < Csign (xi 0) * Csign (xi 1) :=
    mul_pos_of_connected_nonzero hW (hCcont.mono hWsource)
      (fun s hs => hCne s (hWsource hs)) (hWend 0 h0) (hWend 1 h1)
  have hlambda : 0 < lambda0 * lambda1 :=
    endpoint_lambdas_same_sign L0 L1 B0 B1 (J 0) (J 1)
      (Csign (xi 0)) (Csign (xi 1)) lambda0 lambda1
      hL0 hL1 hB0 hB1 hJprod hCprod heq0 heq1
  have hd0ne : 4 * lambda0 * (xi 0).1 * (xi 0).2 ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hlambda0)
      (hport 0 h0).1) (hport 0 h0).2
  have hd1ne : 4 * lambda1 * (xi 1).1 * (xi 1).2 ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hlambda1)
      (hport 1 h1).1) (hport 1 h1).2
  let V : Set UnitTwoSphere := M '' {s : ℝ × ℝ | s.1 ^ 2 + s.2 ^ 2 < r ^ 2}
  let C : Set UnitTwoSphere := M '' {s : ℝ × ℝ | s.1 ^ 2 + s.2 ^ 2 ≤ r ^ 2}
  have hmem (t : ℝ) (ht : alpha t ∈ M.target) :
      (alpha t ∈ V ↔ g t < r ^ 2) ∧ (alpha t ∈ C ↔ g t ≤ r ^ 2) :=
    morse_disc_membership M.symm r hdisc (alpha t) ht
  have hboundary0 : g 0 = r ^ 2 := hwall 0 h0
  have hboundary1 : g 1 = r ^ 2 := hwall 1 h1
  have hright0 : ∀ᶠ t in 𝓝[>] (0 : ℝ), g 0 ≤ g (0 + t) := by
    have hsmall : ∀ᶠ t : ℝ in 𝓝[>] 0, t < 1 :=
      nhdsWithin_le_nhds (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))
    filter_upwards [(hlocal 0 h0).filter_mono nhdsWithin_le_nhds,
      hsmall, self_mem_nhdsWithin] with t ht ht1 ht0
    have hnot : alpha t ∉ C := by
      intro hc
      exact disjoint_left.mp houtside ⟨t, ⟨ht0, ht1⟩, rfl⟩ hc
    have hgt : r ^ 2 < g t := lt_of_not_ge (fun h => hnot ((hmem t ht).2.mpr h))
    simpa only [zero_add, hboundary0] using hgt.le
  have hshift : Tendsto (fun t : ℝ => 1 + t) (𝓝 0) (𝓝 1) := by
    have hc : Continuous (fun t : ℝ => 1 + t) := continuous_const.add continuous_id
    simpa only [add_zero] using (hc.continuousAt (x := (0 : ℝ))).tendsto
  have hright1 : ∀ᶠ t in 𝓝[>] (0 : ℝ), g (1 + t) ≤ g 1 := by
    have hsmall : ∀ᶠ t : ℝ in 𝓝[>] 0, t < eta :=
      nhdsWithin_le_nhds (Iio_mem_nhds heta)
    filter_upwards [(hshift.eventually (hlocal 1 h1)).filter_mono nhdsWithin_le_nhds,
      hsmall, self_mem_nhdsWithin] with t ht hteta ht0
    change 0 < t at ht0
    have hin : alpha (1 + t) ∈ V := hafter (1 + t) ⟨by linarith, by linarith⟩
    have hlt : g (1 + t) < r ^ 2 := (hmem (1 + t) ht).1.mp hin
    rw [hboundary1]
    exact hlt.le
  exact endpoint_port_products_opposite lambda0 lambda1
    (xi 0).1 (xi 0).2 (xi 1).1 (xi 1).2 hlambda
    (deriv_pos_of_right_increase hd0 hd0ne hright0)
    (deriv_neg_of_right_decrease hd1 hd1ne hright1)

end PoincareConjecture.M25.Topology3D.SaddleOrientation
