import PoincareConjecture.Proofs.M09.VariationAction
import PoincareConjecture.Proofs.M09.VariationSecondBoundary
import PoincareConjecture.Proofs.M09.HessianCurveChainRule








set_option autoImplicit false
set_option maxSynthPendingDepth 3

open scoped Manifold ContDiff Bundle Topology
open Filter

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M] [ConnectedSpace M]
  {J : Set ℝ} {F : RicciFlow n M J} {T τmax : ℝ} {p : M}

set_option maxHeartbeats 1000000 in

set_option backward.isDefEq.respectTransparency false in
theorem lExponentialFamily_hessian_eq_variation_index
    (hM04 : RicciFlowCurvatureTheory.{u}) (hL : LGeodesicTheory F T τmax)
    (hτmax : 0 < τmax) (hwindow : Set.Icc (T - τmax) T ⊆ J)
    (A : LExponentialFamily F T τmax p) (Z : TangentSpace (𝓡 n) p)
    (b : ℝ) (hb : 0 < b) (hmax : b < τmax)
    (hmin : IsMinimizingBackwardLPath F T 0 b (A.path Z b hb hmax))
    (f : M → ℝ) (O : Set M) (hO : IsOpen O) (hqO : A.gamma Z b ∈ O)
    (hf : ContMDiffOn (𝓡 n) (𝓘(ℝ, ℝ)) ∞ f O)
    (hdf : ∀ v : TangentSpace (𝓡 n) (A.gamma Z b),
      mvfderiv (𝓡 n) f (A.gamma Z b) v =
        (F.metric (T - b)).inner (A.gamma Z b) (curveVelocity (A.gamma Z) b) v)
    (V : InitialFixedLVariation F T 0 b (A.path Z b hb hmax))
    (hbase : V.toLVariation.baseSquareCurve = A.squareFamily Z)
    (hpull : (fun u ↦ f (V.squareFamily (Real.sqrt b) u)) =ᶠ[𝓝 (0 : ℝ)]
      (fun u ↦ variationLLength V.toLVariation u / (2 * Real.sqrt b))) :
    ∃ D : LVariationDerivativeData V.toLVariation,
      (F.connection (T - b)).hessian f (A.gamma Z b)
        (squareVariationField V.toLVariation (Real.sqrt b))
        (squareVariationField V.toLVariation (Real.sqrt b)) =
          secondVariationIndexForm V.toLVariation D / (2 * Real.sqrt b) := by
  let c := Real.sqrt b
  have hc : 0 < c := Real.sqrt_pos.mpr hb
  have hc2 : c ^ 2 = b := Real.sq_sqrt hb.le
  have hcK : c ∈ sqrtParameterInterval 0 b := ⟨Real.sqrt_le_sqrt hb.le, le_rfl⟩
  let I := V.toLVariation.parameterDomain
  have hI : IsOpen I := isOpen_Ioo
  have h0I : (0 : ℝ) ∈ I := ⟨neg_lt_zero.mpr V.radius_pos, V.radius_pos⟩
  let η := V.squareFamily c
  let S := variationLLength V.toLVariation
  let g : ℝ → ℝ := fun u ↦ f (η u)
  have hη : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ η I :=
    variation_endpoint_contMDiffOn V.toLVariation c hcK
  have hη0 : η 0 = A.gamma Z b := by
    change V.toLVariation.baseSquareCurve c = A.gamma Z b
    rw [hbase, A.square_agrees Z c ⟨hc.le, Real.sqrt_lt_sqrt hb.le hmax⟩, hc2]
  have hS : ContDiffAt ℝ ∞ S 0 :=
    variationLLength_contDiffAt hM04 hτmax hwindow hb hmax V.toLVariation 0 h0I
  have hg : ContDiffAt ℝ ∞ g 0 :=
    ((hf.contMDiffAt (hO.mem_nhds (hη0.symm ▸ hqO))).comp 0
      (hη.contMDiffAt (hI.mem_nhds h0I))).contDiffAt
  obtain ⟨D, Q, hQ, hQeq⟩ := hL.second_variation 0 b le_rfl hb hmax.le
    (A.path Z b hb hmax) (hL.euler_lagrange 0 b le_rfl hb hmax.le _ hmin) V.toLVariation
  have hchain := secondDeriv_comp_eq_hessian_add_acceleration F (T - c ^ 2) η I hI hη
    (D.endpoint_extension c hcK) 0 h0I f O hO (hη0.symm ▸ hqO) hf
  change deriv (deriv g) 0 =
    (F.connection (T - c ^ 2)).hessian f (η 0)
      (squareVariationField V.toLVariation c) (squareVariationField V.toLVariation c) +
    mvfderiv (𝓡 n) f (η 0) (variationEndpointAcceleration V.toLVariation D c hcK) at hchain
  rw [hc2, hη0, hdf] at hchain
  have hscaled : S =ᶠ[𝓝 (0 : ℝ)] (fun u ↦ (2 * c) * g u) := by
    filter_upwards [hpull] with u hu
    change g u = S u / (2 * c) at hu
    rw [hu, mul_div_cancel₀ _ (mul_pos zero_lt_two hc).ne']
  have hgd : HasDerivAt (deriv g) (deriv (deriv g) 0) 0 :=
    ((hg.derivWithin (m := ∞) (by simp)).differentiableAt (by simp)).hasDerivAt
  have hgn : ∀ᶠ u in 𝓝 (0 : ℝ), DifferentiableAt ℝ g u :=
    ((hg.of_le (show (1 : ℕ∞ω) ≤ ∞ by simp)).eventually (by simp)).mono
      (fun u hu ↦ hu.differentiableAt (by simp))
  have hderivscaled : (fun u ↦ (2 * c) * deriv g u) =ᶠ[𝓝 (0 : ℝ)]
      deriv (fun u ↦ (2 * c) * g u) := by
    filter_upwards [hgn] with u hu
    exact (hu.hasDerivAt.const_mul (2 * c)).deriv.symm
  have hsecond : HasDerivAt (deriv S) ((2 * c) * deriv (deriv g) 0) 0 :=
    (hgd.const_mul (2 * c)).congr_of_eventuallyEq (hscaled.deriv.trans hderivscaled.symm)
  have hactual := hQ.unique hsecond
  rw [hQeq, hchain,
    lExponentialFamily_initialFixedVariation_secondBoundary A Z b hb hmax V D hbase] at hactual
  refine ⟨D, (eq_div_iff (mul_pos zero_lt_two hc).ne').mpr ?_⟩
  nlinarith

end PoincareConjecture.Proofs.M09
