import PoincareConjecture.Proofs.M09.VariationAction
import PoincareConjecture.Proofs.M09.VariationSecondBoundary
import PoincareConjecture.Proofs.M09.HessianCurveChainRule
import PoincareConjecture.Proofs.M09.SecondDerivativeComparison
import PoincareConjecture.Proofs.M09.SpatialContact








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

local notation "E" => EuclideanSpace ℝ (Fin n)

set_option maxHeartbeats 1000000 in

set_option backward.isDefEq.respectTransparency false in
theorem lExponentialFamily_hessian_le_variation_index
    (hM04 : RicciFlowCurvatureTheory.{u}) (hL : LGeodesicTheory F T τmax)
    (hτmax : 0 < τmax) (hwindow : Set.Icc (T - τmax) T ⊆ J)
    (A : LExponentialFamily F T τmax p) (Z : TangentSpace (𝓡 n) p)
    (b : ℝ) (hb : 0 < b) (hmax : b < τmax)
    (hmin : IsMinimizingBackwardLPath F T 0 b (A.path Z b hb hmax))
    (f : M → ℝ) (O : Set M) (hO : IsOpen O) (hqO : A.gamma Z b ∈ O)
    (hf : ContMDiffOn (𝓡 n) (𝓘(ℝ, ℝ)) ∞ f O)
    (hvalue : f (A.gamma Z b) = A.action Z b / (2 * Real.sqrt b))
    (hlower : ∀ᶠ q in 𝓝 (A.gamma Z b), f q ≤ reducedLength F T p q b)
    (V : InitialFixedLVariation F T 0 b (A.path Z b hb hmax))
    (hbase : V.toLVariation.baseSquareCurve = A.squareFamily Z) :
    ∃ D : LVariationDerivativeData V.toLVariation,
      (F.connection (T - b)).hessian f (A.gamma Z b)
        (squareVariationField V.toLVariation (Real.sqrt b))
        (squareVariationField V.toLVariation (Real.sqrt b)) ≤
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
  have hfη : ContMDiffAt (𝓡 n) (𝓘(ℝ, ℝ)) ∞ f (η 0) :=
    hf.contMDiffAt (hO.mem_nhds (hη0.symm ▸ hqO))
  have hg : ContDiffAt ℝ ∞ g 0 :=
    (hfη.comp 0 (hη.contMDiffAt (hI.mem_nhds h0I))).contDiffAt
  have hstart : (A.path Z b hb hmax).curve 0 = p :=
    (congrFun (A.path_eq Z b hb hmax) 0).trans (A.gamma_at_zero Z)
  have hS0 : S 0 = A.action Z b := by
    change backwardLLength F T 0 b (fun t ↦ V.family t 0) = A.action Z b
    simp only [V.at_zero, A.path_eq, LExponentialFamily.action]
  have hnear : ∀ᶠ u in 𝓝 (0 : ℝ), f (η u) ≤ reducedLength F T p (η u) b :=
    (hη.contMDiffAt (hI.mem_nhds h0I)).continuousAt.tendsto.eventually (by
      rw [hη0]
      exact hlower)
  have hgap : IsLocalMin (fun u ↦ S u - (2 * c) * g u) 0 := by
    have hzero : S 0 - (2 * c) * g 0 = 0 := by
      change S 0 - (2 * c) * f (η 0) = 0
      rw [hS0, hη0, hvalue, mul_div_cancel₀ _ (mul_pos zero_lt_two hc).ne', sub_self]
    filter_upwards [hI.mem_nhds h0I, hnear] with u hu hl
    rw [hzero]
    have hcomp := reducedLength_le_initialFixedVariation hM04 hL hτmax hwindow hb hmax
      V p hstart u hu
    exact sub_nonneg.mpr (by
      simpa only [mul_comm] using
        (le_div_iff₀ (mul_pos zero_lt_two hc)).mp (hl.trans hcomp))
  have hsecond := localMin_secondDeriv_scaled_comparison S g (2 * c) 0 hS hg hgap
  obtain ⟨D, Q, hQ, hQeq⟩ := hL.second_variation 0 b le_rfl hb hmax.le
    (A.path Z b hb hmax) (hL.euler_lagrange 0 b le_rfl hb hmax.le _ hmin) V.toLVariation
  have hchain := secondDeriv_comp_eq_hessian_add_acceleration F (T - c ^ 2) η I hI hη
    (D.endpoint_extension c hcK) 0 h0I f O hO (hη0.symm ▸ hqO) hf
  change deriv (deriv g) 0 =
    (F.connection (T - c ^ 2)).hessian f (η 0)
      (squareVariationField V.toLVariation c) (squareVariationField V.toLVariation c) +
    mvfderiv (𝓡 n) f (η 0) (variationEndpointAcceleration V.toLVariation D c hcK) at hchain
  rw [hc2, hη0] at hchain
  have hdf := lExponentialFamily_spatial_differential_of_lower_contact hM04 hτmax hwindow
    hL A Z b hb hmax f (hf.contMDiffAt (hO.mem_nhds hqO)) hvalue hlower
    (variationEndpointAcceleration V.toLVariation D c hcK)
  have hboundary := lExponentialFamily_initialFixedVariation_secondBoundary A Z b hb hmax V D hbase
  rw [hQ.deriv, hQeq, hchain, hdf] at hsecond
  rw [hboundary] at hsecond
  refine ⟨D, (le_div_iff₀ (mul_pos zero_lt_two hc)).mpr ?_⟩
  nlinarith

end PoincareConjecture.Proofs.M09
