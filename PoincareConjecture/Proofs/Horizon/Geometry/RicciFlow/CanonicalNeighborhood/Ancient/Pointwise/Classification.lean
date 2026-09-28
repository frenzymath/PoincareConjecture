import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Pointwise.Round
import PoincareConjecture.Definitions.M27KappaAlternatives
import PoincareConjecture.Statements.M27Providers
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.Scalar.Regularity

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
  {K : AncientKappaSolution 3 M} {C : ℝ}

def canonicalComponentConstant (C : ℝ) : ℝ := C + C ^ (1 / 2 : ℝ) + 1

private theorem lt_canonicalComponentConstant (hC : 0 < C) :
    C < canonicalComponentConstant C := by
  have hpow := Real.rpow_pos_of_pos hC (1 / 2 : ℝ)
  dsimp [canonicalComponentConstant]
  linarith

theorem M27CompactPositiveGeometry.canonicalComponent
    (N : M27CompactPositiveGeometry K C) (hC : 0 < C)
    (hcontinuous : Continuous (K.flow.connection 0).scalarCurvature)
    (hscalar : ∀ x, 0 < (K.flow.connection 0).scalarCurvature x) :
    Nonempty (M27CanonicalComponent K 0 (canonicalComponentConstant C)) := by
  let R := (K.flow.connection 0).scalarCurvature
  let s := fun x => R x ^ (-1 / 2 : ℝ)
  have hs : Continuous s := hcontinuous.rpow_const (fun x => Or.inl (hscalar x).ne')
  obtain ⟨p, _, hp⟩ := N.compact.exists_isMaxOn Set.univ_nonempty hcontinuous.continuousOn
  obtain ⟨q, _, hq⟩ := N.compact.exists_isMaxOn Set.univ_nonempty hs.continuousOn
  obtain ⟨r, _, hr⟩ := N.compact.exists_isMinOn Set.univ_nonempty hs.continuousOn
  have hRsup : scalarCurvatureSup (K.flow.metric 0) (K.flow.connection 0) = R p := by
    apply IsGreatest.csSup_eq
    exact ⟨⟨p, rfl⟩, by rintro _ ⟨x, rfl⟩; exact hp (Set.mem_univ x)⟩
  have hssup : sSup (Set.range s) = s q := by
    apply IsGreatest.csSup_eq
    exact ⟨⟨q, rfl⟩, by rintro _ ⟨x, rfl⟩; exact hq (Set.mem_univ x)⟩
  have hsinf : sInf (Set.range s) = s r := by
    apply IsLeast.csInf_eq
    exact ⟨⟨r, rfl⟩, by rintro _ ⟨x, rfl⟩; exact hr (Set.mem_univ x)⟩
  have hCC := lt_canonicalComponentConstant hC
  have hCp := hC.trans hCC
  have hinv : (canonicalComponentConstant C)⁻¹ ≤ C ^ (-1 / 2 : ℝ) := by
    have hhalf : 0 < C ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hC _
    have hle : C ^ (1 / 2 : ℝ) ≤ canonicalComponentConstant C := by
      dsimp [canonicalComponentConstant]
      linarith
    rw [show (-1 / 2 : ℝ) = -(1 / 2 : ℝ) by norm_num, Real.rpow_neg hC.le]
    exact inv_anti₀ hhalf hle
  refine ⟨{
    time_mem := le_rfl
    constant_pos := hCp
    compact := N.compact
    topology := N.topology
    positive := N.positive
    scalar_sup_pos := hRsup ▸ hscalar p
    uniform_sectional_lower := ?_
    diameter_lower := ?_
    diameter_upper := ?_
  }⟩
  · refine ⟨C⁻¹, (inv_lt_inv₀ hCp hC).mpr hCC, fun x a b ha hb hab => ?_⟩
    rw [hRsup]
    exact (N.sectional_bounds p x a b ha hb hab).1.le
  · change (canonicalComponentConstant C)⁻¹ * sSup (Set.range s) < _
    rw [hssup]
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right hinv
      (Real.rpow_nonneg (hscalar q).le _)) (N.diameter_lower q)
  · change _ < canonicalComponentConstant C * sInf (Set.range s)
    rw [hsinf]
    exact (N.diameter_upper r).trans_le (mul_le_mul_of_nonneg_right hCC.le
      (Real.rpow_nonneg (hscalar r).le _))

theorem strongCanonicalNeighborhood_of_classification
    (P : M27KappaAlternativePredecessors.{u}) (K : AncientKappaSolution 3 M)
    {epsilon C : ℝ} (hepsilon : 0 < epsilon) (hC : 0 < C)
    (N : M27KappaNine93Conclusion K epsilon C)
    (hexception : ¬ Nonempty (M27ProjectivePlaneLineFlowCertificate K)) (x : M) :
    M27StrongCanonicalNeighborhood K 0 x epsilon (canonicalComponentConstant C) := by
  have hCC := (lt_canonicalComponentConstant hC).le
  have hcap (cap : StrongCapCertificate K 0 epsilon C)
      (hconnection : cap.cap.connection = K.flow.connection 0) (hx : x ∈ cap.cap.core) :
      M27StrongCanonicalNeighborhood K 0 x epsilon (canonicalComponentConstant C) := by
    exact .cap {
      time_mem := le_rfl
      cap := cap.cap
      epsilon_eq := cap.cap_epsilon
      constant_le := cap.cap_constant.trans hCC
      connection_eq := hconnection
      contains := hx
    }
  cases N with
  | round hr _ => exact strongCanonicalNeighborhood_of_round K hr hepsilon _ 0 le_rfl x
  | compactPositive hg =>
    have hs : ∀ y, 0 < (K.flow.connection 0).scalarCurvature y := by
      intro y
      obtain ⟨A⟩ := P.normalization M K y 0 le_rfl
      exact A.scale_eq ▸ A.scale_pos
    obtain ⟨Q⟩ := hg.canonicalComponent hC
      (P.tensor_calculus 3 M _ _).contMDiff_scalarCurvature.continuous hs
    exact .component Q
  | doubleCapped tube _ _ hcoverage =>
    rcases hcoverage x with hfirst | hsecond | ⟨neck, hneck⟩
    · exact hcap tube.cap₁ tube.first_cap_connection hfirst
    · exact hcap tube.cap₂ tube.second_cap_connection hsecond
    · exact .neck neck hneck
  | cappedEuclidean tube _ _ hcoverage =>
    rcases hcoverage x with hcore | ⟨neck, hneck⟩
    · exact hcap tube.cap tube.cap_connection hcore
    · exact .neck neck hneck
  | cappedQuotient _ tube hcoverage =>
    rcases hcoverage x with hcore | ⟨neck, hneck⟩
    · exact hcap tube.cap tube.cap_connection hcore
    · exact .neck neck hneck
  | sphereLine _ tube =>
    obtain ⟨neck, hneck, _⟩ := tube.strong_at x
    exact .neck neck hneck
  | projectivePlaneLine model => exact (hexception ⟨model⟩).elim

end PoincareConjecture
