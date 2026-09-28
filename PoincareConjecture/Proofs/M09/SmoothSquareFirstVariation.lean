import PoincareConjecture.Proofs.M09.SmoothSquareVariation
import PoincareConjecture.Proofs.M09.InitialVectorIdentification
import PoincareConjecture.Proofs.M09.FamilyEulerEquation
import PoincareConjecture.Statements.Ch06.LGeometry








set_option autoImplicit false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 800000

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ} {F : RicciFlow n M J} {T τmax : ℝ} {p : M}

local notation "Q" => EuclideanSpace ℝ (Fin n)

set_option backward.isDefEq.respectTransparency false in
theorem lExponentialFamily_variation_boundaryTerm (A : LExponentialFamily F T τmax p)
    (Z : TangentSpace (𝓡 n) p) (b : ℝ) (hb : 0 < b) (hmax : b < τmax)
    (V : LVariation F T 0 b (A.path Z b hb hmax)) :
    firstVariationBoundaryTerm V =
      (F.metric (T - b)).inner (A.squareFamily Z (Real.sqrt b))
        (curveVelocity (A.squareFamily Z) (Real.sqrt b)) (squareVariationField V (Real.sqrt b)) -
      (F.metric T).inner p ((2 : ℝ) • Z) (squareVariationField V 0) := by
  let K := sqrtParameterInterval 0 b
  let U := (fun s : ℝ ↦ (s, (0 : ℝ))) ⁻¹' V.squareDomain
  have hzero : (0 : ℝ) ∈ Set.Ioo (-V.radius) V.radius :=
    ⟨neg_lt_zero.mpr V.radius_pos, V.radius_pos⟩
  have hK : K = Set.Icc 0 (Real.sqrt b) := by simp only [K, sqrtParameterInterval, Real.sqrt_zero]
  have hKdiff : UniqueDiffOn ℝ K := hK ▸ uniqueDiffOn_Icc (Real.sqrt_pos.mpr hb)
  have hU : IsOpen U := V.square_open.preimage (continuous_id.prodMk continuous_const)
  have hKU : K ⊆ U := fun s hs ↦ V.square_contains ⟨hs, hzero⟩
  have hβ : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ V.baseSquareCurve U :=
    V.square_smooth.comp (contMDiff_id.prodMk contMDiff_const).contMDiffOn (fun _ hs ↦ hs)
  have heq : Set.EqOn V.baseSquareCurve (A.squareFamily Z) K := by
    intro s hs
    have hs0 : 0 ≤ s := by simpa only [sqrtParameterInterval, Real.sqrt_zero] using hs.1
    have hsmax := hs.2.trans_lt (Real.sqrt_lt_sqrt hb.le hmax)
    exact (V.square_agrees s hs 0 hzero).trans ((V.at_zero (s ^ 2)).trans
      ((congrFun (A.path_eq Z b hb hmax) (s ^ 2)).trans
        (A.square_agrees Z s ⟨hs0, hsmax⟩).symm))
  have hv (s : ℝ) (hs : s ∈ K) :
      (curveVelocityWithin (n := n) V.baseSquareCurve K s : Q) = curveVelocity (A.squareFamily Z) s := by
    have hdβ := (hβ.contMDiffAt (hU.mem_nhds (hKU hs))).mdifferentiableAt (by simp)
    have hs0 : 0 ≤ s := by simpa only [sqrtParameterInterval, Real.sqrt_zero] using hs.1
    have hdA := (lExponentialFamily_squareSlice_contMDiffAt A Z s
      ⟨hs0, hs.2.trans_lt (Real.sqrt_lt_sqrt hb.le hmax)⟩).mdifferentiableAt (by simp)
    exact (curveVelocityWithin_eq_curveVelocity V.baseSquareCurve K s (hKdiff s hs) hdβ).trans
      (curveVelocity_eq_of_eqOn heq hs (hKdiff s hs) hdβ hdA)
  have hvalue (s : ℝ) (hs : s ∈ K) :
      (F.metric (T - s ^ 2)).inner (V.baseSquareCurve s)
        (curveVelocityWithin V.baseSquareCurve K s) (squareVariationField V s) =
      (F.metric (T - s ^ 2)).inner (A.squareFamily Z s)
        (curveVelocity (A.squareFamily Z) s) (squareVariationField V s) := by
    have ht : (V.baseSquareCurve s,
        ((curveVelocityWithin V.baseSquareCurve K s : Q), (squareVariationField V s : Q))) =
        (A.squareFamily Z s, ((curveVelocity (A.squareFamily Z) s : Q),
          (squareVariationField V s : Q))) := Prod.ext (heq hs) (Prod.ext (hv s hs) rfl)
    exact congrArg (fun q : M × (Q × Q) ↦ (F.metric (T - s ^ 2)).inner q.1 q.2.1 q.2.2) ht
  have h0K : (0 : ℝ) ∈ K := by rw [hK]; exact ⟨le_rfl, Real.sqrt_nonneg b⟩
  have hbK : Real.sqrt b ∈ K := by rw [hK]; exact ⟨Real.sqrt_nonneg b, le_rfl⟩
  unfold firstVariationBoundaryTerm
  dsimp only
  rw [Real.sqrt_zero, hvalue _ hbK, hvalue _ h0K, Real.sq_sqrt hb.le]
  simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), sub_zero,
    lExponentialFamily_initial_velocity]
  rw [A.square_at_zero Z]

set_option backward.isDefEq.respectTransparency false in
theorem hasDerivAt_smoothSquareFamily_action [ConnectedSpace M]
    (hM04 : RicciFlowCurvatureTheory.{u}) (hL : LGeodesicTheory F T τmax)
    (hτmax : 0 < τmax) (hwindow : Set.Icc (T - τmax) T ⊆ J)
    (A : LExponentialFamily F T τmax p) (Z : TangentSpace (𝓡 n) p)
    (b : ℝ) (hb : 0 < b) (hmax : b < τmax)
    (f : ℝ × ℝ → M) (U : Set (ℝ × ℝ)) (hU : IsOpen U)
    (hf : ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓘(ℝ, ℝ))) (𝓡 n) ∞ f U)
    (ρ : ℝ) (hρ : 0 < ρ) (hI : Set.Icc 0 (Real.sqrt b) ×ˢ Set.Ioo (-ρ) ρ ⊆ U)
    (hcenter : ∀ s ∈ Set.Icc 0 (Real.sqrt b), f (s, 0) = A.squareFamily Z s) :
    HasDerivAt (fun u ↦ backwardLLength F T 0 b (fun t ↦ f (Real.sqrt t, u)))
      ((F.metric (T - b)).inner (A.squareFamily Z (Real.sqrt b))
        (curveVelocity (A.squareFamily Z) (Real.sqrt b))
        (curveVelocity (fun u ↦ f (Real.sqrt b, u)) 0) -
      (F.metric T).inner p ((2 : ℝ) • Z) (curveVelocity (fun u ↦ f (0, u)) 0)) 0 := by
  obtain ⟨V, _, hVf, _, hVa⟩ := exists_lVariation_of_smoothSquareFamily
    hM04 hτmax hwindow A Z b hb hmax f U hU hf ρ hρ hI hcenter
  obtain ⟨D, hfirst⟩ := hL.first_variation 0 b le_rfl hb hmax.le (A.path Z b hb hmax) V
  rw [lExponentialFamily_firstVariationResidualIntegral_eq_zero hM04 hτmax hwindow
    A Z b hb hmax V D, add_zero, lExponentialFamily_variation_boundaryTerm A Z b hb hmax V] at hfirst
  have hfield (s : ℝ) : (squareVariationField V s : Q) = curveVelocity (fun u ↦ f (s, u)) 0 :=
    congrArg (fun γ : ℝ → M ↦ (curveVelocity γ 0 : Q)) (funext (hVf s))
  rw [hfield (Real.sqrt b), hfield 0, show variationLLength V =
    (fun u ↦ backwardLLength F T 0 b (fun t ↦ f (Real.sqrt t, u))) from funext hVa] at hfirst
  exact hfirst

end PoincareConjecture.Proofs.M09
