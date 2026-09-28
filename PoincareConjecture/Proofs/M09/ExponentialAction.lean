import PoincareConjecture.Definitions.Ch06.ReducedLength
import PoincareConjecture.Proofs.M09.ActionCongruence
import PoincareConjecture.Proofs.M09.FamilyActionDensity
import PoincareConjecture.Proofs.M09.LocalSmoothPrimitive









set_option autoImplicit false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 800000

open scoped Manifold ContDiff Bundle Topology intervalIntegral

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

set_option backward.isDefEq.respectTransparency false in
theorem lExponentialFamily_action_square_eq {J : Set ℝ} {F : RicciFlow n M J}
    {T τmax : ℝ} {p : M} (A : LExponentialFamily F T τmax p)
    (Z : TangentSpace (𝓡 n) p) (τ : ℝ) (hτ : 0 < τ) (hmax : τ < τmax) :
    A.action Z τ = ∫ s in 0..Real.sqrt τ,
      squareFamilyActionDensity F T (fun z ↦ A.squareFamily z.1 z.2) (Z, s) := by
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric T).toRiemannianMetric⟩
  let E := TangentSpace (𝓡 n) p
  have hf : ContMDiffOn (𝓘(ℝ, E × ℝ)) (𝓡 n) ∞
      (fun z ↦ A.squareFamily z.1 z.2) A.squareDomain := by
    convert! A.square_smooth using 1 <;>
      simp only [E, modelWithCornersSelf_prod, chartedSpaceSelf_prod]
  have hα : ∀ s ∈ Set.Ioo 0 (Real.sqrt τ),
      MDifferentiableAt (𝓘(ℝ, ℝ)) (𝓡 n) (A.squareFamily Z) s := by
    intro s hs
    have hmem : (Z, s) ∈ A.squareDomain := A.square_contains
      ⟨Set.mem_univ _, hs.1.le, hs.2.trans (Real.sqrt_lt_sqrt hτ.le hmax)⟩
    have hpair : ContMDiff (𝓘(ℝ, ℝ)) (𝓘(ℝ, E × ℝ)) ∞ (fun r : ℝ ↦ (Z, r)) :=
      (contDiff_const.prodMk contDiff_id).contMDiff
    exact ((hf.contMDiffAt (A.square_open.mem_nhds hmem)).comp s
      hpair.contMDiffAt).mdifferentiableAt (by simp)
  have heq : Set.EqOn (A.gamma Z) (fun r ↦ A.squareFamily Z (Real.sqrt r))
      (Set.Ioo 0 τ) := by
    intro r hr
    have h := A.square_agrees Z (Real.sqrt r)
      ⟨Real.sqrt_nonneg r, Real.sqrt_lt_sqrt hr.1.le (hr.2.trans hmax)⟩
    simpa only [Real.sq_sqrt hr.1.le] using h.symm
  exact (backwardLLength_congr_Ioo F T 0 τ hτ.le _ _ heq).trans
    (backwardLLength_comp_sqrt_eq F T τ hτ (A.squareFamily Z) hα)

set_option backward.isDefEq.respectTransparency false in
theorem lExponentialFamily_action_contDiffOn {J : Set ℝ} {F : RicciFlow n M J}
    (hM04 : RicciFlowCurvatureTheory.{u}) {T τmax : ℝ}
    (hτmax : 0 < τmax) (hwindow : Set.Icc (T - τmax) T ⊆ J)
    {p : M} (A : LExponentialFamily F T τmax p) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨(F.metric T).toRiemannianMetric⟩
    ContDiffOn ℝ ∞ (fun z : TangentSpace (𝓡 n) p × ℝ ↦ A.action z.1 z.2)
      (Set.univ ×ˢ Set.Ioo 0 τmax) := by
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric T).toRiemannianMetric⟩
  let E := TangentSpace (𝓡 n) p
  letI : FiniteDimensional ℝ E :=
    VectorBundle.finiteDimensional ℝ (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) p
  let f : E × ℝ → M := fun z ↦ A.squareFamily z.1 z.2
  let U := A.squareDomain ∩ (Set.univ ×ˢ Set.Ioo (-Real.sqrt τmax) (Real.sqrt τmax))
  let H := squareFamilyActionDensity F T f
  have hU : IsOpen U := A.square_open.inter (isOpen_univ.prod isOpen_Ioo)
  have hf : ContMDiffOn (𝓘(ℝ, E × ℝ)) (𝓡 n) ∞ f A.squareDomain := by
    convert! A.square_smooth using 1 <;>
      simp only [E, modelWithCornersSelf_prod, chartedSpaceSelf_prod]
  have hH : ContDiffOn ℝ ∞ H U :=
    squareFamilyActionDensity_contDiffOn F hM04 T τmax hτmax hwindow f U hU
      (hf.mono Set.inter_subset_left) (fun z hz ↦ hz.2.2)
  intro z hz
  have hsegment : ∀ r ∈ Set.Icc (0 : ℝ) 1, (z.1, Real.sqrt z.2 * r) ∈ U := by
    intro r hr
    have h0 : 0 ≤ Real.sqrt z.2 * r := mul_nonneg (Real.sqrt_nonneg z.2) hr.1
    have hlt : Real.sqrt z.2 * r < Real.sqrt τmax :=
      (mul_le_of_le_one_right (Real.sqrt_nonneg z.2) hr.2).trans_lt
        (Real.sqrt_lt_sqrt hz.2.1.le hz.2.2)
    exact ⟨A.square_contains ⟨Set.mem_univ _, h0, hlt⟩,
      Set.mem_univ _, (neg_lt_zero.mpr (Real.sqrt_pos.mpr hτmax)).trans_le h0, hlt⟩
  have hprimitive := contDiffAt_parameter_primitive H U hU hH (z.1, Real.sqrt z.2) hsegment
  have hsqrt : ContDiffAt ℝ ∞ (fun w : E × ℝ ↦ (w.1, Real.sqrt w.2)) z :=
    contDiffAt_fst.prodMk (contDiffAt_snd.sqrt hz.2.1.ne')
  have hsmooth := hprimitive.comp z hsqrt
  have heq : (fun w : E × ℝ ↦ A.action w.1 w.2) =ᶠ[nhds z]
      (fun w : E × ℝ ↦ ∫ s in 0..Real.sqrt w.2, H (w.1, s)) := by
    filter_upwards [(isOpen_univ.prod isOpen_Ioo).mem_nhds hz] with w hw
    exact lExponentialFamily_action_square_eq A w.1 w.2 hw.2.1 hw.2.2
  exact (hsmooth.congr_of_eventuallyEq heq).contDiffWithinAt

end PoincareConjecture.Proofs.M09
