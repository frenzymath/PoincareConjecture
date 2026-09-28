import PoincareConjecture.Proofs.M09.LineInteriorFamily
import PoincareConjecture.Proofs.M09.ExponentialPhaseLinearization
import PoincareConjecture.Proofs.M09.FamilySlices
import PoincareConjecture.Proofs.M09.VelocityChainRules

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
theorem initialLineChartPhase_fixedTime_contDiffAt
    (A : LExponentialFamily F T τmax p) (Z W : TangentSpace (𝓡 n) p)
    (b : ℝ) (hb : 0 < b) (hmax : b < τmax) (s : ℝ)
    (hs : s ∈ sqrtParameterInterval 0 b) (x : M)
    (hx : A.squareFamily Z s ∈ (chartAt Q x).source) :
    ContDiffAt ℝ ∞ (fun r ↦ initialLineChartPhase A Z W x (s, r)) 0 := by
  let V := (initialVectorVariation A Z W b hb hmax).toLVariation
  let H : ℝ × ℝ → M := fun z ↦ V.squareFamily z.1 z.2
  let Ω := V.squareDomain ∩ H ⁻¹' (chartAt Q x).source
  have hH : ContMDiffOn (𝓘(ℝ, ℝ × ℝ)) (𝓡 n) ∞ H V.squareDomain := by
    convert! V.square_smooth using 1 <;>
      simp only [modelWithCornersSelf_prod, chartedSpaceSelf_prod]
  have hΩ : IsOpen Ω := hH.continuousOn.isOpen_inter_preimage V.square_open
    (chartAt Q x).open_source
  have hmem : (s, (0 : ℝ)) ∈ Ω := by
    refine ⟨V.square_contains ⟨hs, neg_lt_zero.mpr V.radius_pos, V.radius_pos⟩, ?_⟩
    change A.squareFamily (Z + (0 : ℝ) • W) s ∈ (chartAt Q x).source
    simpa only [zero_smul, add_zero] using hx
  exact ((initialLineChartPhase_contDiffOn A Z W b hb hmax x).contDiffAt
    (hΩ.mem_nhds hmem)).comp 0 (contDiffAt_const.prodMk contDiffAt_id)

set_option backward.isDefEq.respectTransparency false in
theorem lineInteriorCoordinate_deriv_eq_zero (A : LExponentialFamily F T τmax p)
    (Z W : TangentSpace (𝓡 n) p) (c : ℝ) (hc : 0 < c) (hmax : c < τmax)
    (hker : A.sliceDifferential Z c W = 0) : deriv (lineInteriorCoordinate A Z W c) 0 = 0 := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric T).toRiemannianMetric⟩
  let q := A.squareFamily Z (Real.sqrt c)
  let β : ℝ → M := fun r ↦ A.gamma (Z + r • W) c
  have heq (Y : TangentSpace (𝓡 n) p) : A.squareFamily Y (Real.sqrt c) = A.gamma Y c := by
    simpa only [Real.sq_sqrt hc.le] using A.square_agrees Y (Real.sqrt c)
      ⟨Real.sqrt_nonneg c, Real.sqrt_lt_sqrt hc.le hmax⟩
  have hslice := (lExponentialFamily_initialSlice_contMDiffAt A Z c hc hmax).mdifferentiableAt
    (by simp)
  have hline : HasDerivAt (fun r : ℝ ↦ Z + r • W) W 0 := by
    simpa only [id_eq, one_smul] using ((hasDerivAt_id (0 : ℝ)).smul_const W).const_add Z
  have hslice' : MDifferentiableAt (𝓘(ℝ, TangentSpace (𝓡 n) p)) (𝓡 n)
      (fun Y ↦ A.gamma Y c) (Z + (0 : ℝ) • W) := by
    simpa only [zero_smul, add_zero] using hslice
  have hβ : MDifferentiableAt (𝓘(ℝ, ℝ)) (𝓡 n) β 0 :=
    hslice'.comp 0 hline.hasFDerivAt.hasMFDerivAt.mdifferentiableAt
  have hv : (curveVelocity (n := n) β 0 : Q) = 0 :=
    (curveVelocity_comp_initial_line (fun Y ↦ A.gamma Y c) Z W hslice).trans hker
  have hβ0 : β 0 = q := by
    simpa only [β, zero_smul, add_zero, q] using (heq Z).symm
  have hx : β 0 ∈ (chartAt Q q).source := hβ0.symm ▸ mem_chart_source Q q
  have hd := hasDerivAt_chart_curve q β 0 hx hβ
  rw [hv, map_zero] at hd
  have hcoord : lineInteriorCoordinate A Z W c = fun r ↦ (chartAt Q q) (β r) := by
    funext r
    exact congrArg (chartAt Q q) (heq (Z + r • W))
  rw [hcoord]
  exact hd.deriv

end PoincareConjecture.Proofs.M09
