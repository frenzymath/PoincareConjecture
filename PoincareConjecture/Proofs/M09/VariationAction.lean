import PoincareConjecture.Proofs.M09.SmoothSquareAction
import PoincareConjecture.Proofs.M09.ActionCongruence
import PoincareConjecture.Proofs.M09.PathComparison








set_option autoImplicit false
set_option maxSynthPendingDepth 3

open scoped Manifold ContDiff Bundle Topology
open Filter

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ} {F : RicciFlow n M J} {T a b τmax : ℝ}

theorem variation_endpoint_contMDiffOn {P : BackwardTimePath F T a b}
    (V : LVariation F T a b P) (s : ℝ) (hs : s ∈ sqrtParameterInterval a b) :
    ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ (V.squareFamily s) V.parameterDomain := by
  exact V.square_smooth.comp (contMDiff_const.prodMk contMDiff_id).contMDiffOn
    (fun _ hu ↦ V.square_contains ⟨hs, hu⟩)

theorem variationLLength_eq_squareAction (hb : 0 < b) {P : BackwardTimePath F T 0 b}
    (V : LVariation F T 0 b P) (u : ℝ) (hu : u ∈ V.parameterDomain) :
    variationLLength V u =
      backwardLLength F T 0 b (fun t ↦ V.squareFamily (Real.sqrt t) u) := by
  apply backwardLLength_congr_Ioo F T 0 b hb.le
  intro t ht
  have hs : Real.sqrt t ∈ sqrtParameterInterval 0 b := by
    simpa only [sqrtParameterInterval, Real.sqrt_zero] using
      (show Real.sqrt t ∈ Set.Icc 0 (Real.sqrt b) from
        ⟨Real.sqrt_nonneg t, Real.sqrt_le_sqrt ht.2.le⟩)
  simpa only [Real.sq_sqrt ht.1.le] using (V.square_agrees (Real.sqrt t) hs u hu).symm

set_option backward.isDefEq.respectTransparency false in
theorem variationLLength_contDiffAt
    (hM04 : RicciFlowCurvatureTheory.{u}) (hτmax : 0 < τmax)
    (hwindow : Set.Icc (T - τmax) T ⊆ J) (hb : 0 < b) (hmax : b < τmax)
    {P : BackwardTimePath F T 0 b} (V : LVariation F T 0 b P)
    (u : ℝ) (hu : u ∈ V.parameterDomain) :
    ContDiffAt ℝ ∞ (variationLLength V) u := by
  let f : ℝ × ℝ → M := fun z ↦ V.squareFamily z.2 z.1
  let U := Prod.swap ⁻¹' V.squareDomain
  have hU : IsOpen U := V.square_open.preimage continuous_swap
  have hV : ContMDiffOn (𝓘(ℝ, ℝ × ℝ)) (𝓡 n) ∞
      (fun z : ℝ × ℝ ↦ V.squareFamily z.1 z.2) V.squareDomain := by
    convert! V.square_smooth using 1 <;>
      simp only [modelWithCornersSelf_prod, chartedSpaceSelf_prod]
  have hf : ContMDiffOn (𝓘(ℝ, ℝ × ℝ)) (𝓡 n) ∞ f U :=
    hV.comp (contDiff_snd.prodMk contDiff_fst).contMDiff.contMDiffOn (fun _ hz ↦ hz)
  have hsegment (r : ℝ) (hr : r ∈ Set.Icc (0 : ℝ) 1) :
      (u, Real.sqrt b * r) ∈ U := by
    change (Real.sqrt b * r, u) ∈ V.squareDomain
    apply V.square_contains
    refine ⟨?_, hu⟩
    simpa only [sqrtParameterInterval, Real.sqrt_zero] using
      (show Real.sqrt b * r ∈ Set.Icc 0 (Real.sqrt b) from
        ⟨mul_nonneg (Real.sqrt_nonneg b) hr.1,
          mul_le_of_le_one_right (Real.sqrt_nonneg b) hr.2⟩)
  have haction := contDiffAt_smoothSquareFamily_action F hM04 T τmax hτmax hwindow
    f U hU hf (u, b) ⟨hb, hmax⟩ hsegment
  have hsmooth : ContDiffAt ℝ ∞
      (fun v ↦ backwardLLength F T 0 b (fun t ↦ V.squareFamily (Real.sqrt t) v)) u :=
    haction.comp u (contDiffAt_id.prodMk contDiffAt_const)
  apply hsmooth.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds hu] with v hv
  exact variationLLength_eq_squareAction hb V v hv

theorem reducedLength_le_initialFixedVariation [ConnectedSpace M]
    (hM04 : RicciFlowCurvatureTheory.{u}) (hL : LGeodesicTheory F T τmax)
    (hτmax : 0 < τmax) (hwindow : Set.Icc (T - τmax) T ⊆ J)
    (hb : 0 < b) (hmax : b < τmax) {P : BackwardTimePath F T 0 b}
    (V : InitialFixedLVariation F T 0 b P) (p : M) (hP0 : P.curve 0 = p)
    (u : ℝ) (hu : u ∈ V.toLVariation.parameterDomain) :
    reducedLength F T p (V.squareFamily (Real.sqrt b) u) b ≤
      variationLLength V.toLVariation u / (2 * Real.sqrt b) := by
  let D := (fun s : ℝ ↦ (s, u)) ⁻¹' V.squareDomain
  have hD : IsOpen D := V.square_open.preimage (continuous_id.prodMk continuous_const)
  have hKD : Set.Icc 0 (Real.sqrt b) ⊆ D := by
    intro s hs
    apply V.square_contains
    exact ⟨by simpa only [sqrtParameterInterval, Real.sqrt_zero] using hs, hu⟩
  have hα : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ (fun s ↦ V.squareFamily s u) D :=
    V.square_smooth.comp (contMDiff_id.prodMk contMDiff_const).contMDiffOn (fun _ hs ↦ hs)
  obtain ⟨Q, hQ, _⟩ := exists_backwardPath_of_smoothSquareCurve F hM04 T τmax hτmax
    hwindow b hb hmax (fun s ↦ V.squareFamily s u) D hD hKD hα
  have h0 : (0 : ℝ) ∈ sqrtParameterInterval 0 b := by
    simp only [sqrtParameterInterval, Real.sqrt_zero, Set.mem_Icc, le_refl,
      Real.sqrt_nonneg, and_self]
  have hQ0 : Q.curve 0 = p := by
    rw [hQ]
    change V.squareFamily (Real.sqrt 0) u = p
    rw [Real.sqrt_zero, V.square_agrees 0 h0 u hu, zero_pow two_ne_zero,
      V.fixed_left u hu, hP0]
  have hQb : Q.curve b = V.squareFamily (Real.sqrt b) u := congrFun hQ b
  have hcompare := reducedLength_le_path hL hb hmax.le Q hQ0 hQb
  rw [hQ, ← variationLLength_eq_squareAction hb V.toLVariation u hu] at hcompare
  exact hcompare

end PoincareConjecture.Proofs.M09
