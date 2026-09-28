import PoincareConjecture.Definitions.Ch06.ReducedLength
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

set_option autoImplicit false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 800000

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ} {F : RicciFlow n M J} {T τmax : ℝ} {p : M}

set_option backward.isDefEq.respectTransparency false in
noncomputable def initialVectorVariation (A : LExponentialFamily F T τmax p)
    (Z W : TangentSpace (𝓡 n) p) (b : ℝ) (hb : 0 < b) (hmax : b < τmax) :
    InitialFixedLVariation F T 0 b (A.path Z b hb hmax) := by
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric T).toRiemannianMetric⟩
  let E := TangentSpace (𝓡 n) p
  let k : ℝ × ℝ → E × ℝ := fun z ↦ (Z + z.2 • W, z.1)
  let U := k ⁻¹' A.squareDomain
  have hk : ContDiff ℝ ∞ k :=
    (contDiff_const.add (contDiff_snd.smul contDiff_const)).prodMk contDiff_fst
  have hU : IsOpen U := A.square_open.preimage hk.continuous
  have hcontains : sqrtParameterInterval 0 b ×ˢ Set.Ioo (-1 : ℝ) 1 ⊆ U := by
    intro z hz
    have hs0 : 0 ≤ z.1 := by simpa only [sqrtParameterInterval, Real.sqrt_zero] using hz.1.1
    have hsmax : z.1 < Real.sqrt τmax :=
      hz.1.2.trans_lt (Real.sqrt_lt_sqrt hb.le hmax)
    exact A.square_contains ⟨Set.mem_univ _, hs0, hsmax⟩
  have hf : ContMDiffOn (𝓘(ℝ, E × ℝ)) (𝓡 n) ∞
      (fun z ↦ A.squareFamily z.1 z.2) A.squareDomain := by
    convert! A.square_smooth using 1 <;>
      simp only [E, modelWithCornersSelf_prod, chartedSpaceSelf_prod]
  have hcomp := hf.comp hk.contMDiff.contMDiffOn (fun z (hz : z ∈ U) ↦ hz)
  have hsquare : ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓘(ℝ, ℝ))) (𝓡 n) ∞
      (fun z : ℝ × ℝ ↦ A.squareFamily (Z + z.2 • W) z.1) U := by
    convert! hcomp using 1 <;>
      simp only [E, modelWithCornersSelf_prod, chartedSpaceSelf_prod]
  refine {
    family := fun t u ↦ A.gamma (Z + u • W) t
    at_zero := ?_
    radius := 1
    radius_pos := zero_lt_one
    squareFamily := fun s u ↦ A.squareFamily (Z + u • W) s
    squareDomain := U
    square_open := hU
    square_contains := hcontains
    square_smooth := hsquare
    square_agrees := ?_
    l_integrable := ?_
    fixed_left := ?_
  }
  · intro t
    simpa only [zero_smul, add_zero] using (congrFun (A.path_eq Z b hb hmax) t).symm
  · intro s hs u _
    have hs0 : 0 ≤ s := by simpa only [sqrtParameterInterval, Real.sqrt_zero] using hs.1
    exact A.square_agrees (Z + u • W) s
      ⟨hs0, hs.2.trans_lt (Real.sqrt_lt_sqrt hb.le hmax)⟩
  · intro u _
    have h := (A.path (Z + u • W) b hb hmax).l_integrable
    rw [A.path_eq] at h
    exact h
  · intro u _
    exact (A.gamma_at_zero (Z + u • W)).trans
      ((congrFun (A.path_eq Z b hb hmax) 0).trans (A.gamma_at_zero Z)).symm

@[simp] theorem initialVectorVariation_family (A : LExponentialFamily F T τmax p)
    (Z W : TangentSpace (𝓡 n) p) (b : ℝ) (hb : 0 < b) (hmax : b < τmax) (t u : ℝ) :
    (initialVectorVariation A Z W b hb hmax).family t u = A.gamma (Z + u • W) t := rfl

@[simp] theorem initialVectorVariation_squareFamily (A : LExponentialFamily F T τmax p)
    (Z W : TangentSpace (𝓡 n) p) (b : ℝ) (hb : 0 < b) (hmax : b < τmax) (s u : ℝ) :
    (initialVectorVariation A Z W b hb hmax).squareFamily s u =
      A.squareFamily (Z + u • W) s := rfl

@[simp] theorem initialVectorVariation_action (A : LExponentialFamily F T τmax p)
    (Z W : TangentSpace (𝓡 n) p) (b : ℝ) (hb : 0 < b) (hmax : b < τmax) (u : ℝ) :
    variationLLength (initialVectorVariation A Z W b hb hmax).toLVariation u =
      A.action (Z + u • W) b := rfl

end PoincareConjecture.Proofs.M09
