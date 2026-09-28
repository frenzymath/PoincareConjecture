import PoincareConjecture.Proofs.M35.Uniqueness.Heat.PrincipalFormRecovery
import PoincareConjecture.Proofs.M35.Uniqueness.Heat.RawSlabTimeRegularity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

noncomputable section

open Set MeasureTheory Filter
open scoped SchwartzMap ContDiff Topology

namespace PoincareConjecture.M35.Uniqueness.Heat

open ValueInitial

variable {n : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin n)

theorem exists_raw_compact_vector_heat_smooth_form {J : Set ℝ} (F : RicciFlow n V J)
    {a b : ℝ} (hab : a < b) (hJ : Icc a b ⊆ J)
    {K : Set V} (hK : IsCompact K) (η : 𝓢(V, ℝ)) (hη : HasCompactSupport η)
    (hηK : ∀ x ∈ K, η x = 1)
    {u₀ : PiLp 2 (fun _ : Fin n => dirichletValue K)}
    {v : ℝ → PiLp 2 (fun _ : Fin n => dirichletForm K)}
    {U : ℝ → PiLp 2 (fun _ : Fin n => dirichletValue K)}
    (hsol : PrincipalValueHeat K
      (fun r => rawCutoffPrincipalCoefficient (F.metric r) η hη)
      (fun r => rawLowerFormOperator (F.connection r) hK.isClosed η hη) a (b - a) u₀ v U) :
    ∃ w : ℝ → PiLp 2 (fun _ : Fin n => dirichletForm K),
      (∀ t ∈ Ioo 0 (b - a), ContDiffAt ℝ ∞ w t) ∧
      (∀ᵐ t ∂volume.restrict (Ioo 0 (b - a)), w t = v t) ∧
      (∀ t ∈ Ioo 0 (b - a), finiteHilbertMap (dirichletInclusion K) (w t) = U t) ∧
      (∀ t ∈ Ioo 0 (b - a),
        finiteHilbertMap (dirichletInclusion K) (deriv w t) = deriv U t) ∧
      (∀ t ∈ Ioo 0 (b - a), ∀ z : PiLp 2 (fun _ : Fin n => dirichletForm K),
        inner ℝ (finiteHilbertMap (dirichletInclusion K) z) (deriv U t) =
          inner ℝ (finiteHilbertMap (dirichletInclusion K) z)
            (rawLowerFormOperator (F.connection (a + t)) hK.isClosed η hη (w t)) -
              principalVectorEnergy K (rawCutoffPrincipalCoefficient (F.metric (a + t)) η hη)
                z (w t)) := by
  have hElliptic : ∃ ell : ℝ, 0 < ell ∧ ∀ t ∈ Icc a b, ∀ x ∈ K,
      ∀ ξ : Fin n → ℝ, ell * (∑ i, ξ i ^ 2) ≤
        ∑ i, ∑ j, rawCutoffPrincipalCoefficient (F.metric t) η hη i j x * ξ i * ξ j :=
    exists_raw_slab_cutoff_ellipticity F isCompact_Icc hJ hK η hη hηK
  obtain ⟨ell, hell, hEll⟩ := hElliptic
  let A := fun r => rawCutoffPrincipalCoefficient (F.metric (a + r)) η hη
  let L := fun r => rawLowerFormOperator (F.connection (a + r)) hK.isClosed η hη
  have hshift : MapsTo (fun r : ℝ => a + r) (Icc 0 (b - a)) (Icc a b) := by
    intro r hr
    constructor <;> linarith only [hr.1, hr.2]
  have hAc : ContDiffOn ℝ ∞ (fun r => principalFormOperator K (A r)) (Icc 0 (b - a)) :=
    (contDiffOn_raw_principalFormOperator F hab hJ K η hη).comp
      (contDiffOn_const.add contDiffOn_id) hshift
  have hLc : ContDiffOn ℝ ∞ L (Icc 0 (b - a)) :=
    (contDiffOn_rawLowerFormOperator F hab hJ hK.isClosed η hη).comp
      (contDiffOn_const.add contDiffOn_id) hshift
  have hs : PrincipalValueHeat K A L 0 (b - a) u₀ v U := by
    simpa only [PrincipalValueHeat, A, L, zero_add] using hsol
  have hrec : ∃ w : ℝ → PiLp 2 (fun _ : Fin n => dirichletForm K),
      (∀ t ∈ Ioo 0 (b - a), ContDiffAt ℝ ∞ w t) ∧
      (∀ᵐ t ∂volume.restrict (Ioo 0 (b - a)), w t = v t) ∧
      (∀ t ∈ Ioo 0 (b - a), finiteHilbertMap (dirichletInclusion K) (w t) = U t) ∧
      (∀ t ∈ Ioo 0 (b - a), ∀ z : PiLp 2 (fun _ : Fin n => dirichletForm K),
        inner ℝ (finiteHilbertMap (dirichletInclusion K) z) (deriv U t) =
          inner ℝ (finiteHilbertMap (dirichletInclusion K) z) (L t (w t)) -
            principalVectorEnergy K (A t) z (w t)) :=
    exists_principalValueHeat_smooth_form hK A hell
      (fun r _ => rawCutoffPrincipalCoefficient_symmetric (F.metric (a + r)) η hη)
      (fun r hr => hEll (a + r) (hshift hr)) hAc L hLc hs
  obtain ⟨w, hw, hae, hgraph, heq⟩ := hrec
  refine ⟨w, hw, hae, hgraph, ?_, heq⟩
  intro t ht
  have hdw := (hw t ht).differentiableAt (by simp : (∞ : ℕ∞ω) ≠ 0)
  have hdi := (finiteHilbertMap (dirichletInclusion K)).hasFDerivAt.comp_hasDerivAt t
    hdw.hasDerivAt
  have he : (fun s => finiteHilbertMap (dirichletInclusion K) (w s)) =ᶠ[𝓝 t] U := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
    exact hgraph s hs
  exact hdi.deriv.symm.trans he.deriv_eq

end PoincareConjecture.M35.Uniqueness.Heat
