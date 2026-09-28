import PoincareConjecture.Proofs.M35.Uniqueness.Heat.PointwiseHeat










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

noncomputable section

open Set MeasureTheory
open scoped SchwartzMap ContDiff

namespace PoincareConjecture.M35.Uniqueness.Heat

open EuclideanDerivativeNative DeTurckGeneratorRegularityNative

variable {n m : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin n)
local notation "L2" => Lp ℝ 2 (volume : Measure V)

theorem localized_schwartzField_eq_ae (K : Set V) (χ : 𝓢(V, ℝ))
    (W : PiLp 2 (fun _ : Fin m => dirichletForm K)) (X : Fin m → 𝓢(V, ℝ))
    (hX : ∀ j, (X j).toLp 2 volume = localizedDirichletValue K χ (W j)) :
    ∀ᵐ x ∂volume, schwartzField X x = χ x • dirichletFieldValue K W x := by
  have hcoords : ∀ᵐ x ∂volume, ∀ j : Fin m,
      X j x = χ x * (dirichletInclusion K (W j) : L2) x := by
    apply ae_all_iff.mpr
    intro j
    filter_upwards [(X j).coeFn_toLp 2 volume,
      schwartzMultiplier_coe χ (dirichletInclusion K (W j) : L2)] with x hx hχ
    have he := congrArg (fun u : L2 => u x) (hX j)
    exact hx.symm.trans (he.trans hχ)
  have hfield : ∀ᵐ x ∂volume, dirichletFieldValue K W x =
      WithLp.toLp 2 (fun j => (dirichletInclusion K (W j) : L2) x) := by
    exact scalarFieldsLp_coe
      (finiteHilbertMap ((dirichletValue K).subtypeL.comp (dirichletInclusion K)) W)
  filter_upwards [hcoords, hfield] with x hx hf
  rw [hf, schwartzField_apply]
  apply PiLp.ext
  intro j
  exact hx j

theorem localized_schwartzField_metric_bound (K : Set V) {O : Set V}
    (hO : IsOpen O) (hOK : O ⊆ K) (g : RiemannianMetric n V)
    (χ : 𝓢(V, ℝ)) (hχO : ∀ x ∈ O, χ x = 1)
    (W : PiLp 2 (fun _ : Fin n => dirichletForm K)) (X : Fin n → 𝓢(V, ℝ))
    (hX : ∀ j, (X j).toLp 2 volume = localizedDirichletValue K χ (W j))
    {Q : ℝ} (hbound : ∀ᵐ x ∂volume, x ∈ K →
      g.inner x (dirichletFieldValue K W x) (dirichletFieldValue K W x) ≤ Q) :
    ∀ x ∈ O, g.inner x (schwartzField X x) (schwartzField X x) ≤ Q := by
  let q := fieldNormSq g (schwartzField X)
  have hc : Continuous q := (fieldNormSq_contDiff g (schwartzField X).smooth').continuous
  have hle : ∀ᵐ x ∂volume, x ∈ O → q x ≤ Q := by
    filter_upwards [localized_schwartzField_eq_ae K χ W X hX, hbound] with x hx hb
    intro hxO
    change g.inner x (schwartzField X x) (schwartzField X x) ≤ Q
    rw [hx, hχO x hxO, one_smul]
    exact hb (hOK hxO)
  have he : ∀ᵐ x ∂volume, x ∈ O → min (q x) Q = q x :=
    hle.mono (fun x hx hxO => min_eq_left (hx hxO))
  have heq : EqOn (fun x => min (q x) Q) q O :=
    Measure.eqOn_open_of_ae_eq ((ae_restrict_iff' hO.measurableSet).mpr he) hO
      (hc.min continuous_const).continuousOn hc.continuousOn
  intro x hx
  change q x ≤ Q
  exact (heq hx).symm.trans_le (min_le_right _ _)

theorem localized_value_schwartzField_metric_bound (K : Set V) {O : Set V}
    (hO : IsOpen O) (hOK : O ⊆ K) (g : RiemannianMetric n V)
    (χ : 𝓢(V, ℝ)) (hχO : ∀ x ∈ O, χ x = 1)
    (W : PiLp 2 (fun _ : Fin n => dirichletForm K))
    (U : PiLp 2 (fun _ : Fin n => dirichletValue K))
    (hgraph : finiteHilbertMap (dirichletInclusion K) W = U)
    (X : Fin n → 𝓢(V, ℝ))
    (hX : ∀ j, (X j).toLp 2 volume = localizedDirichletValue K χ (W j))
    {Q : ℝ} (hbound : ∀ᵐ x ∂volume, x ∈ K →
      g.inner x (dirichletValueField K U x) (dirichletValueField K U x) ≤ Q) :
    ∀ x ∈ O, g.inner x (schwartzField X x) (schwartzField X x) ≤ Q := by
  apply localized_schwartzField_metric_bound K hO hOK g χ hχO W X hX
  have he : dirichletFieldValue K W = dirichletValueField K U :=
    (dirichletValueField_form K W).symm.trans (congrArg (dirichletValueField K) hgraph)
  simpa only [he] using hbound

end PoincareConjecture.M35.Uniqueness.Heat
